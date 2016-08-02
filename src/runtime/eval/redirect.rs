//! A module which defines evaluating any kind of redirection.

use std::fs::OpenOptions;
use syntax::ast::Redirect;
use runtime::{Fd, RedirectionError, Result, RuntimeError};
use runtime::{STDIN_FILENO, STDOUT_FILENO};
use runtime::env::{FileDescEnvironment, IsInteractiveEnvironment, StringWrapper, SubEnvironment};
use runtime::eval::{Fields, TildeExpansion, WordEval, WordEvalConfig};
use runtime::io::{FileDesc, Permissions};

/// Indicates what changes should be made to the environment as a result
/// of a successful `Redirect` evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RedirectAction<T> {
    /// Indicates that a descriptor should be closed.
    Close(Fd),
    /// Indicates that a descriptor should be opened with
    /// a given file handle and permissions.
    Open(Fd, T, Permissions)
}

impl<T> RedirectAction<T> {
    /// Applies changes to a given environment.
    pub fn apply<E: ?Sized + FileDescEnvironment<FileHandle = T>>(self, env: &mut E) {
        match self {
            RedirectAction::Close(fd) => env.close_file_desc(fd),
            RedirectAction::Open(fd, file_desc, perms) => env.set_file_desc(fd, file_desc, perms),
        }
    }
}

impl<W> Redirect<W> {
    /// Evaluates a redirection path and opens the appropriate redirect.
    ///
    /// Newly opened/closed/duplicated file descriptors are NOT updated
    /// in the environment, and thus it is up to the caller to update the
    /// environment as appropriate.
    // FIXME: on unix set file permission bits based on umask
    pub fn eval<T, E>(&self, env: &mut E) -> Result<RedirectAction<E::FileHandle>>
        where T: StringWrapper,
              E: FileDescEnvironment + IsInteractiveEnvironment + SubEnvironment,
              E::FileHandle: Clone + From<FileDesc>,
              W: WordEval<T, E>,
    {
        let open_path_with_options = |path, env, fd, options: OpenOptions, permissions|
            -> Result<RedirectAction<E::FileHandle>>
        {
            let path: T = try!(eval_path(path, env));
            options.open(path.as_str())
                .map(FileDesc::from)
                .map(|fdesc| RedirectAction::Open(fd, fdesc.into(), permissions))
                .map_err(|io| RuntimeError::Io(io, Some(path.into_owned())))
        };

        let open_path = |path, env, fd, permissions: Permissions|
            -> Result<RedirectAction<E::FileHandle>>
        {
            open_path_with_options(path, env, fd, permissions.into(), permissions)
        };

        let ret = match *self {
            Redirect::Read(fd, ref path) =>
                try!(open_path(path, env, fd.unwrap_or(STDIN_FILENO), Permissions::Read)),

            Redirect::ReadWrite(fd, ref path) =>
                try!(open_path(path, env, fd.unwrap_or(STDIN_FILENO), Permissions::ReadWrite)),

            Redirect::Write(fd, ref path) |
            Redirect::Clobber(fd, ref path) =>
                // FIXME: implement checks for noclobber option
                try!(open_path(path, env, fd.unwrap_or(STDOUT_FILENO), Permissions::Write)),

            Redirect::Append(fd, ref path) => {
                let mut options = OpenOptions::new();
                options.append(true);
                let fd = fd.unwrap_or(STDOUT_FILENO);
                try!(open_path_with_options(path, env, fd, options, Permissions::Write))
            },

            Redirect::DupRead(fd, ref src)  => try!(dup_fd(fd.unwrap_or(STDIN_FILENO), src, true, env)),
            Redirect::DupWrite(fd, ref src) => try!(dup_fd(fd.unwrap_or(STDOUT_FILENO), src, false, env)),

            Redirect::Heredoc(fd, ref body) => unimplemented!(), // FIXME: implement
        };

        Ok(ret)
    }
}

/// Evaluates a path in a given environment. Tilde expansion will be done,
/// and words will be split if running in interactive mode. If the evaluation
/// results in more than one path, an error will be returned.
fn eval_path<T, E, W: ?Sized>(path: &W, env: &mut E) -> Result<T>
    where T: StringWrapper,
          E: IsInteractiveEnvironment + SubEnvironment,
          W: WordEval<T, E>,
{
    let cfg = WordEvalConfig {
        tilde_expansion: TildeExpansion::First,
        split_fields_further: env.is_interactive(),
    };

    match try!(path.eval_with_config(env, cfg)) {
        Fields::Single(path) => Ok(path),
        Fields::At(mut v)   |
        Fields::Star(mut v) |
        Fields::Split(mut v) => if v.len() == 1 {
            Ok(v.pop().unwrap())
        } else {
            let v = v.into_iter().map(StringWrapper::into_owned).collect();
            Err(RedirectionError::Ambiguous(v).into())
        },
        Fields::Zero => Err(RedirectionError::Ambiguous(Vec::new()).into()),
    }
}

/// Attempts to duplicate an existing descriptor into a different one.
/// An error will result if the source is not a valid descriptor, or if there
/// is a permission mismatch between the duplication type and source descriptor.
///
/// On success the duplicated descritor is returned. It is up to the caller to
/// actually store the duplicate in the environment.
fn dup_fd<T, E, W: ?Sized>(dst_fd: Fd, src_fd: &W, readable: bool, env: &mut E)
    -> Result<RedirectAction<E::FileHandle>>
    where T: StringWrapper,
          E: FileDescEnvironment + IsInteractiveEnvironment + SubEnvironment,
          E::FileHandle: Clone,
          W: WordEval<T, E>,
{
    let src_fd = try!(eval_path(src_fd, env));
    let src_fd = src_fd.as_str();

    if src_fd == "-" {
        return Ok(RedirectAction::Close(dst_fd));
    }

    let fd_handle_perms = Fd::from_str_radix(src_fd, 10)
        .ok()
        .and_then(|fd| env.file_desc(fd).map(|(fdes, perms)| (fd, fdes, perms)));

    let src_fdes = match fd_handle_perms {
        Some((fd, fdes, perms)) => {
            if (readable && perms.readable()) || (!readable && perms.writable()) {
                fdes.clone()
            } else {
                return Err(RedirectionError::BadFdPerms(fd, perms).into());
            }
        },

        None => return Err(RedirectionError::BadFdSrc(src_fd.to_owned()).into()),
    };

    let perms = if readable { Permissions::Read } else { Permissions::Write };
    Ok(RedirectAction::Open(dst_fd, src_fdes, perms))
}

#[cfg(test)]
mod tests {
    extern crate tempdir;

    use runtime::{Fd, STDIN_FILENO, STDOUT_FILENO};
    use runtime::env::{DefaultEnvConfig, Env, EnvConfig, FileDescEnv, FileDescEnvironment,
                       IsInteractiveEnvironment};
    use runtime::io::{FileDesc, Permissions};
    use runtime::tests::{MockWord, word};
    use self::tempdir::TempDir;
    use std::fs::File;
    use std::io::{Read as IoRead, Write as IoWrite};
    use std::path::PathBuf;
    use std::rc::Rc;
    use super::RedirectAction::*;
    use syntax::ast::Redirect::*;

    type Redirect = ::syntax::ast::Redirect<MockWord>;

    fn test_eval_close(fd: Fd, redirect: Redirect) {
        let mut env = Env::with_config(EnvConfig {
            file_desc_env: FileDescEnv::with_process_fds().unwrap(),
            .. DefaultEnvConfig::<String>::default()
        });

        assert!(env.file_desc(fd).is_some());
        let action = redirect.eval(&mut env).unwrap();
        assert_eq!(action, Close(fd));
        action.apply(&mut env);
        assert_eq!(env.file_desc(fd), None);
    }

    fn test_open_redirect<F1, F2>(cases: Vec<(Fd, Redirect)>,
                                  correct_permissions: Permissions,
                                  mut before: F1,
                                  mut after: F2)
        where F1: FnMut(),
              F2: FnMut(FileDesc)
    {
        for (fd, redirect) in cases {
            before();

            let mut env = Env::with_config(EnvConfig {
                file_desc_env: FileDescEnv::with_process_fds().unwrap(),
                .. DefaultEnvConfig::<String>::default()
            });

            let action = redirect.eval(&mut env).unwrap();
            if let Open(ref result_fd, _, permissions) = action {
                assert_eq!(permissions, correct_permissions);
                assert_eq!(result_fd, &fd);
            } else {
                panic!("Unexpected action: {:#?}", action);
            }

            action.apply(&mut env);

            let rc = {
                let (rc, perms) = env.file_desc(fd).unwrap();
                assert_eq!(perms, correct_permissions);
                rc.clone()
            };
            env.close_file_desc(fd);

            let file_desc = Rc::try_unwrap(rc).unwrap();
            after(file_desc);
        }
    }

    #[test]
    fn test_eval_read() {
        let msg = "hello world";
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push("out");

        let cases: Vec<(Fd, Redirect)> = vec!(
            (STDIN_FILENO, Read(None, word(&file_path.display()))),
            (42,           Read(Some(42), word(&file_path.display()))),
        );

        test_open_redirect(
            cases,
            Permissions::Read,
            || {
                let mut file = File::create(&file_path).unwrap();
                file.write_all(msg.as_bytes()).unwrap();
                file.flush().unwrap();
            },
            |mut file_desc| {
                let mut read = String::new();
                file_desc.read_to_string(&mut read).unwrap();
                assert_eq!(read, msg);
            }
        );
    }

    #[test]
    fn test_eval_write_and_clobber() {
        let msg = "hello world";
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push("out");

        let cases: Vec<(Fd, Redirect)> = vec!(
            (STDOUT_FILENO, Write(None, word(&file_path.display()))),
            (42,            Write(Some(42), word(&file_path.display()))),
            // FIXME: split out clobber tests and check clobber semantics
            (STDOUT_FILENO, Clobber(None, word(&file_path.display()))),
            (42,            Clobber(Some(42), word(&file_path.display()))),
        );

        test_open_redirect(
            cases,
            Permissions::Write,
            || {
                let mut file = File::create(&file_path).unwrap();
                file.write_all(b"should be overwritten").unwrap();
                file.flush().unwrap();
            },
            |mut file_desc| {
                file_desc.write_all(msg.as_bytes()).unwrap();
                file_desc.flush().unwrap();
                drop(file_desc);

                let mut file = File::open(&file_path).unwrap();
                let mut read = String::new();
                file.read_to_string(&mut read).unwrap();
                assert_eq!(read, msg);
            }
        );
    }

    #[test]
    fn test_eval_read_write() {
        let original = "original message";
        let msg = "hello world";
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push("out");

        let cases: Vec<(Fd, Redirect)> = vec!(
            (STDIN_FILENO, ReadWrite(None, word(&file_path.display()))),
            (42,           ReadWrite(Some(42), word(&file_path.display()))),
        );

        test_open_redirect(
            cases,
            Permissions::ReadWrite,
            || {
                let mut file = File::create(&file_path).unwrap();
                file.write_all(original.as_bytes()).unwrap();
                file.flush().unwrap();
            },
            |mut file_desc| {
                let mut read = String::new();
                file_desc.read_to_string(&mut read).unwrap();
                assert_eq!(read, original);

                file_desc.write_all(msg.as_bytes()).unwrap();
                file_desc.flush().unwrap();
                drop(file_desc);

                let mut file = File::open(&file_path).unwrap();
                read.clear();
                file.read_to_string(&mut read).unwrap();
                assert_eq!(read, format!("{}{}", original, msg));
            }
        );
    }

    #[test]
    fn test_eval_append() {
        let msg1 = "hello world";
        let msg2 = "appended";
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push("out");

        let cases: Vec<(Fd, Redirect)> = vec!(
            (STDOUT_FILENO, Append(None, word(&file_path.display()))),
            (42,            Append(Some(42), word(&file_path.display()))),
        );

        test_open_redirect(
            cases,
            Permissions::Write,
            || {
                let mut file = File::create(&file_path).unwrap();
                file.write_all(msg1.as_bytes()).unwrap();
                file.flush().unwrap();
            },
            |mut file_desc| {
                file_desc.write_all(msg2.as_bytes()).unwrap();
                file_desc.flush().unwrap();
                drop(file_desc);

                let mut file = File::open(&file_path).unwrap();
                let mut read = String::new();
                file.read_to_string(&mut read).unwrap();
                assert_eq!(read, format!("{}{}", msg1, msg2));
            }
        );
    }

    #[test]
    fn test_eval_dup_read_close_with_fd() {
        let fd = STDOUT_FILENO;
        test_eval_close(fd, DupRead(Some(fd), word("-")));
    }

    #[test]
    fn test_eval_dup_read_close_without_fd() {
        let fd = STDIN_FILENO;
        test_eval_close(fd, DupRead(None, word("-")));
    }

    #[test]
    fn test_eval_dup_write_close_with_fd() {
        let fd = STDIN_FILENO;
        test_eval_close(fd, DupWrite(Some(fd), word("-")));
    }

    #[test]
    fn test_eval_dup_write_close_without_fd() {
        let fd = STDOUT_FILENO;
        test_eval_close(fd, DupWrite(None, word("-")));
    }

    #[test]
    fn test_eval_dup_not_numeric() {
        use runtime::RedirectionError::BadFdSrc;
        use runtime::RuntimeError::Redirection;

        let mut env = Env::with_config(EnvConfig {
            file_desc_env: FileDescEnv::with_process_fds().unwrap(),
            .. DefaultEnvConfig::<String>::default()
        });
        let path = "a1e2".to_owned();

        let redirect: Redirect = DupRead(None, word(&path));
        assert_eq!(redirect.eval(&mut env), Err(Redirection(BadFdSrc(path.clone()))));
        let redirect: Redirect = DupWrite(None, word(&path));
        assert_eq!(redirect.eval(&mut env), Err(Redirection(BadFdSrc(path.clone()))));
    }

    #[test]
    fn test_eval_dup_src_not_open() {
        use runtime::RedirectionError::BadFdSrc;
        use runtime::RuntimeError::Redirection;

        let mut env = Env::with_config(EnvConfig {
            file_desc_env: FileDescEnv::with_process_fds().unwrap(),
            .. DefaultEnvConfig::<String>::default()
        });
        let path = "42".to_owned();

        let redirect: Redirect = DupRead(None, word(&path));
        assert_eq!(redirect.eval(&mut env), Err(Redirection(BadFdSrc(path.clone()))));
        let redirect: Redirect = DupWrite(None, word(&path));
        assert_eq!(redirect.eval(&mut env), Err(Redirection(BadFdSrc(path.clone()))));
    }

    #[test]
    fn test_eval_dup_bad_perms() {
        use runtime::RedirectionError::BadFdPerms;
        use runtime::RuntimeError::Redirection;

        let mut env = Env::with_config(EnvConfig {
            file_desc_env: FileDescEnv::with_process_fds().unwrap(),
            .. DefaultEnvConfig::<String>::default()
        });

        let fd = STDOUT_FILENO;
        let redirect: Redirect = DupRead(None, word(&fd.to_string()));
        assert_eq!(redirect.eval(&mut env), Err(Redirection(BadFdPerms(fd, Permissions::Write))));

        let fd = STDIN_FILENO;
        let redirect: Redirect = DupWrite(None, word(&fd.to_string()));
        assert_eq!(redirect.eval(&mut env), Err(Redirection(BadFdPerms(fd, Permissions::Read))));
    }

    #[test]
    fn test_eval_dup() {
        let mut env = Env::with_config(EnvConfig {
            file_desc_env: FileDescEnv::with_process_fds().unwrap(),
            .. DefaultEnvConfig::<String>::default()
        });

        let cases: Vec<(Fd, Fd, Redirect)> = vec!(
            (STDIN_FILENO, 5, DupRead(Some(5), word(&STDIN_FILENO.to_string()))),
            (STDOUT_FILENO, 5, DupWrite(Some(5), word(&STDOUT_FILENO.to_string()))),
        );

        for (fd_to_copy, dst, redirect) in cases {
            let action = redirect.eval(&mut env);
            if let Open(fd, fdesc, perms) = redirect.eval(&mut env).unwrap() {
                assert_eq!(fd, dst);
                assert_eq!((&fdesc, perms), env.file_desc(fd_to_copy).unwrap());
            } else {
                panic!("Unexpected action: {:#?}", action);
            }
        }
    }

    #[test]
    fn test_eval_ambiguous_path() {
        use runtime::Result;
        use runtime::eval::{Fields, WordEval, WordEvalConfig};
        use runtime::eval::Fields::*;
        use runtime::tests::DEV_NULL;
        use runtime::RedirectionError::Ambiguous;
        use runtime::RuntimeError::Redirection;

        type Redirect = ::syntax::ast::Redirect<MockWord>;

        struct MockWord(Fields<String>);
        impl<E: ?Sized> WordEval<String, E> for MockWord {
            fn eval_with_config(&self, _: &mut E, _: WordEvalConfig) -> Result<Fields<String>> {
                Ok(self.0.clone())
            }
        }

        let dev_null = DEV_NULL.to_owned();

        let mut env = Env::with_config(EnvConfig {
            file_desc_env: FileDescEnv::with_process_fds().unwrap(),
            .. DefaultEnvConfig::<String>::default()
        });

        // If there is a single field it is not considered an error
        let redirect: Redirect = Read(None, MockWord(Single(dev_null.clone())));
        redirect.eval(&mut env).unwrap();
        let redirect: Redirect = Read(None, MockWord(Star(vec!(dev_null.clone()))));
        redirect.eval(&mut env).unwrap();
        let redirect: Redirect = Read(None, MockWord(At(vec!(dev_null.clone()))));
        redirect.eval(&mut env).unwrap();
        let redirect: Redirect = Read(None, MockWord(Split(vec!(dev_null.clone()))));
        redirect.eval(&mut env).unwrap();

        // Multiple fields, however, are an error
        let vec = vec!(dev_null.clone(), dev_null.clone());
        let redirect: Redirect = Read(None, MockWord(Star(vec.clone())));
        assert_eq!(redirect.eval(&mut env), Err(Redirection(Ambiguous(vec.clone()))));
        let redirect: Redirect = Read(None, MockWord(At(vec.clone())));
        assert_eq!(redirect.eval(&mut env), Err(Redirection(Ambiguous(vec.clone()))));
        let redirect: Redirect = Read(None, MockWord(Split(vec.clone())));
        assert_eq!(redirect.eval(&mut env), Err(Redirection(Ambiguous(vec.clone()))));
        let redirect: Redirect = Read(None, MockWord(Zero));
        assert_eq!(redirect.eval(&mut env), Err(Redirection(Ambiguous(vec!()))));
    }

    #[test]
    fn test_eval_redirect_word_splitting_done_in_interactive_mode() {
        use runtime::Result;
        use runtime::eval::{Fields, WordEval, WordEvalConfig};
        use runtime::tests::DEV_NULL;

        type Redirect = ::syntax::ast::Redirect<MockWord>;

        #[derive(Copy, Clone)]
        struct MockWord(Option<u16>);
        impl<E: ?Sized + IsInteractiveEnvironment> WordEval<String, E> for MockWord {
            fn eval_with_config(&self, env: &mut E, cfg: WordEvalConfig) -> Result<Fields<String>> {
                assert_eq!(env.is_interactive(), cfg.split_fields_further);
                let s = match self.0 {
                    Some(fd) => fd.to_string(),
                    None => DEV_NULL.to_owned(),
                };

                Ok(Fields::Single(s))
            }
        }

        let dev_null = MockWord(None);
        let cases: Vec<Redirect> = vec!(
            Read(None, dev_null),
            Write(None, dev_null),
            ReadWrite(None, dev_null),
            Append(None, dev_null),
            Clobber(None, dev_null),
            //Heredoc(None, W), // FIXME: implement
            DupRead(None, MockWord(Some(STDIN_FILENO))),
            DupWrite(None, MockWord(Some(STDOUT_FILENO))),
        );

        for &interactive in &[true, false] {
            let mut env = Env::with_config(EnvConfig {
                interactive: interactive,
                file_desc_env: FileDescEnv::with_process_fds().unwrap(),
                .. DefaultEnvConfig::<String>::default()
            });

            for redirect in cases.clone() {
                redirect.eval(&mut env).unwrap();
            }
        }
    }
}
