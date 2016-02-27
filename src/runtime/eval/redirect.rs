//! A module which defines evaluating any kind of redirection.

use std::fs::OpenOptions;
use std::rc::Rc;
use syntax::ast::Redirect;
use runtime::{Fd, Environment, RedirectionError, Result, RuntimeError};
use runtime::{EXIT_ERROR, STDIN_FILENO, STDOUT_FILENO};
use runtime::eval::{Fields, TildeExpansion, WordEval, WordEvalConfig};
use runtime::io::{FileDesc, Permissions};

impl<W: WordEval> Redirect<W> {
    /// Evaluates a redirection path and opens the appropriate redirect.
    ///
    /// Newly opened/closed/duplicated file descriptors are NOT updated
    /// in the environment, and thus it is up to the caller to update the
    /// environment as appropriate.
    ///
    /// On success the affected file descriptor (from the script's perspective)
    /// is returned, along with an Optional file handle and the respective
    /// permissions. A `Some` value indicates a newly opened or duplicated descriptor
    /// while a `None` indicates that that descriptor should be closed.
    /// The caller is responsible for actually applying these changes to the environment.
    // FIXME: on unix set file permission bits based on umask
    pub fn eval(&self, env: &mut Environment) -> Result<(Fd, Option<(Rc<FileDesc>, Permissions)>)> {
        let open_path_with_options = |path, env, fd, options: OpenOptions, permissions|
            -> Result<(Fd, Option<(Rc<FileDesc>, Permissions)>)>
        {
            let path = try!(eval_path(path, env));
            match options.open(&**path) {
                Ok(file) => Ok((fd, Some((Rc::new(file.into()), permissions)))),
                Err(io) => Err(RuntimeError::Io(io, rc_to_owned(path))),
            }
        };

        let open_path = |path, env, fd, permissions: Permissions|
            -> Result<(Fd, Option<(Rc<FileDesc>, Permissions)>)>
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
                let perms = Permissions::Write;
                let mut options: OpenOptions = perms.into();
                options.append(true);
                try!(open_path_with_options(path, env, fd.unwrap_or(STDOUT_FILENO), options, perms))
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
fn eval_path(path: &WordEval, env: &mut Environment) -> Result<Rc<String>> {
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
            env.set_last_status(EXIT_ERROR);
            let v = v.into_iter().map(rc_to_owned).collect();
            return Err(RedirectionError::Ambiguous(v).into())
        },
        Fields::Zero => {
            env.set_last_status(EXIT_ERROR);
            return Err(RedirectionError::Ambiguous(Vec::new()).into())
        },
    }
}

/// Attempts to duplicate an existing descriptor into a different one.
/// An error will result if the source is not a valid descriptor, or if there
/// is a permission mismatch between the duplication type and source descriptor.
///
/// On success the duplicated descritor is returned. It is up to the caller to
/// actually store the duplicate in the environment.
fn dup_fd(dst_fd: Fd, src_fd: &WordEval, readable: bool, env: &mut Environment)
    -> Result<(Fd, Option<(Rc<FileDesc>, Permissions)>)>
{
    let src_fd = try!(eval_path(src_fd, env));

    if *src_fd == "-" {
        return Ok((dst_fd, None));
    }

    let src_fdes = match Fd::from_str_radix(&src_fd, 10) {
        Ok(fd) => match env.file_desc(fd) {
            Some((fdes, perms)) => {
                if (readable && perms.readable()) || (!readable && perms.writable()) {
                    Ok(fdes.clone())
                } else {
                    Err(RedirectionError::BadFdPerms(fd, perms).into())
                }
            },

            None => Err(RedirectionError::BadFdSrc(rc_to_owned(src_fd)).into()),
        },

        Err(_) => Err(RedirectionError::BadFdSrc(rc_to_owned(src_fd)).into()),
    };

    let src_fdes = match src_fdes {
        Ok(fd) => fd,
        Err(e) => {
            env.set_last_status(EXIT_ERROR);
            return Err(e);
        },
    };

    let perms = if readable { Permissions::Read } else { Permissions::Write };
    Ok((dst_fd, Some((src_fdes, perms))))
}

/// Attempts to unwrap an Rc<T>, cloning the inner value if the unwrap fails.
fn rc_to_owned<T: Clone>(rc: Rc<T>) -> T {
    Rc::try_unwrap(rc).unwrap_or_else(|rc| (*rc).clone())
}
