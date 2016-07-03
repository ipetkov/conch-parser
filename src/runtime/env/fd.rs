use runtime::{Fd, STDERR_FILENO, STDIN_FILENO, STDOUT_FILENO};
use runtime::env::SubEnvironment;
use runtime::io::{dup_stdio, FileDesc, Permissions};
use runtime::ref_counted::RefCounted;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::error::Error;
use std::io::Result;
use std::rc::Rc;
use std::sync::Arc;

/// An interface for setting and getting shell file descriptors.
pub trait FileDescEnvironment {
    /// A file handle (or wrapper) to associate with shell file descriptors.
    type FileHandle;
    /// Get the permissions and a handle associated with an opened file descriptor.
    fn file_desc(&self, fd: Fd) -> Option<(&Self::FileHandle, Permissions)>;
    /// Associate a file descriptor with a given handle and permissions.
    fn set_file_desc(&mut self, fd: Fd, fdes: Self::FileHandle, perms: Permissions);
    /// Treat the specified file descriptor as closed for the current environment.
    fn close_file_desc(&mut self, fd: Fd);
    /// Reports any `Error` as appropriate, e.g. print to stderr.
    fn report_error(&mut self, err: &Error);
}

impl<'a, T: ?Sized + FileDescEnvironment> FileDescEnvironment for &'a mut T {
    type FileHandle = T::FileHandle;

    fn file_desc(&self, fd: Fd) -> Option<(&Self::FileHandle, Permissions)> {
        (**self).file_desc(fd)
    }

    fn set_file_desc(&mut self, fd: Fd, fdes: Self::FileHandle, perms: Permissions) {
        (**self).set_file_desc(fd, fdes, perms)
    }

    fn close_file_desc(&mut self, fd: Fd) {
        (**self).close_file_desc(fd)
    }

    fn report_error(&mut self, err: &Error) {
        (**self).report_error(err);
    }
}

macro_rules! impl_env {
    ($(#[$attr:meta])* pub struct $Env:ident, $Rc:ident) => {
        $(#[$attr])*
        #[derive(Debug, PartialEq, Eq)]
        pub struct $Env<T = $Rc<FileDesc>> {
            fds: $Rc<HashMap<Fd, (T, Permissions)>>,
        }

        impl<T> $Env<T> {
            /// Constructs a new environment with no open file descriptors.
            pub fn new() -> Self {
                $Env {
                    fds: HashMap::new().into(),
                }
            }

            /// Constructs a new environment and initializes it with duplicated
            /// stdio file descriptors or handles of the current process.
            pub fn with_process_fds() -> Result<Self> where T: From<FileDesc> {
                let (stdin, stdout, stderr) = try!(dup_stdio());
                Ok(Self::with_fds(vec!(
                    (STDIN_FILENO,  stdin.into(),  Permissions::Read),
                    (STDOUT_FILENO, stdout.into(), Permissions::Write),
                    (STDERR_FILENO, stderr.into(), Permissions::Write),
                )))
            }

            /// Constructs a new environment with a provided collection of provided
            /// file descriptors in the form `(shell_fd, handle, permissions)`.
            pub fn with_fds<I: IntoIterator<Item = (Fd, T, Permissions)>>(iter: I) -> Self {
                $Env {
                    fds: iter.into_iter()
                        .map(|(fd, fdes, perms)| (fd, (fdes, perms)))
                        .collect::<HashMap<_, _>>()
                        .into(),
                }
            }
        }

        impl<T> Default for $Env<T> {
            fn default() -> Self {
                Self::new()
            }
        }

        impl<T> Clone for $Env<T> {
            fn clone(&self) -> Self {
                $Env {
                    fds: self.fds.clone(),
                }
            }
        }

        impl<T> SubEnvironment for $Env<T> {
            fn sub_env(&self) -> Self {
                self.clone()
            }
        }

        impl<T: Clone + Borrow<FileDesc>> FileDescEnvironment for $Env<T> {
            type FileHandle = T;

            fn file_desc(&self, fd: Fd) -> Option<(&Self::FileHandle, Permissions)> {
                self.fds.get(&fd).map(|&(ref fdes, perms)| (fdes, perms))
            }

            fn set_file_desc(&mut self, fd: Fd, fdes: Self::FileHandle, perms: Permissions) {
                let needs_insert = {
                    let existing = self.fds.get(&fd).map(|&(ref fdes, perms)| (fdes.borrow(), perms));
                    existing != Some((fdes.borrow(), perms))
                };

                if needs_insert {
                    self.fds.make_mut().insert(fd, (fdes, perms));
                }
            }

            fn close_file_desc(&mut self, fd: Fd) {
                if self.fds.contains_key(&fd) {
                    self.fds.make_mut().remove(&fd);
                }
            }

            fn report_error(&mut self, err: &Error) {
                // We *could* duplicate the handle here and ensure that we are the only
                // owners of that *copy*, but it won't make much difference. On Unix
                // sytems file descriptor duplication is effectively just an alias, and
                // we really *do* want to write into whatever stderr is. Plus our error
                // description should safely fall well within the system's size for atomic
                // writes so we (hopefully) shouldn't observe any interleaving of data.
                //
                // Tl;dr: duplicating the handle won't offer us any extra safety, so we
                // can avoid the overhead.
                self.file_desc(STDERR_FILENO).map(|(fd, _)| unsafe {
                    let mut writer = fd.borrow().unsafe_write();
                    let _ = writeln!(&mut writer, "{}", err);
                });
            }
        }
    };
}

impl_env!(
    /// An `Environment` module for setting and getting shell file descriptors.
    ///
    /// Uses `Rc` internally. For a possible `Send` and `Sync` implementation,
    /// see `AtomicFileDescEnv`.
    pub struct FileDescEnv,
    Rc
);

impl_env!(
    /// An `Environment` module for setting and getting shell file descriptors.
    ///
    /// Uses `Arc` internally. If `Send` and `Sync` is not required of the implementation,
    /// see `FileDescEnv` as a cheaper alternative.
    pub struct AtomicFileDescEnv,
    Arc
);

#[cfg(test)]
mod tests {
    use runtime::{STDIN_FILENO, STDOUT_FILENO, STDERR_FILENO};
    use runtime::env::SubEnvironment;
    use runtime::io::{Permissions, Pipe};
    use runtime::ref_counted::RefCounted;
    use runtime::tests::dev_null;
    use std::thread;
    use std::rc::Rc;
    use super::*;

    #[test]
    fn test_set_get_and_close_file_desc() {
        let fd = STDIN_FILENO;
        let perms = Permissions::ReadWrite;
        let file_desc = Rc::new(dev_null());

        let mut env = FileDescEnv::new();
        assert_eq!(env.file_desc(fd), None);

        env.set_file_desc(fd, file_desc.clone(), perms);
        assert_eq!(env.file_desc(fd), Some((&file_desc, perms)));

        env.close_file_desc(fd);
        assert_eq!(env.file_desc(fd), None);

        // Closing a file should drop any copies the env had
        Rc::try_unwrap(file_desc).expect("unexpected reference to file_desc remains");
    }

    #[test]
    fn test_sub_env_no_needless_clone() {
        let fd = STDIN_FILENO;
        let fd_not_set = 42;
        let perms = Permissions::ReadWrite;
        let file_desc = Rc::new(dev_null());

        let env = FileDescEnv::with_fds(vec!((fd, file_desc.clone(), perms)));
        assert_eq!(env.file_desc(fd), Some((&file_desc, perms)));

        let mut env = env.sub_env();
        env.set_file_desc(fd, file_desc.clone(), perms);
        if let Some(_) = env.fds.get_mut() {
            panic!("needles clone!");
        }

        assert_eq!(env.file_desc(fd_not_set), None);
        env.close_file_desc(fd_not_set);
        if let Some(_) = env.fds.get_mut() {
            panic!("needles clone!");
        }
    }

    #[test]
    fn test_report_error() {
        use std::error::Error;
        use std::fmt;
        use std::io::{Read, Write};

        const MSG: &'static str = "some error message";

        #[derive(Debug)]
        struct MockErr;

        impl fmt::Display for MockErr {
            fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
                write!(fmt, "{}", self.description())
            }
        }

        impl Error for MockErr {
            fn description(&self) -> &str {
                MSG
            }
        }

        let Pipe { mut reader, writer } = Pipe::new().unwrap();

        let guard = thread::spawn(move || {
            let writer = Rc::new(writer);
            let mut env = FileDescEnv::with_fds(vec!(
                (STDERR_FILENO, writer.clone(), Permissions::Write))
            );

            env.report_error(&MockErr);
            drop(env);

            let mut writer = Rc::try_unwrap(writer).unwrap();
            writer.flush().unwrap();
            drop(writer);
        });

        let mut msg = String::new();
        reader.read_to_string(&mut msg).unwrap();
        guard.join().unwrap();
        assert_eq!(msg, format!("{}\n", MSG));
    }

    #[test]
    fn test_set_and_closefile_desc_in_child_env_should_not_affect_parent() {
        let fd = STDIN_FILENO;
        let fd_open_in_child = STDOUT_FILENO;
        let fd_close_in_child = STDERR_FILENO;

        let perms = Permissions::Write;
        let fdes = Rc::new(dev_null());
        let fdes_close_in_child = Rc::new(dev_null());

        let parent = FileDescEnv::with_fds(vec!(
            (fd, fdes.clone(), perms),
            (fd_close_in_child, fdes_close_in_child.clone(), perms),
        ));

        assert_eq!(parent.file_desc(fd_open_in_child), None);

        {
            let child_perms = Permissions::Read;
            let fdes_open_in_child = Rc::new(dev_null());
            let mut child = parent.sub_env();
            child.set_file_desc(fd, fdes_open_in_child.clone(), child_perms);
            child.set_file_desc(fd_open_in_child, fdes_open_in_child.clone(), child_perms);
            child.close_file_desc(fd_close_in_child);

            assert_eq!(child.file_desc(fd), Some((&fdes_open_in_child, child_perms)));
            assert_eq!(child.file_desc(fd_open_in_child), Some((&fdes_open_in_child, child_perms)));
            assert_eq!(child.file_desc(fd_close_in_child), None);
        }

        assert_eq!(parent.file_desc(fd), Some((&fdes, perms)));
        assert_eq!(parent.file_desc(fd_close_in_child), Some((&fdes_close_in_child, perms)));
        assert_eq!(parent.file_desc(fd_open_in_child), None);
    }
}
