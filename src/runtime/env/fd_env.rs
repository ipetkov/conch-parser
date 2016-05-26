use runtime::{Fd, STDERR_FILENO, STDIN_FILENO, STDOUT_FILENO};
use runtime::env::{SubEnvironment, shallow_copy};
use runtime::io::{dup_stdio, FileDesc, Permissions};

use std::borrow::{Borrow, Cow};
use std::collections::HashMap;
use std::error::Error;
use std::io::Result;
use std::rc::Rc;

/// An interface for setting and getting shell file descriptors.
pub trait FileDescEnvironment<T> {
    /// Get the permissions and a handle associated with an opened file descriptor.
    fn file_desc(&self, fd: Fd) -> Option<(&T, Permissions)>;
    /// Associate a file descriptor with a given handle and permissions.
    fn set_file_desc(&mut self, fd: Fd, fdes: T, perms: Permissions);
    /// Treat the specified file descriptor as closed for the current environment.
    fn close_file_desc(&mut self, fd: Fd);
    /// Reports any `Error` as appropriate, e.g. print to stderr.
    fn report_error(&self, err: &Error);
}

impl<'a, T, E: ?Sized> FileDescEnvironment<T> for &'a mut E
    where E: FileDescEnvironment<T>
{
    fn file_desc(&self, fd: Fd) -> Option<(&T, Permissions)> {
        (**self).file_desc(fd)
    }

    fn set_file_desc(&mut self, fd: Fd, fdes: T, perms: Permissions) {
        (**self).set_file_desc(fd, fdes, perms)
    }

    fn close_file_desc(&mut self, fd: Fd) {
        (**self).close_file_desc(fd)
    }

    fn report_error(&self, err: &Error) {
        (**self).report_error(err);
    }
}

/// An `Environment` module for setting and getting shell file descriptors.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FileDescEnv<'a, T = Rc<FileDesc>> where T: 'a + Clone + Borrow<FileDesc> {
    /// A mapping of file descritpors to their handles and permissions.
    fds: Cow<'a, HashMap<Fd, (T, Permissions)>>,
}

impl<'a, T: Clone + Borrow<FileDesc>> FileDescEnv<'a, T> {
    /// Constructs a new `FileDescEnv` with no open file descriptors.
    pub fn new() -> Self {
        FileDescEnv {
            fds: Cow::Owned(HashMap::new()),
        }
    }

    /// Constructs a new `FileDescEnv` and initializes it with duplicated
    /// stdio file descriptors or handles of the current process.
    pub fn with_process_fds() -> Result<Self> where T: From<FileDesc> {
        let (stdin, stdout, stderr) = try!(dup_stdio());
        Ok(Self::with_fds(vec!(
            (STDIN_FILENO,  stdin.into(),  Permissions::Read),
            (STDOUT_FILENO, stdout.into(), Permissions::Write),
            (STDERR_FILENO, stderr.into(), Permissions::Write),
        )))
    }

    /// Constructs a new `FileDescEnv` with a provided collection of provided
    /// file descriptors in the form `(shell_fd, handle, permissions)`.
    pub fn with_fds<I: IntoIterator<Item = (Fd, T, Permissions)>>(iter: I) -> Self {
        FileDescEnv {
            fds: Cow::Owned(iter.into_iter()
                             .map(|(fd, fdes, perms)| (fd, (fdes, perms)))
                             .collect()),
        }
    }
}

impl<'a, T: Clone + Borrow<FileDesc>> Default for FileDescEnv<'a, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: Clone + Borrow<FileDesc>> SubEnvironment<'a> for FileDescEnv<'a, T> {
    fn sub_env(&'a self) -> Self {
        FileDescEnv {
            fds: shallow_copy(&self.fds),
        }
    }
}

impl<'a, T: Clone + Borrow<FileDesc>> FileDescEnvironment<T> for FileDescEnv<'a, T> {
    fn file_desc(&self, fd: Fd) -> Option<(&T, Permissions)> {
        self.fds.get(&fd).map(|&(ref fdes, perms)| (fdes, perms))
    }

    fn set_file_desc(&mut self, fd: Fd, fdes: T, perms: Permissions) {
        let needs_insert = {
            let existing = self.fds.get(&fd).map(|&(ref fdes, perms)| (fdes.borrow(), perms));
            existing != Some((fdes.borrow(), perms))
        };

        if needs_insert {
            self.fds.to_mut().insert(fd, (fdes, perms));
        }
    }

    fn close_file_desc(&mut self, fd: Fd) {
        if self.fds.contains_key(&fd) {
            self.fds.to_mut().remove(&fd);
        }
    }

    fn report_error(&self, err: &Error) {
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

#[cfg(test)]
mod tests {
    use runtime::{STDERR_FILENO, STDIN_FILENO};
    use runtime::env::SubEnvironment;
    use runtime::io::{Permissions, Pipe};
    use runtime::tests::dev_null;
    use std::borrow::Cow;
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
        if let Cow::Owned(_) = env.fds {
            panic!("needles clone!");
        }

        assert_eq!(env.file_desc(fd_not_set), None);
        env.close_file_desc(fd_not_set);
        if let Cow::Owned(_) = env.fds {
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
            let env = FileDescEnv::with_fds(vec!(
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
}
