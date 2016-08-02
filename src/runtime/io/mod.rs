//! Defines interfaces and methods for doing OS agnostic file IO operations.

mod file_desc_wrapper;
#[cfg(unix)]
#[path = "unix.rs"] mod os;
#[cfg(windows)]
#[path = "windows.rs"] mod os;

use std::cell::UnsafeCell;
use std::fmt;
use std::fs;
use std::io::{Read, Result, Seek, SeekFrom, Write};
use std::path;
use std::process::Stdio;

pub use self::file_desc_wrapper::*;
pub use self::os::{getpid, is_child_running, is_child_process_running};

/// An indicator of the read/write permissions of an OS file primitive.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Permissions {
    /// A file was opened for reading only.
    Read,
    /// A file was opened for writing only.
    Write,
    /// A file was opened for both reading and writing.
    ReadWrite,
}

impl Into<fs::OpenOptions> for Permissions {
    fn into(self) -> fs::OpenOptions {
        let mut options = fs::OpenOptions::new();
        match self {
            Permissions::Read => options.read(true),
            Permissions::Write => options.write(true).create(true).truncate(true),
            Permissions::ReadWrite => options.read(true).write(true).create(true),
        };
        options
    }
}

impl Permissions {
    /// Checks if read permissions are granted.
    pub fn readable(&self) -> bool {
        match *self {
            Permissions::Read |
            Permissions::ReadWrite => true,
            Permissions::Write => false,
        }
    }

    /// Checks if write permissions are granted.
    pub fn writable(&self) -> bool {
        match *self {
            Permissions::Read => false,
            Permissions::Write |
            Permissions::ReadWrite => true,
        }
    }

    /// Opens permissions as a file handle.
    pub fn open<P: AsRef<path::Path>>(self, path: P) -> Result<fs::File> {
        let options: fs::OpenOptions = self.into();
        options.open(path)
    }
}

impl fmt::Display for Permissions {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{:?}", self)
    }
}

/// A wrapper around an owned OS file primitive. The wrapper
/// allows reading from or writing to the OS file primitive, and
/// will close it once it goes out of scope.
pub struct FileDesc(UnsafeCell<os::RawIo>);

impl Eq for FileDesc {}
impl PartialEq<FileDesc> for FileDesc {
    fn eq(&self, other: &FileDesc) -> bool {
        self.inner() == other.inner()
    }
}

impl fmt::Debug for FileDesc {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_tuple("FileDesc")
            .field(self.inner())
            .finish()
    }
}

impl FileDesc {
    #[cfg(unix)]
    /// Takes ownership of and wraps an OS file primitive.
    pub unsafe fn new(fd: ::std::os::unix::io::RawFd) -> Self {
        Self::from_inner(os::RawIo::new(fd))
    }

    #[cfg(windows)]
    /// Takes ownership of and wraps an OS file primitive.
    pub unsafe fn new(handle: ::std::os::windows::io::RawHandle) -> Self {
        Self::from_inner(os::RawIo::new(handle))
    }

    /// Duplicates the underlying OS file primitive.
    pub fn duplicate(&self) -> Result<Self> {
        Ok(Self::from_inner(try!(self.inner().duplicate())))
    }

    /// Allows for performing read operations on the underlying OS file
    /// handle without requiring unique access to the handle.
    pub unsafe fn unsafe_read(&self) -> &mut Read {
        self.inner_mut()
    }

    /// Allows for performing write operations on the underlying OS file
    /// handle without requiring unique access to the handle.
    pub unsafe fn unsafe_write(&self) -> &mut Write {
        self.inner_mut()
    }

    fn inner(&self) -> &os::RawIo {
        unsafe { &*self.0.get() }
    }

    fn inner_mut(&self) -> &mut os::RawIo {
        unsafe { &mut *self.0.get() }
    }

    fn into_inner(self) -> os::RawIo {
        unsafe { self.0.into_inner() }
    }

    fn from_inner(inner: os::RawIo) -> Self {
        FileDesc(UnsafeCell::new(inner))
    }
}

impl Into<Stdio> for FileDesc {
    fn into(self) -> Stdio { self.into_inner().into() }
}

impl Read for FileDesc {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        self.inner_mut().read(buf)
    }
}

impl Write for FileDesc {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.inner_mut().write(buf)
    }

    fn flush(&mut self) -> Result<()> {
        self.inner_mut().flush()
    }
}

impl Seek for FileDesc {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        self.inner_mut().seek(pos)
    }
}

/// A wrapper for a reader and writer OS pipe pair.
#[derive(Debug)]
pub struct Pipe {
    /// The reader end of the pipe. Anything written to the writer end can be read here.
    pub reader: FileDesc,
    /// The writer end of the pipe. Anything written here can be read from the reader end.
    pub writer: FileDesc,
}

impl Pipe {
    /// Creates and returns a new pipe pair.
    /// On Unix systems, both file descriptors of the pipe will have their CLOEXEC flags set,
    /// however, note that the setting of the flags is nonatomic on BSD systems.
    pub fn new() -> Result<Pipe> {
        let (reader, writer) = try!(os::pipe());
        Ok(Pipe {
            reader: FileDesc::from_inner(reader),
            writer: FileDesc::from_inner(writer),
        })
    }
}

#[doc(hidden)]
/// Duplicates handles for (stdin, stdout, stderr) and returns them in that order.
pub fn dup_stdio() -> Result<(FileDesc, FileDesc, FileDesc)> {
    let (stdin, stdout, stderr) = try!(os::dup_stdio());
    Ok((
        FileDesc::from_inner(stdin),
        FileDesc::from_inner(stdout),
        FileDesc::from_inner(stderr)
    ))
}

#[cfg(test)]
mod tests {
    extern crate tempdir;

    use self::tempdir::TempDir;
    use std::fs::File;
    use std::io::{Read, Write};
    use std::path::PathBuf;
    use std::thread;
    use std::time::Duration;
    use super::*;

    #[test]
    fn test_permissions_readable() {
        assert_eq!(Permissions::Read.readable(), true);
        assert_eq!(Permissions::ReadWrite.readable(), true);
        assert_eq!(Permissions::Write.readable(), false);
    }

    #[test]
    fn test_permissions_writable() {
        assert_eq!(Permissions::Read.writable(), false);
        assert_eq!(Permissions::ReadWrite.writable(), true);
        assert_eq!(Permissions::Write.writable(), true);
    }

    #[test]
    fn test_permissions_open_read() {
        let msg = "hello world!\n";
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push("test_open_read");

        {
            let mut file = File::create(&file_path).unwrap();
            file.write_all(msg.as_bytes()).unwrap();
            file.sync_data().unwrap();
            thread::sleep(Duration::from_millis(100));
        }

        {
            let mut file = Permissions::Read.open(&file_path).unwrap();
            let mut read = String::new();
            file.read_to_string(&mut read).unwrap();
            assert_eq!(msg, read);
        }

        tempdir.close().unwrap();
    }

    #[test]
    fn test_permissions_open_write() {
        let msg = "hello world!\n";
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push("test_open_write");

        {
            let mut file = Permissions::Write.open(&file_path).unwrap();
            file.write_all(msg.as_bytes()).unwrap();
            file.sync_data().unwrap();
            thread::sleep(Duration::from_millis(100));
        }

        {
            let mut file = File::open(&file_path).unwrap();
            let mut read = String::new();
            file.read_to_string(&mut read).unwrap();
            assert_eq!(msg, read);
        }

        tempdir.close().unwrap();
    }

    #[test]
    fn test_permissions_open_readwrite() {
        let msg1 = "hello world!\n";
        let msg2 = "goodbye world!\n";

        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push("test_open_readwrite");

        {
            let mut file1 = Permissions::ReadWrite.open(&file_path).unwrap();
            let mut file2 = Permissions::ReadWrite.open(&file_path).unwrap();

            file1.write_all(msg1.as_bytes()).unwrap();
            file1.sync_data().unwrap();
            thread::sleep(Duration::from_millis(100));

            let mut read = String::new();
            file2.read_to_string(&mut read).unwrap();
            assert_eq!(msg1, read);

            file2.write_all(msg2.as_bytes()).unwrap();
            file2.sync_data().unwrap();
            thread::sleep(Duration::from_millis(100));

            let mut read = String::new();
            file1.read_to_string(&mut read).unwrap();
            assert_eq!(msg2, read);
        }

        tempdir.close().unwrap();
    }

    #[test]
    fn test_pipe() {
        let msg = "pipe message";
        let Pipe { mut reader, mut writer } = Pipe::new().unwrap();

        let guard = thread::spawn(move || {
            writer.write_all(msg.as_bytes()).unwrap();
            writer.flush().unwrap();
            drop(writer);
        });

        let mut read = String::new();
        reader.read_to_string(&mut read).unwrap();
        guard.join().unwrap();
        assert_eq!(msg, read);
    }

    #[test]
    fn test_file_desc_duplicate() {
        let msg1 = "pipe message one\n";
        let msg2 = "pipe message two\n";
        let Pipe { mut reader, mut writer } = Pipe::new().unwrap();

        let guard = thread::spawn(move || {
            writer.write_all(msg1.as_bytes()).unwrap();
            writer.flush().unwrap();

            let mut dup = writer.duplicate().unwrap();
            drop(writer);

            dup.write_all(msg2.as_bytes()).unwrap();
            dup.flush().unwrap();
            drop(dup);
        });

        let mut read = String::new();
        reader.read_to_string(&mut read).unwrap();
        guard.join().unwrap();
        assert_eq!(format!("{}{}", msg1, msg2), read);
    }

    #[test]
    fn test_file_desc_unsafe_read_and_write() {
        let msg = "pipe message";
        let Pipe { reader, writer } = Pipe::new().unwrap();

        let guard = thread::spawn(move || {
            let mut writer_ref = unsafe { writer.unsafe_write() };
            writer_ref.write_all(msg.as_bytes()).unwrap();
            writer_ref.flush().unwrap();
        });

        let mut read = String::new();
        unsafe { reader.unsafe_read().read_to_string(&mut read).unwrap(); }
        guard.join().unwrap();
        assert_eq!(msg, read);
    }

    #[test]
    fn test_file_desc_seeking() {
        use std::io::{Seek, SeekFrom};

        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push("out");

        let mut file: FileDesc = File::create(&file_path).unwrap().into();

        file.write_all(b"foobarbaz").unwrap();
        file.flush().unwrap();

        file.seek(SeekFrom::Start(3)).unwrap();
        file.write_all(b"???").unwrap();
        file.flush().unwrap();

        file.seek(SeekFrom::End(-3)).unwrap();
        file.write_all(b"!!!").unwrap();
        file.flush().unwrap();

        file.seek(SeekFrom::Current(-9)).unwrap();
        file.write_all(b"***").unwrap();
        file.flush().unwrap();

        let mut file: FileDesc = File::open(&file_path).unwrap().into();
        let mut read = String::new();
        file.read_to_string(&mut read).unwrap();

        assert_eq!(read, "***???!!!");
    }

    #[test]
    fn test_is_child_running() {
        use std::process::{Command, Stdio};

        let cmd = if cfg!(windows) {
            "cmd"
        } else {
            "sh"
        };

        let mut child = Command::new(cmd)
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("failed to start up command");

        assert_eq!(true, is_child_running(&child).unwrap());

        // Close the input pipe, shell should exit
        drop(child.stdin.take());
        thread::sleep(Duration::from_millis(100));

        assert_eq!(false, is_child_running(&child).unwrap());
    }
}
