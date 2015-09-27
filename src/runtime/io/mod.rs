//! Defines interfaces and methods for doing OS agnostic file IO operations.

#[cfg(unix)]
#[path = "unix.rs"] mod os;
#[cfg(windows)]
#[path = "windows.rs"] mod os;

use std::fmt;
use std::io::{Read, Result, Write};
use std::process::Stdio;

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

impl Permissions {
    pub fn readable(&self) -> bool {
        match *self {
            Permissions::Read |
            Permissions::ReadWrite => true,
            Permissions::Write => false,
        }
    }

    pub fn writable(&self) -> bool {
        match *self {
            Permissions::Read => false,
            Permissions::Write |
            Permissions::ReadWrite => true,
        }
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
#[derive(Debug)]
pub struct FileDesc(os::RawIo);

impl FileDesc {
    #[cfg(unix)]
    /// Takes ownership of and wraps an OS file primitive.
    pub unsafe fn new(fd: ::std::os::unix::io::RawFd) -> Self {
        FileDesc(os::RawIo::new(fd))
    }

    #[cfg(windows)]
    /// Takes ownership of and wraps an OS file primitive.
    pub unsafe fn new(handle: ::std::os::windows::io::RawHandle) -> Self {
        FileDesc(os::RawIo::new(handle))
    }

    /// Duplicates the underlying OS file primitive.
    pub fn duplicate(&self) -> Result<Self> {
        self.0.duplicate().map(FileDesc)
    }
}

impl Into<Stdio> for FileDesc {
    fn into(self) -> Stdio { self.0.into() }
}

impl Read for FileDesc {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        self.0.read(buf)
    }
}

impl Write for FileDesc {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.0.write(buf)
    }

    fn flush(&mut self) -> Result<()> { Ok(()) }
}

/// Creates and returns a `(reader, writer)` pipe pair.
pub fn pipe() -> Result<(FileDesc, FileDesc)> {
    let (reader, writer) = try!(os::pipe());
    Ok((FileDesc(reader), FileDesc(writer)))
}
