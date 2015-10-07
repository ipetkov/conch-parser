//! Defines interfaces and methods for doing OS agnostic file IO operations.

#[cfg(unix)]
#[path = "unix.rs"] mod os;
#[cfg(windows)]
#[path = "windows.rs"] mod os;

use std::cell::UnsafeCell;
use std::fmt;
use std::fs;
use std::io::{Read, Result, Write};
use std::path;
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

impl FileDesc {
    #[cfg(unix)]
    /// Takes ownership of and wraps an OS file primitive.
    pub unsafe fn new(fd: ::std::os::unix::io::RawFd) -> Self {
        FileDesc(UnsafeCell::new(os::RawIo::new(fd)))
    }

    #[cfg(windows)]
    /// Takes ownership of and wraps an OS file primitive.
    pub unsafe fn new(handle: ::std::os::windows::io::RawHandle) -> Self {
        FileDesc(UnsafeCell::new(os::RawIo::new(handle)))
    }

    /// Duplicates the underlying OS file primitive.
    pub fn duplicate(&self) -> Result<Self> {
        Ok(FileDesc(UnsafeCell::new(try!(self.inner().duplicate()))))
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

impl fmt::Debug for FileDesc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "FileDesc({:?})", self.inner())
    }
}

/// A wrapper for a reader and writer OS pipe pair.
pub struct Pipe {
    pub reader: FileDesc,
    pub writer: FileDesc,
}

impl Pipe {
    /// Creates and returns a new pipe pair.
    pub fn new() -> Result<Pipe> {
        let (reader, writer) = try!(os::pipe());
        Ok(Pipe {
            reader: FileDesc(UnsafeCell::new(reader)),
            writer: FileDesc(UnsafeCell::new(writer)),
        })
    }
}

impl Read for Pipe {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        self.reader.read(buf)
    }
}

impl Write for Pipe {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.writer.write(buf)
    }

    fn flush(&mut self) -> Result<()> {
        self.writer.flush()
    }
}
