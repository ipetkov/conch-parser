//! Defines interfaces and methods for doing IO operations on UNIX file descriptors.

use libc::{self, c_void, size_t};
use std::fs::File;
use std::io::{Error, ErrorKind, Result};
use std::num::One;
use std::ops::Neg;
use std::os::unix::io::{RawFd, AsRawFd, FromRawFd, IntoRawFd};
use std::process::Stdio;
use super::FileDesc;

/// A wrapper around an owned UNIX file descriptor. The wrapper
/// allows reading from or write to the descriptor, and will
/// close it once it goes out of scope.
#[derive(Debug)]
pub struct RawIo {
    /// The underlying descriptor.
    fd: RawFd,
    /// Indicates whether the fd has been extracted and
    /// transferred ownership or whether we should close it.
    must_close: bool,
}

impl Into<Stdio> for RawIo {
    fn into(self) -> Stdio {
        unsafe { FromRawFd::from_raw_fd(self.into_inner()) }
    }
}

impl FromRawFd for FileDesc {
    unsafe fn from_raw_fd(fd: RawFd) -> Self {
        Self::new(fd)
    }
}

impl AsRawFd for FileDesc {
    fn as_raw_fd(&self) -> RawFd { self.0.inner() }
}

impl IntoRawFd for FileDesc {
    fn into_raw_fd(self) -> RawFd { unsafe { self.0.into_inner() } }
}

impl From<File> for FileDesc {
    fn from(file: File) -> Self {
        unsafe { FromRawFd::from_raw_fd(file.into_raw_fd()) }
    }
}

impl RawIo {
    /// Takes ownership of and wraps an OS file descriptor.
    pub unsafe fn new(fd: RawFd) -> Self {
        RawIo {
            fd: fd,
            must_close: true,
        }
    }

    /// Unwraps the underlying file descriptor and transfers ownership to the caller.
    pub unsafe fn into_inner(mut self) -> RawFd {
        // Make sure our desctructor doesn't actually close
        // the fd we just transfered to the caller.
        self.must_close = false;
        self.fd
    }

    /// Returns the underlying file descriptor without transfering ownership.
    pub fn inner(&self) -> RawFd { self.fd }

    /// Duplicates the underlying file descriptor via `libc::dup`.
    pub fn duplicate(&self) -> Result<Self> {
        unsafe {
            Ok(RawIo::new(try!(cvt_r(|| { libc::dup(self.fd) }))))
        }
    }

    /// Reads from the underlying file descriptor.
    // Taken from rust: libstd/sys/unix/fd.rs
    pub fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let ret = try!(cvt(unsafe {
            libc::read(self.fd,
                       buf.as_mut_ptr() as *mut c_void,
                       buf.len() as size_t)
        }));
        Ok(ret as usize)
    }

    /// Writes to the underlying file descriptor.
    // Taken from rust: libstd/sys/unix/fd.rs
    pub fn write(&mut self, buf: &[u8]) -> Result<usize> {
        let ret = try!(cvt(unsafe {
            libc::write(self.fd,
                        buf.as_ptr() as *const c_void,
                        buf.len() as size_t)
        }));
        Ok(ret as usize)
    }
}

impl Drop for RawIo {
    // Adapted from rust: libstd/sys/unix/fd.rs
    fn drop(&mut self) {
        // Note that errors are ignored when closing a file descriptor. The
        // reason for this is that if an error occurs we don't actually know if
        // the file descriptor was closed or not, and if we retried (for
        // something like EINTR), we might close another valid file descriptor
        // (opened after we closed ours).
        if self.must_close {
            let _ = unsafe { libc::close(self.fd) };
        }
    }
}

// Taken from rust: libstd/sys/unix/mod.rs
fn cvt<T: One + PartialEq + Neg<Output=T>>(t: T) -> Result<T> {
    let one: T = T::one();
    if t == -one {
        Err(Error::last_os_error())
    } else {
        Ok(t)
    }
}

// Taken from rust: libstd/sys/unix/mod.rs
fn cvt_r<T, F>(mut f: F) -> Result<T>
    where T: One + PartialEq + Neg<Output=T>, F: FnMut() -> T
{
    loop {
        match cvt(f()) {
            Err(ref e) if e.kind() == ErrorKind::Interrupted => {}
            other => return other,
        }
    }
}

/// Creates and returns a `(reader, writer)` pipe pair.
pub fn pipe() -> Result<(RawIo, RawIo)> {
    // FIXME: these should probably have NONBLOCK and CLOEXEC flags when libc catches up
    use libc::pipe;
    unsafe {
        let mut fds = [0; 2];
        try!(cvt_r(|| { pipe(fds.as_mut_ptr()) }));
        let reader = RawIo::new(fds[0]);
        let writer = RawIo::new(fds[1]);
        Ok((reader, writer))
    }
}
