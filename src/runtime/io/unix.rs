//! Defines interfaces and methods for doing IO operations on UNIX file descriptors.

use libc::{self, c_void, size_t};
use std::io::{ErrorKind, Result};
use std::num::One;
use std::ops::Neg;
use std::os::unix::io::{RawFd, AsRawFd, FromRawFd, IntoRawFd};
use std::process::Stdio;
use super::{cvt, FileDesc};

/// A wrapper around an owned UNIX file descriptor. The wrapper
/// allows reading from or write to the descriptor, and will
/// close it once it goes out of scope.
#[derive(Debug)]
pub struct RawIo(RawFd);

impl Into<Stdio> for RawIo {
    fn into(self) -> Stdio {
        unsafe { FromRawFd::from_raw_fd(self.0) }
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

impl RawIo {
    /// Takes ownership of and wraps an OS file descriptor.
    pub unsafe fn new(fd: RawFd) -> Self { RawIo(fd) }

    /// Unwraps the underlying file descriptor and transfers ownership to the caller.
    pub unsafe fn into_inner(self) -> RawFd { self.0 }

    /// Returns the underlying file descriptor without transfering ownership.
    pub fn inner(&self) -> RawFd { self.0 }

    /// Duplicates the underlying file descriptor via `libc::dup`.
    pub fn duplicate(&self) -> Result<Self> {
        unsafe {
            cvt_r(|| { libc::dup(self.0) }).map(RawIo)
        }
    }

    /// Reads from the underlying file descriptor.
    // Taken from rust: libstd/sys/unix/fd.rs
    pub fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let ret = try!(cvt(unsafe {
            libc::read(self.0,
                       buf.as_mut_ptr() as *mut c_void,
                       buf.len() as size_t)
        }));
        Ok(ret as usize)
    }

    /// Writes to the underlying file descriptor.
    // Taken from rust: libstd/sys/unix/fd.rs
    pub fn write(&mut self, buf: &[u8]) -> Result<usize> {
        let ret = try!(cvt(unsafe {
            libc::write(self.0,
                        buf.as_ptr() as *const c_void,
                        buf.len() as size_t)
        }));
        Ok(ret as usize)
    }
}

impl Drop for RawIo {
    // A very hacky way to close raw descriptors (by transfering ownership to
    // someone else), but it keeps us from doing the `libc` calls ourselves.
    fn drop(&mut self) { let _: Stdio = RawIo(self.0).into(); }
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
