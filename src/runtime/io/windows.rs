//! Defines interfaces and methods for doing IO operations on Windows HANDLEs.

use libc;
use std::io::Result;
use std::os::windows::io::{RawHandle, FromRawHandle, IntoRawHandle};
use std::process::Stdio;
use super::{cvt, FileDesc};

/// A wrapper around an owned Windows HANDLE. The wrapper
/// allows reading from or write to the HANDLE, and will
/// close it once it goes out of scope.
#[derive(Debug)]
pub struct RawIo(RawHandle);

impl Into<Stdio> for RawIo {
    fn into(self) -> Stdio {
        unsafe { sys_io::FromRawHandle::from_raw_handle(self.0) }
    }
}

impl FromRawHandle for FileDesc {
    unsafe fn from_raw_handle(handle: RawHandle) -> Self {
        Self::new(handle)
    }
}

impl AsRawHandle for FileDesc {
    fn as_raw_handle(&self) -> RawHandle { self.0.inner() }
}

impl IntoRawHandle for FileDesc {
    fn into_raw_handle(self) -> RawHandle { self.0.into_inner() }
}

impl RawIo {
    /// Takes ownership of and wraps an OS file HANDLE.
    pub unsafe fn new(handle: sys_io::RawHandle) -> Self { RawIo(handle) }

    /// Unwraps the underlying HANDLE and transfers ownership to the caller.
    pub unsafe fn into_inner(self) -> RawHandle { self.0 }

    /// Returns the underlying HANDLE without transfering ownership.
    pub fn inner(&self) -> RawFd { self.0 }

    /// Duplicates the underlying HANDLE.
    // Adapted from rust: libstd/sys/windows/handle.rs
    pub fn duplicate(&self) -> Result<Self> {
        let mut ret = 0 as libc::HANDLE;
        try!(cvt(unsafe {
            let cur_proc = libc::GetCurrentProcess();

            libc::DuplicateHandle(cur_proc, self.0, cur_proc, &mut ret,
                                  0 as libc::DWORD, false as libc::BOOL,
                                  libc::DUPLICATE_SAME_ACCESS)
        }));
        Ok(RawIo(ret))
    }

    /// Reads from the underlying HANDLE.
    // Taken from rust: libstd/sys/windows/handle.rs
    pub fn read(&self, buf: &mut [u8]) -> Result<usize> {
        let mut read = 0;
        let res = cvt(unsafe {
            libc::ReadFile(self.0, buf.as_ptr() as libc::LPVOID,
            buf.len() as libc::DWORD, &mut read,
            ptr::null_mut())
        });

        match res {
            Ok(_) => Ok(read as usize),

            // The special treatment of BrokenPipe is to deal with Windows
            // pipe semantics, which yields this error when *reading* from
            // a pipe after the other end has closed; we interpret that as
            // EOF on the pipe.
                Err(ref e) if e.kind() == ErrorKind::BrokenPipe => Ok(0),

            Err(e) => Err(e)
        }
    }

    /// Writes to the underlying HANDLE.
    // Taken from rust: libstd/sys/windows/handle.rs
    pub fn write(&self, buf: &[u8]) -> Result<usize> {
        let mut amt = 0;
        try!(cvt(unsafe {
            libc::WriteFile(self.0, buf.as_ptr() as libc::LPVOID,
            buf.len() as libc::DWORD, &mut amt,
            ptr::null_mut())
        }));
        Ok(amt as usize)
    }
}

impl Drop for RawIo {
    // A very hacky way to close raw descriptors (by transfering ownership to
    // someone else), but it keeps us from doing the `libc` calls ourselves.
    fn drop(&mut self) { let _: Stdio = RawIo(self.0).into(); }
}
