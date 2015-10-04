//! Defines interfaces and methods for doing IO operations on Windows HANDLEs.

use libc;
use std::fs::File;
use std::io::{Error, Result};
use std::num::Zero;
use std::os::windows::io::{RawHandle, FromRawHandle, IntoRawHandle};
use std::process::Stdio;
use super::FileDesc;

#[link(name = "kernel32")]
extern {
    fn CreatePipe(hReadPipe: libc::LPHANDLE,
                  hWritePipe: libc::LPHANDLE,
                  lpPipeAttributes: libc::LPSECURITY_ATTRIBUTES,
                  nSize: libc::DWORD) -> libc::BOOL;
}

/// A wrapper around an owned Windows HANDLE. The wrapper
/// allows reading from or write to the HANDLE, and will
/// close it once it goes out of scope.
#[derive(Debug)]
pub struct RawIo {
    /// The underlying HANDLE.
    handle: RawHandle,
    /// Indicates whether the HANDLE has been extracted and
    /// transferred ownership or whether we should close it.
    must_close: bool,
}

impl Into<Stdio> for RawIo {
    fn into(self) -> Stdio {
        unsafe { sys_io::FromRawHandle::from_raw_handle(self.into_inner()) }
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

impl From<File> for FileDesc {
    fn from(file: File) -> Self {
        unsafe { FromRawHandle::from_raw_handle(file.into_raw_handle()) }
    }
}

impl RawIo {
    /// Takes ownership of and wraps an OS file HANDLE.
    pub unsafe fn new(handle: sys_io::RawHandle) -> Self {
        RawIo {
            handle: handle,
            must_close: true,
        }
    }

    /// Unwraps the underlying HANDLE and transfers ownership to the caller.
    pub unsafe fn into_inner(mut self) -> RawHandle {
        // Make sure our desctructor doesn't actually close
        // the handle we just transfered to the caller.
        self.must_close = false;
        self.handle
    }

    /// Returns the underlying HANDLE without transfering ownership.
    pub fn inner(&self) -> RawFd { self.handle }

    /// Duplicates the underlying HANDLE.
    // Adapted from rust: libstd/sys/windows/handle.rs
    pub fn duplicate(&self) -> Result<Self> {
        let mut ret = 0 as libc::HANDLE;
        try!(cvt(unsafe {
            let cur_proc = libc::GetCurrentProcess();

            libc::DuplicateHandle(cur_proc, self.handle, cur_proc, &mut ret,
                                  0 as libc::DWORD, false as libc::BOOL,
                                  libc::DUPLICATE_SAME_ACCESS)
        }));
        Ok(RawIo(ret))
    }

    /// Reads from the underlying HANDLE.
    pub fn read(&self, buf: &mut [u8]) -> Result<usize> {
        unsafe { self.unsafe_read(buf) }
    }

    /// Writes to the underlying HANDLE.
    pub fn write(&self, buf: &[u8]) -> Result<usize> {
        unsafe { self.unsafe_write(buf) }
    }

    // Performs a read operation on the underlying HANDLE without
    // guaranteeing the caller has unique access to it.
    // Taken from rust: libstd/sys/windows/handle.rs
    #[doc(hidden)]
    pub unsafe fn unsafe_read(&self, buf: &mut [u8]) -> Result<usize> {
        let mut read = 0;
        let res = cvt(libc::ReadFile(self.handle, buf.as_ptr() as libc::LPVOID,
                                     buf.len() as libc::DWORD, &mut read,
                                     ptr::null_mut()));

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

    // Performs a write operation on the underlying HANDLE without
    // guaranteeing the caller has unique access to it.
    // Taken from rust: libstd/sys/windows/handle.rs
    #[doc(hidden)]
    pub unsafe fn unsafe_write(&self, buf: &[u8]) -> Result<usize> {
        let mut amt = 0;
        try!(cvt(libc::WriteFile(self.handle, buf.as_ptr() as libc::LPVOID,
                                 buf.len() as libc::DWORD, &mut amt,
                                 ptr::null_mut())));
        Ok(amt as usize)
    }
}

impl Drop for RawIo {
    // Adapted from rust: src/libstd/sys/windows/handle.rs
    fn drop(&mut self) {
        if self.must_close {
            unsafe { let _ = libc::CloseHandle(self.handle); }
        }
    }
}

// Taken from rust: src/libstd/sys/windows/mod.rs
fn cvt<I: PartialEq + Zero>(i: I) -> io::Result<I> {
    if i == I::zero() {
        Err(Error::last_os_error())
    } else {
        Ok(i)
    }
}

/// Creates and returns a `(reader, writer)` pipe pair.
pub fn pipe() -> Result<(RawIo, RawIo)> {
    use std::ptr;
    unsafe {
        let mut reader = 0;
        let mut writer = 0;
        try!(cvt(CreatePipe(&mut reader, &mut writer, ptr::null(), 0)));
        Ok((RawIo::new(reader), RawIo::new(writer)))
    }
}
