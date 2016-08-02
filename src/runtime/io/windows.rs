//! Defines interfaces and methods for doing IO operations on Windows HANDLEs.

use kernel32;
use winapi;

use std::fmt;
use std::fs::File;
use std::io::{Error, ErrorKind, Read, Result, SeekFrom, Write};
use std::ops::{Deref, DerefMut};
use std::os::raw::c_void as HANDLE;
use std::os::windows::io::{AsRawHandle, FromRawHandle, IntoRawHandle, RawHandle};
use std::process::Stdio;
use std::ptr;
use std::ptr::Unique as StdUnique;
use super::FileDesc;

/// Return value used by `GetExitCodeProcess` to denote if a process
/// is still running.
/// Definition comes from
/// https://msdn.microsoft.com/en-us/library/windows/desktop/ms683189(v=vs.85).aspx
// FIXME: Did not see this defined by the winapi crate, would be useful upstream
// see https://github.com/retep998/winapi-rs/issues/309
const STILL_ACTIVE: winapi::DWORD = 259;

// A Debug wrapper around `std::ptr::Unique`
struct Unique<T>(StdUnique<T>);

impl<T> Deref for Unique<T> {
    type Target = StdUnique<T>;
    fn deref(&self) -> &Self::Target { &self.0 }
}

impl<T> DerefMut for Unique<T> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl fmt::Debug for Unique<HANDLE> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{:p}", *self.0)
    }
}

/// A wrapper around an owned Windows HANDLE. The wrapper
/// allows reading from or write to the HANDLE, and will
/// close it once it goes out of scope.
#[derive(Debug, Eq)]
pub struct RawIo {
    /// The underlying HANDLE.
    handle: Unique<HANDLE>,
    /// Indicates whether the HANDLE has been extracted and
    /// transferred ownership or whether we should close it.
    must_close: bool,
}

impl PartialEq<RawIo> for RawIo {
    fn eq(&self, other: &RawIo) -> bool {
        **(self.handle) == **(other.handle)
    }
}

impl Into<Stdio> for RawIo {
    fn into(self) -> Stdio {
        unsafe { FromRawHandle::from_raw_handle(self.into_inner()) }
    }
}

impl FromRawHandle for FileDesc {
    unsafe fn from_raw_handle(handle: RawHandle) -> Self {
        Self::new(handle)
    }
}

impl AsRawHandle for FileDesc {
    fn as_raw_handle(&self) -> RawHandle { self.inner().inner() }
}

impl IntoRawHandle for FileDesc {
    fn into_raw_handle(self) -> RawHandle { unsafe { self.into_inner().into_inner() } }
}

impl From<File> for FileDesc {
    fn from(file: File) -> Self {
        unsafe { FromRawHandle::from_raw_handle(file.into_raw_handle()) }
    }
}

impl RawIo {
    /// Takes ownership of and wraps an OS file HANDLE.
    pub unsafe fn new(handle: RawHandle) -> Self {
        RawIo {
            handle: Unique(StdUnique::new(handle)),
            must_close: true,
        }
    }

    /// Unwraps the underlying HANDLE and transfers ownership to the caller.
    pub unsafe fn into_inner(mut self) -> RawHandle {
        // Make sure our desctructor doesn't actually close
        // the handle we just transfered to the caller.
        self.must_close = false;
        **self.handle
    }

    /// Returns the underlying HANDLE without transfering ownership.
    pub fn inner(&self) -> RawHandle { **self.handle }

    /// Duplicates the underlying HANDLE.
    // Adapted from rust: libstd/sys/windows/handle.rs
    pub fn duplicate(&self) -> Result<Self> {
        unsafe {
            let mut ret = winapi::INVALID_HANDLE_VALUE;
            try!(cvt({
                let cur_proc = kernel32::GetCurrentProcess();

                kernel32::DuplicateHandle(cur_proc,
                                          **self.handle,
                                          cur_proc,
                                          &mut ret,
                                          0 as winapi::DWORD,
                                          winapi::FALSE,
                                          winapi::DUPLICATE_SAME_ACCESS)
            }));
            Ok(RawIo::new(ret))
        }
    }

    /// Reads from the underlying HANDLE.
    // Taken from rust: libstd/sys/windows/handle.rs
    pub fn read_inner(&self, buf: &mut [u8]) -> Result<usize> {
        let mut read = 0;
        let res = cvt(unsafe {
            kernel32::ReadFile(**self.handle,
                               buf.as_ptr() as winapi::LPVOID,
                               buf.len() as winapi::DWORD,
                               &mut read,
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
    pub fn write_inner(&self, buf: &[u8]) -> Result<usize> {
        let mut amt = 0;
        try!(cvt(unsafe {
            kernel32::WriteFile(**self.handle,
                                buf.as_ptr() as winapi::LPVOID,
                                buf.len() as winapi::DWORD,
                                &mut amt,
                                ptr::null_mut())
        }));
        Ok(amt as usize)
    }

    /// Seeks the underlying HANDLE.
    // Taken from rust: libstd/sys/windows/fs.rs
    pub fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        let (whence, pos) = match pos {
            SeekFrom::Start(n) => (winapi::FILE_BEGIN, n as i64),
            SeekFrom::End(n) => (winapi::FILE_END, n),
            SeekFrom::Current(n) => (winapi::FILE_CURRENT, n),
        };
        let pos = pos as winapi::LARGE_INTEGER;
        let mut newpos = 0;
        try!(cvt(unsafe {
            kernel32::SetFilePointerEx(self.handle.get_mut(), pos, &mut newpos, whence)
        }));
        Ok(newpos as u64)
    }
}

impl Read for RawIo {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        self.read_inner(buf)
    }
}

impl Write for RawIo {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.write_inner(buf)
    }

    fn flush(&mut self) -> Result<()> { Ok(()) }
}

impl Drop for RawIo {
    // Adapted from rust: src/libstd/sys/windows/handle.rs
    fn drop(&mut self) {
        if self.must_close {
            unsafe { let _ = kernel32::CloseHandle(**self.handle); }
        }
    }
}

trait IsZero {
    fn is_zero(&self) -> bool;
}

macro_rules! impl_is_zero {
    ($($t:ident)*) => ($(impl IsZero for $t {
        fn is_zero(&self) -> bool {
            *self == 0
        }
    })*)
}

impl_is_zero! { i8 i16 i32 i64 isize u8 u16 u32 u64 usize }

impl<T> IsZero for *mut T {
    fn is_zero(&self) -> bool {
        self.is_null()
    }
}

fn cvt<I: IsZero>(i: I) -> Result<I> {
    if i.is_zero() {
        Err(Error::last_os_error())
    } else {
        Ok(i)
    }
}

/// Creates and returns a `(reader, writer)` pipe pair.
pub fn pipe() -> Result<(RawIo, RawIo)> {
    use std::ptr;
    unsafe {
        let mut reader = winapi::INVALID_HANDLE_VALUE;
        let mut writer = winapi::INVALID_HANDLE_VALUE;
        try!(cvt(kernel32::CreatePipe(&mut reader, &mut writer, ptr::null_mut(), 0)));

        Ok((RawIo::new(reader), RawIo::new(writer)))
    }
}

/// Duplicates file HANDLES for (stdin, stdout, stderr) and returns them in that order.
pub fn dup_stdio() -> Result<(RawIo, RawIo, RawIo)> {
    fn dup_handle(handle: winapi::DWORD) -> Result<RawIo> {
        unsafe {
            let current_process = kernel32::GetCurrentProcess();
            let mut new_handle = winapi::INVALID_HANDLE_VALUE;

            try!(cvt(kernel32::DuplicateHandle(current_process,
                                               kernel32::GetStdHandle(handle),
                                               current_process,
                                               &mut new_handle,
                                               0 as winapi::DWORD,
                                               winapi::FALSE,
                                               winapi::DUPLICATE_SAME_ACCESS)));

            Ok(RawIo::new(new_handle))
        }
    }

    Ok((
        try!(dup_handle(winapi::STD_INPUT_HANDLE)),
        try!(dup_handle(winapi::STD_OUTPUT_HANDLE)),
        try!(dup_handle(winapi::STD_ERROR_HANDLE))
    ))
}

/// Retrieves the process identifier of the calling process.
pub fn getpid() -> winapi::DWORD {
    unsafe {
        kernel32::GetCurrentProcessId()
    }
}

/// Safe wrapper around `is_child_process_running`. See docs for more info.
pub fn is_child_running(child: &::std::process::Child) -> Result<bool> {
    use std::os::windows::io::AsRawHandle;
    unsafe {
        is_child_process_running(child.as_raw_handle())
    }
}

/// Checks if a given process handle is still running.
///
/// Note: this function has Windows specific behavior. Check the documentation of
/// its Unix counterpart if caller supports both platforms.
///
/// Warning: Windows uses a `STILL_ACTIVE` constant to denote if a process
/// is running, however, it is possible that the process can exit with that.
/// In this situation, this function will treat the process as still running.
/// It is up to the caller to perform any additional checks to avoid getting
/// stuck in a loop.
pub unsafe fn is_child_process_running(handle: RawHandle) -> Result<bool> {
    let mut status = 0;
    try!(cvt(kernel32::GetExitCodeProcess(handle, &mut status)));
    Ok(status == STILL_ACTIVE)
}
