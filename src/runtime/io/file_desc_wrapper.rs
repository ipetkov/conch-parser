use runtime::io::FileDesc;

use std::borrow::Borrow;
use std::rc::Rc;
use std::sync::Arc;

/// An interface for any `Clone`able wrapper around a `FileDesc`.
pub trait FileDescWrapper: From<FileDesc> + Clone + Borrow<FileDesc> {
    /// Unwrap to an owned `FileDesc` handle.
    fn try_unwrap(self) -> Result<FileDesc, Self>;
}

impl FileDescWrapper for Rc<FileDesc> {
    fn try_unwrap(self) -> Result<FileDesc, Self> {
        Rc::try_unwrap(self)
    }
}

impl FileDescWrapper for Arc<FileDesc> {
    fn try_unwrap(self) -> Result<FileDesc, Self> {
        Arc::try_unwrap(self)
    }
}
