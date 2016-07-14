use std::borrow::Borrow;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Arc;

/// An interface for any `Clone`able wrapper around a `String`.
pub trait StringWrapper: Borrow<String> + Clone + Eq + From<String> + Hash {
    /// Unwrap to an owned `String`.
    fn into_owned(self) -> String;
    /// Borrow the contents as a slice.
    fn as_str(&self) -> &str;
}

impl StringWrapper for String {
    fn into_owned(self) -> String {
        self
    }

    fn as_str(&self) -> &str {
        self
    }
}

impl StringWrapper for Box<String> {
    #[cfg_attr(feature = "clippy", allow(boxed_local))]
    fn into_owned(self) -> String {
        *self
    }

    fn as_str(&self) -> &str {
        self
    }
}

impl StringWrapper for Rc<String> {
    fn into_owned(self) -> String {
        match Rc::try_unwrap(self) {
            Ok(s) => s,
            Err(rc) => (*rc).clone(),
        }
    }

    fn as_str(&self) -> &str {
        self
    }
}

impl StringWrapper for Arc<String> {
    fn into_owned(self) -> String {
        match Arc::try_unwrap(self) {
            Ok(s) => s,
            Err(arc) => (*arc).clone(),
        }
    }

    fn as_str(&self) -> &str {
        self
    }
}
