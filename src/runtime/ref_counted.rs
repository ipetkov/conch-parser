use std::ops::Deref;
use std::rc::Rc;
use std::sync::Arc;

/// A convenience trait to abstract over Arc<T> and Rc<T> APIs.
pub trait RefCounted<T>: Sized + Clone + Deref<Target = T> + From<T> {
    /// Returns a mutable reference to the contained value if the wrapper
    /// has a single, unique, reference.
    ///
    /// Returns `None` if the `Rc<T>` is not unique.
    ///
    fn get_mut(&mut self) -> Option<&mut T>;

    /// Make a mutable reference into the given implementation. If the
    /// implementation has more than one strong reference, or any weak
    /// references, the inner data is cloned.
    ///
    /// This is also referred to as a copy-on-write.
    fn make_mut(&mut self) -> &mut T where T: Clone;
}

impl<T> RefCounted<T> for Rc<T> {
    fn get_mut(&mut self) -> Option<&mut T> {
        Rc::get_mut(self)
    }

    fn make_mut(&mut self) -> &mut T where T: Clone {
        Rc::make_mut(self)
    }
}

impl<T> RefCounted<T> for Arc<T> {
    fn get_mut(&mut self) -> Option<&mut T> {
        Arc::get_mut(self)
    }

    fn make_mut(&mut self) -> &mut T where T: Clone {
        Arc::make_mut(self)
    }
}
