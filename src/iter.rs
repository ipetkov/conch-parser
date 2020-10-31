//! An module of utilities for working with `Token` iterators.

use crate::parse::SourcePos;

mod backtick;
mod balanced;

pub use self::backtick::BacktickBackslashRemover;
pub use self::balanced::Balanced;

/// An iterator that can track its internal position in the stream.
pub trait PositionIterator: Iterator {
    /// Get the current position of the iterator.
    fn pos(&self) -> SourcePos;
}

impl<T> PositionIterator for &'_ mut T
where
    T: ?Sized + PositionIterator,
{
    fn pos(&self) -> SourcePos {
        (**self).pos()
    }
}

impl<T> PositionIterator for Box<T>
where
    T: ?Sized + PositionIterator,
{
    fn pos(&self) -> SourcePos {
        (**self).pos()
    }
}

/// An iterator that supports peeking a single element in the stream.
///
/// Identical to `std::iter::Peekable` but in a trait form.
pub trait PeekableIterator: Iterator {
    /// Peek at the next item, identical to `std::iter::Peekable::peek`.
    fn peek(&mut self) -> Option<&Self::Item>;
}

impl<T> PeekableIterator for &'_ mut T
where
    T: ?Sized + PeekableIterator,
{
    fn peek(&mut self) -> Option<&Self::Item> {
        (**self).peek()
    }
}

impl<T> PeekableIterator for Box<T>
where
    T: ?Sized + PeekableIterator,
{
    fn peek(&mut self) -> Option<&Self::Item> {
        (**self).peek()
    }
}

impl<I> PeekableIterator for std::iter::Peekable<I>
where
    I: Iterator,
{
    fn peek(&mut self) -> Option<&Self::Item> {
        std::iter::Peekable::peek(self)
    }
}

/// A marker trait that unifies `PeekableIterator` and `PositionIterator`.
pub trait PeekablePositionIterator: PeekableIterator + PositionIterator {}

impl<T> PeekablePositionIterator for T where T: ?Sized + PeekableIterator + PositionIterator {}

/// An interface for iterators which support peeking of more than one item.
pub trait Multipeek: Iterator {
    /// Create a new cursor for peeking many future items. When dropped it will automatically
    /// `reset_peek`.
    ///
    /// # Examples
    /// ```no_run
    /// use conch_parser::iter::Multipeek;
    ///
    /// # struct Dummy<T>(Vec<T>);
    /// # impl<T> Iterator for Dummy<T> {
    /// #   type Item = T;
    /// #   fn next(&mut self) -> Option<Self::Item> {
    /// #     unimplemented!()
    /// #   }
    /// # }
    /// # impl<T> Multipeek for Dummy<T> {
    /// #   fn advance_peek(&mut self) -> Option<&Self::Item> {
    /// #     unimplemented!()
    /// #   }
    /// #   fn reset_peek(&mut self) {
    /// #     unimplemented!()
    /// #   }
    /// # }
    /// fn make_multipeek<T>(v: Vec<T>) -> impl Multipeek<Item = T> {
    ///   // ...
    /// #  Dummy(v)
    /// }
    ///
    /// let mut iter = make_multipeek(vec![1usize, 2, 3]);
    ///
    /// let mut peeker = iter.multipeek();
    /// assert_eq!(Some(&1), peeker.peek_next());
    /// assert_eq!(Some(&2), peeker.peek_next());
    /// assert_eq!(Some(&3), peeker.peek_next());
    /// assert_eq!(None, peeker.peek_next());
    /// drop(peeker);
    ///
    /// let mut peeker = iter.multipeek();
    /// assert_eq!(Some(&1), peeker.peek_next());
    /// assert_eq!(Some(&2), peeker.peek_next());
    /// drop(peeker);
    ///
    /// let mut peeker = iter.multipeek();
    /// assert_eq!(Some(&1), peeker.peek_next());
    /// drop(peeker);
    /// ```
    fn multipeek(&mut self) -> MultipeekCursor<'_, Self> {
        self.reset_peek();
        MultipeekCursor { parent: self }
    }

    /// Peek forward another more item which will be yielded in the future.
    ///
    /// This method should begin by yielding items in the order which
    /// `Iterator::next` would yield them. Calling `Iterator::next` should
    /// reset this internal position back to the start.
    ///
    /// Note: callers should utilize the cursor returned by `multipeek`. Below
    /// is an example to illustrate behavior for implementors.
    ///
    /// ```no_run
    /// use conch_parser::iter::Multipeek;
    ///
    /// # struct Dummy<T>(Vec<T>);
    /// # impl<T> Iterator for Dummy<T> {
    /// #   type Item = T;
    /// #   fn next(&mut self) -> Option<Self::Item> {
    /// #     unimplemented!()
    /// #   }
    /// # }
    /// # impl<T> Multipeek for Dummy<T> {
    /// #   fn advance_peek(&mut self) -> Option<&Self::Item> {
    /// #     unimplemented!()
    /// #   }
    /// #   fn reset_peek(&mut self) {
    /// #     unimplemented!()
    /// #   }
    /// # }
    /// fn make_multipeek<T>(v: Vec<T>) -> impl Multipeek<Item = T> {
    ///   // ...
    /// #  Dummy(v)
    /// }
    ///
    /// let mut iter = make_multipeek(vec![1usize, 2, 3]);
    /// assert_eq!(Some(1), iter.next());
    ///
    /// assert_eq!(Some(&2), iter.advance_peek());
    /// assert_eq!(Some(&3), iter.advance_peek());
    /// assert_eq!(None, iter.advance_peek());
    ///
    /// assert_eq!(Some(2), iter.next());
    ///
    /// assert_eq!(Some(&3), iter.advance_peek());
    /// assert_eq!(None, iter.advance_peek());
    ///
    /// assert_eq!(Some(3), iter.next());
    /// assert_eq!(None, iter.advance_peek());
    /// ```
    fn advance_peek(&mut self) -> Option<&Self::Item>;

    /// Reset the peek position back to the start.
    ///
    /// Note: callers should utilize the cursor returned by `multipeek`. Below
    /// is an example to illustrate behavior for implementors.
    ///
    /// ```no_run
    /// use conch_parser::iter::Multipeek;
    ///
    /// # struct Dummy<T>(Vec<T>);
    /// # impl<T> Iterator for Dummy<T> {
    /// #   type Item = T;
    /// #   fn next(&mut self) -> Option<Self::Item> {
    /// #     unimplemented!()
    /// #   }
    /// # }
    /// # impl<T> Multipeek for Dummy<T> {
    /// #   fn advance_peek(&mut self) -> Option<&Self::Item> {
    /// #     unimplemented!()
    /// #   }
    /// #   fn reset_peek(&mut self) {
    /// #     unimplemented!()
    /// #   }
    /// # }
    /// fn make_multipeek<T>(v: Vec<T>) -> impl Multipeek<Item = T> {
    ///   // ...
    /// #  Dummy(v)
    /// }
    ///
    /// let mut iter = make_multipeek(vec![1usize, 2, 3]);
    ///
    /// assert_eq!(Some(&1), iter.advance_peek());
    /// assert_eq!(Some(&2), iter.advance_peek());
    ///
    /// iter.reset_peek();
    ///
    /// assert_eq!(Some(&1), iter.advance_peek());
    /// assert_eq!(Some(&2), iter.advance_peek());
    /// ```
    fn reset_peek(&mut self);
}

impl<T> Multipeek for &'_ mut T
where
    T: ?Sized + Multipeek,
{
    fn advance_peek(&mut self) -> Option<&Self::Item> {
        (**self).advance_peek()
    }

    fn reset_peek(&mut self) {
        (**self).reset_peek();
    }
}

impl<T> Multipeek for Box<T>
where
    T: ?Sized + Multipeek,
{
    fn advance_peek(&mut self) -> Option<&Self::Item> {
        (**self).advance_peek()
    }

    fn reset_peek(&mut self) {
        (**self).reset_peek();
    }
}

/// A cursor for working with `Multipeek` iterators.
///
/// Calling `MultipeekCursor::peek_next()` will advance the peek position
/// and dropping the cursor will automatically reset the position.
#[derive(Debug)]
pub struct MultipeekCursor<'a, I: Multipeek + ?Sized> {
    parent: &'a mut I,
}

impl<I> Drop for MultipeekCursor<'_, I>
where
    I: Multipeek + ?Sized,
{
    fn drop(&mut self) {
        self.parent.reset_peek();
    }
}

impl<I> MultipeekCursor<'_, I>
where
    I: Multipeek + ?Sized,
{
    /// Peek at another item to be yielded later.
    ///
    /// # Example
    /// ```no_run
    /// use conch_parser::iter::Multipeek;
    ///
    /// # struct Dummy<T>(Vec<T>);
    /// # impl<T> Iterator for Dummy<T> {
    /// #   type Item = T;
    /// #   fn next(&mut self) -> Option<Self::Item> {
    /// #     unimplemented!()
    /// #   }
    /// # }
    /// # impl<T> Multipeek for Dummy<T> {
    /// #   fn advance_peek(&mut self) -> Option<&Self::Item> {
    /// #     unimplemented!()
    /// #   }
    /// #   fn reset_peek(&mut self) {
    /// #     unimplemented!()
    /// #   }
    /// # }
    /// fn make_multipeek<T>(v: Vec<T>) -> impl Multipeek<Item = T> {
    ///   // ...
    /// #  Dummy(v)
    /// }
    ///
    /// let mut iter = make_multipeek(vec![1usize, 2, 3]);
    ///
    /// let mut peeker = iter.multipeek();
    /// assert_eq!(Some(&1), peeker.peek_next());
    /// assert_eq!(Some(&2), peeker.peek_next());
    /// assert_eq!(Some(&3), peeker.peek_next());
    /// assert_eq!(None, peeker.peek_next());
    /// drop(peeker);
    ///
    /// let mut peeker = iter.multipeek();
    /// assert_eq!(Some(&1), peeker.peek_next());
    /// assert_eq!(Some(&2), peeker.peek_next());
    /// drop(peeker);
    ///
    /// let mut peeker = iter.multipeek();
    /// assert_eq!(Some(&1), peeker.peek_next());
    /// drop(peeker);
    /// ```
    pub fn peek_next(&mut self) -> Option<&I::Item> {
        self.parent.advance_peek()
    }
}
