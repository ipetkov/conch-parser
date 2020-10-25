//! An module of utilities for working with `Token` iterators.

use crate::parse::SourcePos;

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
