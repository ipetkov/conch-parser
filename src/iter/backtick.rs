use crate::error::UnmatchedError;
use crate::iter::{Balanced, PeekablePositionIterator};
use crate::parse::SourcePos;
use crate::token::Token;

/// A `Balanced` backtick `Token` iterator which removes all backslashes
/// from the stream that are followed by `\`, `$`, or `` ` ``.
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub struct BacktickBackslashRemover<I> {
    /// The underlying token iterator.
    iter: Balanced<I>,
    peeked: Option<Result<Token, UnmatchedError>>,
    /// Makes the iterator *fused* by yielding None forever after we are done.
    done: bool,
}

impl<I> BacktickBackslashRemover<I>
where
    I: PeekablePositionIterator<Item = Token>,
{
    /// Constructs a new balanced backtick iterator which removes all backslashes
    /// from the stream that are followed by `\`, `$`, or `` ` ``.
    pub fn new(iter: I, pos: SourcePos) -> Self {
        Self {
            iter: Balanced::backticked(iter, pos),
            peeked: None,
            done: false,
        }
    }
}

impl<I> std::iter::FusedIterator for BacktickBackslashRemover<I> where
    I: PeekablePositionIterator<Item = Token>
{
}

impl<I> Iterator for BacktickBackslashRemover<I>
where
    I: PeekablePositionIterator<Item = Token>,
{
    type Item = Result<Token, UnmatchedError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.peeked.is_some() {
            return self.peeked.take();
        } else if self.done {
            return None;
        }

        match self.iter.next() {
            Some(Ok(Token::Backslash)) => match self.iter.next() {
                ret @ Some(Ok(Token::Dollar))
                | ret @ Some(Ok(Token::Backtick))
                | ret @ Some(Ok(Token::Backslash)) => ret,

                Some(t) => {
                    debug_assert!(self.peeked.is_none());
                    self.peeked = Some(t);
                    Some(Ok(Token::Backslash))
                }

                None => {
                    self.done = true;
                    Some(Ok(Token::Backslash))
                }
            },

            Some(t) => Some(t),
            None => {
                self.done = true;
                None
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // The number of tokens we actually yield will never be
        // more than those of the underlying iterator, and will
        // probably be less, but this is a good enough estimate.
        self.iter.size_hint()
    }
}
