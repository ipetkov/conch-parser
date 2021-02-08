use crate::iter::{Multipeek, PeekableIterator, PositionIterator};
use crate::parse::SourcePos;
use crate::token::Token;
use std::iter::{FusedIterator, Iterator};

/// An iterator that yields up to (but not including) a specified token
/// from another iterator. Note that the delimter token will be pulled
/// from the underlying iterator, but it will not be yielded.
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub struct Delimited<'a, I: ?Sized> {
    iter: &'a mut I,
    delimiter: Token,
    done: bool,
    multipeek_done: bool,
}

impl<'a, I> Delimited<'a, I>
where
    I: ?Sized,
{
    /// Constructs a new delimited iterator.
    ///
    /// Tokens will be yielded from `iter` until `delimiter` is encountered,
    /// after which the iterator is fused and will never yield any more tokens.
    pub fn new(delimiter: Token, iter: &'a mut I) -> Self {
        Self {
            delimiter,
            iter,
            done: false,
            multipeek_done: false,
        }
    }
}

impl<I> PositionIterator for Delimited<'_, I>
where
    I: ?Sized + PositionIterator<Item = Token>,
{
    fn pos(&self) -> SourcePos {
        self.iter.pos()
    }
}

impl<I> PeekableIterator for Delimited<'_, I>
where
    I: ?Sized + Iterator<Item = Token> + PeekableIterator,
{
    fn peek(&mut self) -> Option<&Self::Item> {
        if self.done {
            return None
        };

        match self.iter.peek() {
            None => None,
            Some(t) if *t == self.delimiter => None,
            Some(t) => Some(t),
        }
    }
}

impl<I> FusedIterator for Delimited<'_, I> where I: ?Sized + Iterator<Item = Token> {}

impl<I> Iterator for Delimited<'_, I>
where
    I: ?Sized + Iterator<Item = Token>,
{
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        match self.iter.next() {
            Some(t) if t == self.delimiter => {
                self.done = true;
                None
            }
            Some(t) => Some(t),
            None => {
                self.done = true;
                None
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I> Multipeek for Delimited<'_, I>
where
    I: ?Sized + Multipeek<Item = Token>
{
    fn advance_peek(&mut self) -> Option<&Self::Item> {
        if self.done || self.multipeek_done {
            return None;
        }

        match self.iter.advance_peek() {
            Some(t) if *t == self.delimiter => {
                self.multipeek_done = true;
                None
            },
            Some(t) => Some(t),
            None => None,
        }
    }

    fn reset_peek(&mut self) {
        self.iter.reset_peek();
        self.multipeek_done = self.done;
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::iter::PositionIterator;
    use crate::parse::SourcePos;
    use crate::parse::iter::TokenIter;


    #[test]
    fn does_not_yield_or_peek_past_delimiter() {
        let mut tokens = TokenIter::new(vec![
            Token::Plus,
            Token::Dash,
            Token::CurlyClose,
            Token::Amp,
        ]);

        let mut iter = Delimited::new(Token::CurlyClose, &mut tokens);

        let mut pos = SourcePos::new();
        assert_eq!(pos, iter.pos());

        assert_eq!(Some(&Token::Plus), iter.peek());
        assert_eq!(Some(Token::Plus), iter.next());
        pos.advance(&Token::Plus);
        assert_eq!(pos, iter.pos());

        assert_eq!(Some(&Token::Dash), iter.peek());
        assert_eq!(Some(Token::Dash), iter.next());
        pos.advance(&Token::Dash);
        assert_eq!(pos, iter.pos());

        assert_eq!(None, iter.peek());
        assert_eq!(None, iter.next());
        pos.advance(&Token::CurlyClose);
        assert_eq!(pos, iter.pos());

        assert_eq!(None, iter.peek());
        assert_eq!(None, iter.next());
        assert_eq!(pos, iter.pos());

        assert_eq!(None, iter.peek());
        assert_eq!(None, iter.next());
        assert_eq!(pos, iter.pos());
    }

    #[test]
    fn does_not_multipeek_past_delimiter() {
        let mut tokens = TokenIter::new(vec![
            Token::Plus,
            Token::Dash,
            Token::CurlyClose,
            Token::Amp,
        ]);

        let mut iter = Delimited::new(Token::CurlyClose, &mut tokens);

        let mut mp = iter.multipeek();
        assert_eq!(Some(&Token::Plus), mp.peek_next());
        assert_eq!(Some(&Token::Dash), mp.peek_next());
        assert_eq!(None, mp.peek_next());
        assert_eq!(None, mp.peek_next());
        drop(mp);

        assert_eq!(Some(Token::Plus), iter.next());
        let mut mp = iter.multipeek();
        assert_eq!(Some(&Token::Dash), mp.peek_next());
        assert_eq!(None, mp.peek_next());
        assert_eq!(None, mp.peek_next());
        drop(mp);

        assert_eq!(Some(Token::Dash), iter.next());
        let mut mp = iter.multipeek();
        assert_eq!(None, mp.peek_next());
        assert_eq!(None, mp.peek_next());
        drop(mp);
    }
}
