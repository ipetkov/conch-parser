//! An module for easily iterating over a `Token` stream.

use crate::error::UnmatchedError;
use crate::iter::{
    BacktickBackslashRemover, Balanced, Multipeek, MultipeekCursor, PeekableIterator,
    PeekablePositionIterator, PositionIterator,
};
use crate::parse::SourcePos;
use crate::token::Token;
use crate::token::Token::*;
use std::collections::VecDeque;
use std::iter as std_iter;

/// An internal variant that indicates if a token should be yielded
/// or the current position updated to some value.
#[derive(Debug)]
enum TokenOrPos {
    /// A consumed token which should be yielded.
    Tok(Token),
    /// The current position should be updated to the contained value.
    Pos(SourcePos),
}

impl TokenOrPos {
    /// Returns `true` if `self` is a `Tok` value.
    #[inline]
    fn is_tok(&self) -> bool {
        match *self {
            TokenOrPos::Tok(_) => true,
            TokenOrPos::Pos(_) => false,
        }
    }
}

/// A Token iterator that keeps track of how many lines have been read.
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub struct TokenIter<I> {
    /// The underlying token iterator being wrapped. Iterator is fused to avoid
    /// inconsistent behavior when doing multiple peek ahead operations.
    iter: std_iter::Fuse<I>,
    /// The current position in the source that we have consumed up to
    pos: SourcePos,
    /// A buffer of tokens which we've peeked, and should be yielded next.
    peek_buf: VecDeque<TokenOrPos>,
    /// The current peek offset into our buffer.
    peek_idx: usize,
}

impl<I: Iterator<Item = Token>> PositionIterator for TokenIter<I> {
    fn pos(&self) -> SourcePos {
        self.pos
    }
}

impl<I: Iterator<Item = Token>> PeekableIterator for TokenIter<I> {
    fn peek(&mut self) -> Option<&Self::Item> {
        if self.peek_buf.is_empty() {
            let next = self.iter.next()?;
            self.peek_buf.push_back(TokenOrPos::Tok(next));
        }

        self.peek_buf.front().map(|t| match t {
            TokenOrPos::Tok(t) => t,
            TokenOrPos::Pos(_) => panic!("invalid peek state"),
        })
    }
}

impl<I: Iterator<Item = Token>> Iterator for TokenIter<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        self.reset_peek();

        let next = match self.peek_buf.pop_front() {
            Some(TokenOrPos::Tok(t)) => t,
            Some(TokenOrPos::Pos(_)) => panic!("invalid state"),
            None => self.iter.next()?,
        };

        self.pos.advance(&next);

        // Make sure we update our position according to any trailing `Pos` points.
        // The parser expects that polling our current position will give it the
        // position of the next token we will yield. If we perform this check right
        // before yielding the next token, the parser will believe that token appears
        // much earlier in the source than it actually does.
        while let Some(&TokenOrPos::Pos(pos)) = self.peek_buf.front() {
            self.peek_buf.pop_front();
            self.pos = pos;
        }

        Some(next)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lo, hi) = self.iter.size_hint();

        let buffered_tokens = self.peek_buf.iter().filter(|t| t.is_tok()).count();

        let lo = lo + buffered_tokens;
        let hi = hi.map(|hi| hi + buffered_tokens);

        (lo, hi)
    }
}

impl<I: Iterator<Item = Token>> Multipeek for TokenIter<I> {
    fn advance_peek(&mut self) -> Option<&Self::Item> {
        debug_assert!(
            self.peek_idx <= self.peek_buf.len(),
            "peek_idx ({}) must be <= len ({})",
            self.peek_idx,
            self.peek_buf.len()
        );

        while self.peek_idx < self.peek_buf.len() {
            if let Some(TokenOrPos::Tok(_)) = self.peek_buf.get(self.peek_idx) {
                break;
            }

            self.peek_idx += 1;
        }

        if self.peek_idx == self.peek_buf.len() {
            let next = self.iter.next()?;
            self.peek_buf.push_back(TokenOrPos::Tok(next));
        }

        let ret = match &self.peek_buf[self.peek_idx] {
            TokenOrPos::Tok(t) => Some(t),
            TokenOrPos::Pos(_) => unreachable!(),
        };

        self.peek_idx += 1;
        ret
    }

    fn reset_peek(&mut self) {
        self.peek_idx = 0;
    }
}

impl<I> TokenIter<I>
where
    I: Iterator<Item = Token>,
{
    /// Creates a new TokenIter from another Token iterator.
    pub fn new<II>(iter: II) -> Self
    where
        II: IntoIterator<IntoIter = I, Item = Token>,
    {
        Self {
            iter: iter.into_iter().fuse(),
            pos: SourcePos::new(),
            peek_buf: VecDeque::new(),
            peek_idx: 0,
        }
    }

    /// Creates a new TokenIter from another Token iterator and an initial position.
    pub fn with_position(iter: I, pos: SourcePos) -> TokenIter<I> {
        let mut iter = TokenIter::new(iter);
        iter.pos = pos;
        iter
    }

    /// Accepts a vector of tokens to be yielded completely before the inner
    /// iterator is advanced further. The provided `buf_start` indicates
    /// what the iterator's position should have been if we were to naturally
    /// yield the provided buffer.
    pub fn buffer_tokens_to_yield_first(&mut self, mut buf: Vec<Token>, buf_start: SourcePos) {
        self.reset_peek();

        if buf.is_empty() {
            return;
        }

        self.peek_buf.reserve(buf.len() + 1);

        self.peek_buf.push_front(TokenOrPos::Pos(self.pos));
        while let Some(t) = buf.pop() {
            self.peek_buf.push_front(TokenOrPos::Tok(t));
        }

        self.pos = buf_start;
    }

    /// Collects all tokens yielded by `TokenIter::backticked_remove_backslashes`
    /// and creates a `TokenIter` which will yield the collected tokens, and maintain
    /// the correct position of where each token appears in the original source,
    /// regardless of how many backslashes may have been removed since then.
    pub fn token_iter_from_backticked_with_removed_backslashes(
        &mut self,
    ) -> Result<TokenIter<std_iter::Empty<Token>>, UnmatchedError> {
        BacktickBackslashRemover::create_token_iter(Balanced::backticked(self))
    }
}

/// A wrapper which allows treating `TokenIter<I>` and `TokenIter<Empty<_>>` as
/// the same thing, even though they are technically different types.
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub enum TokenIterWrapper<I> {
    /// A `TokenIter` which holds an aribtrary `Iterator` over `Token`s.
    Regular(TokenIter<I>),
    /// A `TokenIter` which has all `Token`s buffered in memory, and thus
    /// has no underlying iterator.
    Buffered(TokenIter<std_iter::Empty<Token>>),
}

impl<I: Iterator<Item = Token>> PositionIterator for TokenIterWrapper<I> {
    fn pos(&self) -> SourcePos {
        match *self {
            TokenIterWrapper::Regular(ref inner) => inner.pos(),
            TokenIterWrapper::Buffered(ref inner) => inner.pos(),
        }
    }
}

impl<I: Iterator<Item = Token>> PeekableIterator for TokenIterWrapper<I> {
    fn peek(&mut self) -> Option<&Self::Item> {
        match *self {
            TokenIterWrapper::Regular(ref mut inner) => inner.peek(),
            TokenIterWrapper::Buffered(ref mut inner) => inner.peek(),
        }
    }
}

impl<I: Iterator<Item = Token>> Iterator for TokenIterWrapper<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        match *self {
            TokenIterWrapper::Regular(ref mut inner) => inner.next(),
            TokenIterWrapper::Buffered(ref mut inner) => inner.next(),
        }
    }
}

impl<I: Iterator<Item = Token>> Multipeek for TokenIterWrapper<I> {
    fn advance_peek(&mut self) -> Option<&Self::Item> {
        match self {
            TokenIterWrapper::Regular(ref mut inner) => inner.advance_peek(),
            TokenIterWrapper::Buffered(ref mut inner) => inner.advance_peek(),
        }
    }

    fn reset_peek(&mut self) {
        match self {
            TokenIterWrapper::Regular(ref mut inner) => inner.reset_peek(),
            TokenIterWrapper::Buffered(ref mut inner) => inner.reset_peek(),
        }
    }
}

impl<I: Iterator<Item = Token>> TokenIterWrapper<I> {
    /// Return a wrapper which allows for arbitrary look ahead. Dropping the
    /// wrapper will restore the internal stream back to what it was.
    pub fn multipeek(&mut self) -> MultipeekCursor<'_, Self> {
        Multipeek::multipeek(self)
    }

    /// Delegates to `TokenIter::buffer_tokens_to_yield_first`.
    pub fn buffer_tokens_to_yield_first(&mut self, buf: Vec<Token>, buf_start: SourcePos) {
        match *self {
            TokenIterWrapper::Regular(ref mut inner) => {
                inner.buffer_tokens_to_yield_first(buf, buf_start)
            }
            TokenIterWrapper::Buffered(ref mut inner) => {
                inner.buffer_tokens_to_yield_first(buf, buf_start)
            }
        }
    }

    /// Delegates to `TokenIter::token_iter_from_backticked_with_removed_backslashes`.
    pub fn token_iter_from_backticked_with_removed_backslashes(
        &mut self,
    ) -> Result<TokenIter<std_iter::Empty<Token>>, UnmatchedError> {
        match *self {
            TokenIterWrapper::Regular(ref mut inner) => {
                inner.token_iter_from_backticked_with_removed_backslashes()
            }
            TokenIterWrapper::Buffered(ref mut inner) => {
                inner.token_iter_from_backticked_with_removed_backslashes()
            }
        }
    }
}

impl<I: PeekablePositionIterator<Item = Token>> BacktickBackslashRemover<I> {
    /// Collects all tokens yielded by `TokenIter::backticked_remove_backslashes`
    /// and creates a `TokenIter` which will yield the collected tokens, and maintain
    /// the correct position of where each token appears in the original source,
    /// regardless of how many backslashes may have been removed since then.
    fn create_token_iter(
        mut iter: Balanced<I>,
    ) -> Result<TokenIter<std_iter::Empty<Token>>, UnmatchedError> {
        let mut all_chunks = Vec::new();
        let mut chunk_start = iter.pos();
        let mut chunk = Vec::new();

        loop {
            match iter.next() {
                Some(Ok(Backslash)) => {
                    let next_pos = iter.pos();
                    match iter.next() {
                        Some(Ok(tok @ Dollar))
                        | Some(Ok(tok @ Backtick))
                        | Some(Ok(tok @ Backslash)) => {
                            all_chunks.push((chunk, chunk_start));
                            chunk_start = next_pos;
                            chunk = vec![tok];
                        }

                        Some(tok) => {
                            chunk.push(Backslash);
                            chunk.push(tok?);
                        }

                        None => chunk.push(Backslash),
                    }
                }

                Some(tok) => chunk.push(tok?),
                None => break,
            }
        }

        if !chunk.is_empty() {
            all_chunks.push((chunk, chunk_start));
        }

        let mut tok_iter = TokenIter::with_position(std_iter::empty(), iter.pos());
        while let Some((chunk, chunk_end)) = all_chunks.pop() {
            tok_iter.buffer_tokens_to_yield_first(chunk, chunk_end);
        }
        Ok(tok_iter)
    }
}

#[cfg(test)]
mod tests {
    use super::{PositionIterator, TokenIter};
    use crate::iter::Multipeek;
    use crate::parse::SourcePos;
    use crate::token::Token;

    #[test]
    fn test_multipeek() {
        let tokens = vec![
            Token::ParenOpen,
            Token::Semi,
            Token::Dollar,
            Token::ParenClose,
        ];

        let mut tok_iter = TokenIter::new(tokens.clone().into_iter());
        {
            let mut multipeek = tok_iter.multipeek();
            let mut expected_peeked = tokens.iter();
            while let Some(t) = multipeek.peek_next() {
                assert_eq!(expected_peeked.next(), Some(t));
            }

            // Exhausted the expected stream
            assert_eq!(expected_peeked.next(), None);
        }

        // Original iterator still yields the expected values
        assert_eq!(tokens, tok_iter.collect::<Vec<_>>());
    }

    #[test]
    fn test_buffering_tokens_should_immediately_update_position() {
        fn src(byte: usize, line: usize, col: usize) -> SourcePos {
            SourcePos { byte, line, col }
        }

        let orig = src(0, 1, 1);
        let pos1 = src(3, 3, 3);
        let pos2 = src(4, 4, 4);

        let mut tok_iter = TokenIter::with_position(std::iter::empty(), orig);

        tok_iter.buffer_tokens_to_yield_first(vec![Token::Newline], pos1);
        tok_iter.buffer_tokens_to_yield_first(vec![Token::Semi, Token::Semi], pos2);

        assert_eq!(pos2, tok_iter.pos());
        let mut cur_pos = pos2;
        cur_pos.advance(&Token::Semi);
        assert_eq!(Some(Token::Semi), tok_iter.next());
        assert_eq!(cur_pos, tok_iter.pos());
        assert_eq!(Some(Token::Semi), tok_iter.next());
        assert_eq!(pos1, tok_iter.pos());
        assert_eq!(Some(Token::Newline), tok_iter.next());

        assert_eq!(orig, tok_iter.pos());
    }
}
