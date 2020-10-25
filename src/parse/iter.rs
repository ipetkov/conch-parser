//! An module for easily iterating over a `Token` stream.

use crate::error::UnmatchedError;
use crate::iter::{
    BacktickBackslashRemover, Balanced, PeekableIterator, PeekablePositionIterator,
    PositionIterator,
};
use crate::parse::SourcePos;
use crate::token::Token;
use crate::token::Token::*;
use std::iter as std_iter;
use std::mem;


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

/// A convenience trait for converting `Token` iterators into other sub-iterators.
pub trait TokenIterator: Sized + PeekablePositionIterator<Item = Token> {
    /// Returns an iterator that yields at least one token, but continues to yield
    /// tokens until all matching cases of single/double quotes, backticks,
    /// `${ }`, `$( )`, or `( )` are found.
    fn balanced(&mut self) -> Balanced<&mut Self> {
        Balanced::balanced(self)
    }

    /// Returns an iterator that yields tokens up to when a (closing) single quote
    /// is reached (assuming that the caller has reached the opening quote and
    /// wishes to continue up to but not including the closing quote).
    fn single_quoted(&mut self, pos: SourcePos) -> Balanced<&mut Self> {
        Balanced::single_quoted(self, pos)
    }

    /// Returns an iterator that yields tokens up to when a (closing) double quote
    /// is reached (assuming that the caller has reached the opening quote and
    /// wishes to continue up to but not including the closing quote).
    fn double_quoted(&mut self, pos: SourcePos) -> Balanced<&mut Self> {
        Balanced::double_quoted(self, pos)
    }

    /// Returns an iterator that yields tokens up to when a (closing) backtick
    /// is reached (assuming that the caller has reached the opening backtick and
    /// wishes to continue up to but not including the closing backtick).
    fn backticked(&mut self, pos: SourcePos) -> Balanced<&mut Self> {
        Balanced::backticked(self, pos)
    }

    /// Returns an iterator that yields tokens up to when a (closing) backtick
    /// is reached (assuming that the caller has reached the opening backtick and
    /// wishes to continue up to but not including the closing backtick).
    /// from the stream that are followed by `\`, `$`, or `` ` ``.
    fn backticked_remove_backslashes(
        &mut self,
        pos: SourcePos,
    ) -> BacktickBackslashRemover<&mut Self> {
        BacktickBackslashRemover::new(self, pos)
    }
}

/// Convenience trait for `Token` iterators which could be "rewound" so that
/// they can yield tokens that were already pulled out of their stream.
trait RewindableTokenIterator {
    /// Rewind the iterator with the provided tokens. Vector should contain
    /// the tokens in the order they should be yielded.
    fn rewind(&mut self, tokens: Vec<TokenOrPos>);

    /// Grab the next token (or internal position) that should be buffered
    /// by the caller.
    fn next_token_or_pos(&mut self) -> Option<TokenOrPos>;
}

/// A Token iterator that keeps track of how many lines have been read.
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub struct TokenIter<I> {
    /// The underlying token iterator being wrapped. Iterator is fused to avoid
    /// inconsistent behavior when doing multiple peek ahead operations.
    iter: std_iter::Fuse<I>,
    /// Any tokens that were previously yielded but to be consumed later, stored
    /// as a stack. Intersperced between the tokens are any changes to the current
    /// position that should be applied. This is useful for situations where the
    /// parser may have removed certain tokens (e.g. \ when unescaping), but we still
    /// want to keep track of token positions in the actual source.
    prev_buffered: Vec<TokenOrPos>,
    /// The current position in the source that we have consumed up to
    pos: SourcePos,
}

impl<I: Iterator<Item = Token>> PositionIterator for TokenIter<I> {
    fn pos(&self) -> SourcePos {
        self.pos
    }
}

impl<I: Iterator<Item = Token>> PeekableIterator for TokenIter<I> {
    fn peek(&mut self) -> Option<&Self::Item> {
        // Peek the next token, then drop the wrapper to get the token pushed
        // back on our buffer. Not the clearest solution, but gets around
        // the borrow checker.
        let _ = self.multipeek().peek_next()?;

        if let Some(&TokenOrPos::Tok(ref t)) = self.prev_buffered.last() {
            Some(t)
        } else {
            unreachable!("unexpected state: peeking next token failed. This is a bug!")
        }
    }
}

impl<I: Iterator<Item = Token>> Iterator for TokenIter<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        let mut ret = None;
        loop {
            // Make sure we update our current position before continuing.
            match self.next_token_or_pos() {
                Some(TokenOrPos::Tok(next)) => {
                    self.pos.advance(&next);
                    ret = Some(next);
                    break;
                }

                Some(TokenOrPos::Pos(_)) => panic!("unexpected state. This is a bug!"),
                None => break,
            }
        }

        // Make sure we update our position according to any trailing `Pos` points.
        // The parser expects that polling our current position will give it the
        // position of the next token we will yield. If we perform this check right
        // before yielding the next token, the parser will believe that token appears
        // much earlier in the source than it actually does.
        self.updated_buffered_pos();
        ret
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (low_hint, hi) = self.iter.size_hint();
        let low = if self.prev_buffered.is_empty() {
            low_hint
        } else {
            self.prev_buffered.len()
        };
        (low, hi)
    }
}

impl<I: Iterator<Item = Token>> RewindableTokenIterator for TokenIter<I> {
    fn rewind(&mut self, tokens: Vec<TokenOrPos>) {
        self.buffer_tokens_and_positions_to_yield_first(tokens, None);
    }

    fn next_token_or_pos(&mut self) -> Option<TokenOrPos> {
        self.prev_buffered
            .pop()
            .or_else(|| self.iter.next().map(TokenOrPos::Tok))
    }
}

impl<I: Iterator<Item = Token>> TokenIterator for TokenIter<I> {}

impl<I: Iterator<Item = Token>> TokenIter<I> {
    /// Creates a new TokenIter from another Token iterator.
    pub fn new(iter: I) -> TokenIter<I> {
        TokenIter {
            iter: iter.fuse(),
            prev_buffered: Vec::new(),
            pos: SourcePos::new(),
        }
    }

    /// Creates a new TokenIter from another Token iterator and an initial position.
    pub fn with_position(iter: I, pos: SourcePos) -> TokenIter<I> {
        let mut iter = TokenIter::new(iter);
        iter.pos = pos;
        iter
    }

    /// Return a wrapper which allows for arbitrary look ahead. Dropping the
    /// wrapper will restore the internal stream back to what it was.
    pub fn multipeek(&mut self) -> Multipeek<'_> {
        Multipeek::new(self)
    }

    /// Update the current position based on any buffered state.
    ///
    /// This allows us to always correctly report the position of the next token
    /// we are about to yield.
    fn updated_buffered_pos(&mut self) {
        while let Some(&TokenOrPos::Pos(pos)) = self.prev_buffered.last() {
            self.prev_buffered.pop();
            self.pos = pos;
        }
    }

    /// Accepts a vector of tokens (and positions) to be yielded completely before the
    /// inner iterator is advanced further. The optional `buf_start` (if provided)
    /// indicates what the iterator's position should have been if we were to naturally
    /// yield the provided buffer.
    fn buffer_tokens_and_positions_to_yield_first(
        &mut self,
        mut tokens: Vec<TokenOrPos>,
        token_start: Option<SourcePos>,
    ) {
        self.prev_buffered.reserve(tokens.len() + 1);

        // Push the current position further up the stack since we want to
        // restore it before yielding any previously-peeked tokens.
        if token_start.is_some() {
            self.prev_buffered.push(TokenOrPos::Pos(self.pos));
        }

        // Buffer the newly provided tokens in reverse since we are using a stack
        tokens.reverse();
        self.prev_buffered.extend(tokens);

        // Set our position to what it should be as we yield the buffered tokens
        if let Some(p) = token_start {
            self.pos = p;
        }

        self.updated_buffered_pos();
    }

    /// Accepts a vector of tokens to be yielded completely before the inner
    /// iterator is advanced further. The provided `buf_start` indicates
    /// what the iterator's position should have been if we were to naturally
    /// yield the provided buffer.
    pub fn buffer_tokens_to_yield_first(&mut self, buf: Vec<Token>, buf_start: SourcePos) {
        let tokens = buf.into_iter().map(TokenOrPos::Tok).collect();
        self.buffer_tokens_and_positions_to_yield_first(tokens, Some(buf_start));
    }

    /// Collects all tokens yielded by `TokenIter::backticked_remove_backslashes`
    /// and creates a `TokenIter` which will yield the collected tokens, and maintain
    /// the correct position of where each token appears in the original source,
    /// regardless of how many backslashes may have been removed since then.
    pub fn token_iter_from_backticked_with_removed_backslashes(
        &mut self,
        pos: SourcePos,
    ) -> Result<TokenIter<std_iter::Empty<Token>>, UnmatchedError> {
        BacktickBackslashRemover::create_token_iter(self.backticked(pos))
    }
}

/// A wrapper for peeking arbitrary amounts into a `Token` stream.
/// Inspired by the `Multipeek` implementation in the `itertools` crate.
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
pub struct Multipeek<'a> {
    /// The underlying token iterator. This is pretty much just a `TokenIter`,
    /// but we use a trait object to avoid having a generic signature and
    /// make this wrapper more flexible.
    iter: &'a mut dyn RewindableTokenIterator,
    /// A buffer of values taken from the underlying iterator, in the order
    /// they were pulled.
    buf: Vec<TokenOrPos>,
}

impl<'a> Drop for Multipeek<'a> {
    fn drop(&mut self) {
        let tokens = mem::replace(&mut self.buf, Vec::new());
        self.iter.rewind(tokens);
    }
}

impl<'a> Multipeek<'a> {
    /// Wrap an iterator for arbitrary look-ahead.
    fn new(iter: &'a mut dyn RewindableTokenIterator) -> Self {
        Multipeek {
            iter,
            buf: Vec::new(),
        }
    }

    /// Public method for lazily peeking the next (unpeeked) value.
    /// Implemented as its own API instead of as an `Iterator` to avoid
    /// confusion with advancing the regular iterator.
    pub fn peek_next(&mut self) -> Option<&Token> {
        loop {
            match self.iter.next_token_or_pos() {
                Some(t) => {
                    let is_tok = t.is_tok();
                    self.buf.push(t);

                    if is_tok {
                        break;
                    }
                }
                None => return None,
            }
        }

        if let Some(&TokenOrPos::Tok(ref t)) = self.buf.last() {
            Some(t)
        } else {
            None
        }
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

impl<I: Iterator<Item = Token>> TokenIterator for TokenIterWrapper<I> {}

impl<I: Iterator<Item = Token>> TokenIterWrapper<I> {
    /// Return a wrapper which allows for arbitrary look ahead. Dropping the
    /// wrapper will restore the internal stream back to what it was.
    pub fn multipeek(&mut self) -> Multipeek<'_> {
        match *self {
            TokenIterWrapper::Regular(ref mut inner) => inner.multipeek(),
            TokenIterWrapper::Buffered(ref mut inner) => inner.multipeek(),
        }
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
        pos: SourcePos,
    ) -> Result<TokenIter<std_iter::Empty<Token>>, UnmatchedError> {
        match *self {
            TokenIterWrapper::Regular(ref mut inner) => {
                inner.token_iter_from_backticked_with_removed_backslashes(pos)
            }
            TokenIterWrapper::Buffered(ref mut inner) => {
                inner.token_iter_from_backticked_with_removed_backslashes(pos)
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
    use super::{PositionIterator, TokenIter, TokenOrPos};
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

        let mut tok_iter = TokenIter::new(std::iter::empty());

        let pos = src(4, 4, 4);

        tok_iter.buffer_tokens_and_positions_to_yield_first(
            vec![
                TokenOrPos::Pos(src(2, 2, 2)),
                TokenOrPos::Pos(src(3, 3, 3)),
                TokenOrPos::Pos(pos),
                TokenOrPos::Tok(Token::Newline),
            ],
            Some(src(1, 1, 1)),
        );

        assert_eq!(tok_iter.pos(), pos);
    }
}
