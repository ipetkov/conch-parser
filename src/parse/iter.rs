//! An module for easily iterating over a `Token` stream.

use std::collections::VecDeque;
use std::fmt;
use std::iter as std_iter;
use parse::SourcePos;
use token::Token;
use token::Token::*;

/// Indicates an error such that EOF was encountered while some unmatched
/// tokens were still pending. The error stores the unmatched token
/// and the position where it appears in the source.
#[derive(Debug)]
pub struct UnmatchedError(pub Token, pub SourcePos);

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

/// An iterator that can track its internal position in the stream.
pub trait PositionIterator: Iterator {
    /// Get the current position of the iterator.
    fn pos(&self) -> SourcePos;
}

impl<'a, T: PositionIterator> PositionIterator for &'a mut T {
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

impl<'a, T: PeekableIterator> PeekableIterator for &'a mut T {
    fn peek(&mut self) -> Option<&Self::Item> {
        (**self).peek()
    }
}

impl<I: Iterator> PeekableIterator for std_iter::Peekable<I> {
    fn peek(&mut self) -> Option<&Self::Item> {
        std_iter::Peekable::peek(self)
    }
}

/// A marker trait that unifies `PeekableIterator` and `PositionIterator`.
pub trait PeekablePositionIterator: PeekableIterator + PositionIterator {}
impl<T: PeekableIterator + PositionIterator> PeekablePositionIterator for T {}

/// A convenience trait for converting `Token` iterators into other sub-iterators.
pub trait TokenIterator: PeekablePositionIterator<Item = Token> + Sized {
    /// Returns an iterator that yields at least one token, but continues to yield
    /// tokens until all matching cases of single/double quotes, backticks,
    /// ${ }, $( ), or ( ) are found.
    fn balanced(&mut self) -> Balanced {
        let pos = self.pos();
        Balanced::new(self, None, pos)
    }

    /// Returns an iterator that yields tokens up to when a (closing) single quote
    /// is reached (assuming that the caller has reached the opening quote and
    /// wishes to continue up to but not including the closing quote).
    fn single_quoted(&mut self, pos: SourcePos) -> Balanced {
        Balanced::new(self, Some(SingleQuote), pos)
    }

    /// Returns an iterator that yields tokens up to when a (closing) double quote
    /// is reached (assuming that the caller has reached the opening quote and
    /// wishes to continue up to but not including the closing quote).
    fn double_quoted(&mut self, pos: SourcePos) -> Balanced {
        Balanced::new(self, Some(DoubleQuote), pos)
    }

    /// Returns an iterator that yields tokens up to when a (closing) backtick
    /// is reached (assuming that the caller has reached the opening backtick and
    /// wishes to continue up to but not including the closing backtick).
    fn backticked(&mut self, pos: SourcePos) -> Balanced {
        Balanced::new(self, Some(Backtick), pos)
    }

    /// Returns an iterator that yields tokens up to when a (closing) backtick
    /// is reached (assuming that the caller has reached the opening backtick and
    /// wishes to continue up to but not including the closing backtick).
    /// Any backslashes followed by \, $, or ` are removed from the stream.
    fn backticked_remove_backslashes(&mut self, pos: SourcePos) -> BacktickBackslashRemover {
        BacktickBackslashRemover::new(self.backticked(pos))
    }
}

/// A Token iterator that keeps track of how many lines have been read.
#[derive(Debug)]
pub struct TokenIter<I: Iterator<Item = Token>> {
    /// The underlying token iterator being wrapped. Iterator is fused to avoid
    /// inconsistent behavior when doing multiple `peek_many` operations.
    iter: std_iter::Fuse<I>,
    /// Any tokens that were previously yielded but to be consumed later, stored
    /// as a stack. Intersperced between the tokens are any changes to the current
    /// position that should be applied. This is useful for situations where the
    /// parser may have removed certain tokens (e.g. \ when unescaping), but we still
    /// want to keep track of token positions in the actual source.
    prev_buffered: Vec<TokenOrPos>,
    /// Any tokens that have been peeked from the underlying token iterator or from
    /// the previously buffered tokens, but which have not yet been yielded to the caller.
    peek_buf: VecDeque<TokenOrPos>,
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
        let slice = self.peek_many(1);
        if slice.is_empty() {
            None
        } else {
            Some(slice[0])
        }
    }
}

impl<I: Iterator<Item = Token>> Iterator for TokenIter<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        // Grab the next token to be yielded to the caller.
        let next = if self.peek_buf.is_empty() {
            if self.prev_buffered.is_empty() {
                self.iter.next().map(TokenOrPos::Tok)
            } else {
                self.prev_buffered.pop()
            }
        } else {
            self.peek_buf.pop_front()
        };

        // Make sure we update our current position before continuing.
        let ret = match next {
            Some(TokenOrPos::Tok(next)) => {
                self.pos.advance(&next);
                Some(next)
            },

            // The code below should ensure that any `Pos` variants trailing
            // after a `Tok` will be removed from the buffer. Any code that
            // stores a `Pos` in any of the buffers should ensure that there
            // is always a leading `Tok` variant ahead somewhere.
            Some(TokenOrPos::Pos(_)) => unreachable!(),
            None => None,
        };

        // Make sure we update our position according to any trailing `Pos` points.
        // The parser expects that polling our current position will give it the
        // position of the next token we will yield. If we perform this check right
        // before yielding the next token, the parser will believe that token appears
        // much earlier in the source than it actually does.
        loop {
            if let Some(&TokenOrPos::Pos(pos)) = self.peek_buf.front() {
                self.peek_buf.pop_front();
                self.pos = pos;
            } else if let Some(&TokenOrPos::Pos(pos)) = self.prev_buffered.last() {
                self.prev_buffered.pop();
                self.pos = pos;
            } else {
                break;
            }
        }

        ret
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (low_hint, hi) = self.iter.size_hint();
        let low = if self.prev_buffered.is_empty() && self.peek_buf.is_empty() {
            low_hint
        } else {
            self.prev_buffered.len() + self.peek_buf.len()
        };
        (low, hi)
    }
}

impl<I: Iterator<Item = Token>> TokenIterator for TokenIter<I> {}

impl<I: Iterator<Item = Token>> TokenIter<I> {
    /// Creates a new TokenIter from another Token iterator.
    pub fn new(iter: I) -> TokenIter<I> {
        TokenIter {
            iter: iter.fuse(),
            prev_buffered: Vec::new(),
            peek_buf: VecDeque::new(),
            pos: SourcePos::new(),
        }
    }

    /// Creates a new TokenIter from another Token iterator and an initial position.
    pub fn with_position(iter: I, pos: SourcePos) -> TokenIter<I> {
        let mut iter = TokenIter::new(iter);
        iter.pos = pos;
        iter
    }

    /// Allows the caller to peek multiple tokens at a time, returning a vector of borrowed tokens.
    pub fn peek_many(&mut self, amt: usize) -> Vec<&Token> {
        let mut tok_count = self.peek_buf.iter().filter(|t| t.is_tok()).count();

        // Fill up the peek buffer if needed
        // NB: this relies on self.iter being fused, other wise weird things may happen
        // between different calls to peek_many
        while tok_count < amt {
            let next = self.prev_buffered.pop().or_else(|| self.iter.next().map(TokenOrPos::Tok));
            match next {
                Some(t) => {
                    if t.is_tok() { tok_count += 1 }
                    self.peek_buf.push_back(t)
                },
                None => break,
            }
        }

        self.peek_buf.iter()
            .filter_map(|t| match *t {
                TokenOrPos::Tok(ref t) => Some(t),
                TokenOrPos::Pos(_) => None,
            })
            .take(amt)
            .collect()
    }

    /// Accepts a vector of tokens to be yielded completely before the inner
    /// iterator is advanced further. The provided `post_buf_pos` indicates
    /// what the iterator's position should be when the buffer of tokens is
    /// exhausted completely.
    pub fn backup_buffered_tokens(&mut self, mut buf: Vec<Token>, post_buf_pos: SourcePos) {
        self.prev_buffered.reserve(buf.len()+1);
        self.prev_buffered.push(TokenOrPos::Pos(self.pos));
        while let Some(t) = buf.pop() {
            self.prev_buffered.push(TokenOrPos::Tok(t));
        }
        self.pos = post_buf_pos;
    }

    /// Collects all tokens yielded by `TokenIter::backticked_remove_backslashes`
    /// and creates a `TokenIter` which will yield the collected tokens, and maintain
    /// the correct position of where each token appears in the original source,
    /// regardless of how many backslashes may have been removed since then.
    pub fn token_iter_from_backticked_with_removed_backslashes(&mut self, pos: SourcePos)
        -> Result<TokenIter<std_iter::Empty<Token>>, UnmatchedError>
    {
        BacktickBackslashRemover::create_token_iter(self.backticked(pos))
    }
}

/// A wrapper which allows treating `TokenIter<I>` and `TokenIter<Empty<_>>` as
/// the same thing, even though they are technically different types.
#[derive(Debug)]
pub enum TokenIterWrapper<I: Iterator<Item = Token>> {
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
    /// Delegates to `TokenIter::peek_many`.
    pub fn peek_many(&mut self, amt: usize) -> Vec<&Token> {
        match *self {
            TokenIterWrapper::Regular(ref mut inner) => inner.peek_many(amt),
            TokenIterWrapper::Buffered(ref mut inner) => inner.peek_many(amt),
        }
    }

    /// Delegates to `TokenIter::backup_buffered_tokens`.
    pub fn backup_buffered_tokens(&mut self, buf: Vec<Token>, post_buf_pos: SourcePos) {
        match *self {
            TokenIterWrapper::Regular(ref mut inner) => inner.backup_buffered_tokens(buf, post_buf_pos),
            TokenIterWrapper::Buffered(ref mut inner) => inner.backup_buffered_tokens(buf, post_buf_pos),
        }
    }

    /// Delegates to `TokenIter::token_iter_from_backticked_with_removed_backslashes`.
    pub fn token_iter_from_backticked_with_removed_backslashes(&mut self, pos: SourcePos)
        -> Result<TokenIter<std_iter::Empty<Token>>, UnmatchedError>
    {
        match *self {
            TokenIterWrapper::Regular(ref mut inner) =>
                inner.token_iter_from_backticked_with_removed_backslashes(pos),
            TokenIterWrapper::Buffered(ref mut inner) =>
                inner.token_iter_from_backticked_with_removed_backslashes(pos),
        }
    }
}

/// An iterator that yields at least one token, but continues to yield
/// tokens until all matching cases of single/double quotes, backticks,
/// ${ }, $( ), or ( ) are found.
pub struct Balanced<'a> {
    /// The underlying token iterator.
    iter: &'a mut PeekablePositionIterator<Item = Token>,
    /// Any token we had to peek after a backslash but haven't yielded yet,
    /// as well as the position after it.
    escaped: Option<(Token, SourcePos)>,
    /// A stack of pending unmatched tokens we still must encounter.
    stack: Vec<(Token, SourcePos)>,
    /// Indicates if we should yield the final, outermost delimeter.
    skip_last_delimeter: bool,
    /// Makes the iterator *fused* by yielding None forever after we are done.
    done: bool,
    /// The current position of the iterator.
    pos: SourcePos,
}

impl<'a> fmt::Debug for Balanced<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Balanced")
            .field("escaped", &self.escaped)
            .field("stack", &self.stack)
            .field("skip_last_delimeter", &self.skip_last_delimeter)
            .field("done", &self.done)
            .field("pos", &self.pos)
            .finish()
    }
}

impl<'a> Balanced<'a> {
    /// Constructs a new balanced iterator.
    ///
    /// If no delimeter is given, a single token will be yielded, unless the
    /// first found token is an opening one (e.g. "), making the iterator yield
    /// tokens until its matching delimeter is found (the matching delimeter *will*
    /// be consumed).
    ///
    /// If a delimeter is specified, tokens are yielded *up to* the delimeter,
    /// but the delimeter will be silently consumed.
    pub fn new(iter: &'a mut PeekablePositionIterator<Item = Token>,
           delim: Option<Token>,
           pos: SourcePos)
        -> Self
    {
        Balanced {
            escaped: None,
            skip_last_delimeter: delim.is_some(),
            stack: delim.map_or(Vec::new(), |d| vec!((d, pos))),
            done: false,
            pos: iter.pos(),
            iter: iter,
        }
    }
}

impl<'a> PositionIterator for Balanced<'a> {
    fn pos(&self) -> SourcePos {
        self.pos
    }
}

impl<'a> Iterator for Balanced<'a> {
    type Item = Result<Token, UnmatchedError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((tok, pos)) = self.escaped.take() {
            self.pos = pos;
            return Some(Ok(tok));
        } else if self.done {
            return None;
        }

        if self.stack.last().map(|t| &t.0) == self.iter.peek() {
            let ret = self.iter.next().map(Ok);
            self.stack.pop();
            let stack_empty = self.stack.is_empty();
            self.done |= stack_empty;
            self.pos = self.iter.pos();
            if self.skip_last_delimeter && stack_empty {
                return None;
            } else {
                return ret;
            };
        }

        // Tokens between single quotes have no special meaning
        // so we should make sure we don't treat anything specially.
        if let Some(&(SingleQuote, pos)) = self.stack.last() {
            let ret = match self.iter.next() {
                // Closing SingleQuote should have been captured above
                Some(t) => Some(Ok(t)),
                // Make sure we indicate errors on missing closing quotes
                None => Some(Err(UnmatchedError(SingleQuote, pos))),
            };

            self.pos = self.iter.pos();
            return ret;
        }

        let cur_pos = self.iter.pos();
        let ret = match self.iter.next() {
            Some(Backslash) => {
                // Make sure that we indicate our position as before the escaped token,
                // and NOT as the underlying iterator's position, which will indicate the
                // position AFTER the escaped token (which we are buffering ourselves)
                self.pos = self.iter.pos();

                debug_assert_eq!(self.escaped, None);
                self.escaped = self.iter.next().map(|t| (t, self.iter.pos()));
                // Make sure we stop yielding tokens after the stored escaped token
                // otherwise we risk consuming one token too many!
                self.done |= self.stack.is_empty();
                return Some(Ok(Backslash));
            },

            Some(Backtick) => {
                self.stack.push((Backtick, cur_pos));
                Some(Ok(Backtick))
            },

            Some(SingleQuote) => {
                if self.stack.last().map(|t| &t.0) != Some(&DoubleQuote) {
                    self.stack.push((SingleQuote, cur_pos));
                }
                Some(Ok(SingleQuote))
            },

            Some(DoubleQuote) => {
                self.stack.push((DoubleQuote, cur_pos));
                Some(Ok(DoubleQuote))
            },

            Some(ParenOpen) => {
                self.stack.push((ParenClose, cur_pos));
                Some(Ok(ParenOpen))
            },

            Some(Dollar) => {
                let cur_pos = self.iter.pos(); // Want the pos of curly or paren, not $ here
                match self.iter.peek() {
                    Some(&CurlyOpen) => self.stack.push((CurlyClose, cur_pos)),
                    Some(&ParenOpen) => {}, // Already handled by paren case above

                    // We have nothing further to match
                    _ => { self.done |= self.stack.is_empty(); },
                }
                Some(Ok(Dollar))
            },

            Some(t) => {
                // If we aren't looking for any more delimeters we should only
                // consume a single token (since its balanced by nature)
                self.done |= self.stack.is_empty();
                Some(Ok(t))
            },

            None => match self.stack.pop() {
                // Its okay to hit EOF if everything is balanced so far
                None => { self.done = true; None },
                // But its not okay otherwise
                Some((ParenClose, pos)) => Some(Err(UnmatchedError(ParenOpen, pos))),
                Some((CurlyClose, pos)) => Some(Err(UnmatchedError(CurlyOpen, pos))),
                Some((delim, pos))      => Some(Err(UnmatchedError(delim, pos))),
            },
        };

        self.pos = self.iter.pos();
        ret
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // Our best guess is as good as the internal token iterator's...
        self.iter.size_hint()
    }

}

/// A `Balanced` backtick `Token` iterator which removes all backslashes
/// from the stream that are followed by \, $, or `.
#[derive(Debug)]
pub struct BacktickBackslashRemover<'a> {
    /// The underlying token iterator.
    iter: Balanced<'a>,
    peeked: Option<Result<Token, UnmatchedError>>,
    /// Makes the iterator *fused* by yielding None forever after we are done.
    done: bool,
}

impl<'a> BacktickBackslashRemover<'a> {
    /// Constructs a new balanced backtick iterator which removes all backslashes
    /// from the stream that are followed by \, $, or `.
    pub fn new(iter: Balanced<'a>) -> Self {
        BacktickBackslashRemover {
            iter: iter,
            peeked: None,
            done: false,
        }
    }

    /// Collects all tokens yielded by `TokenIter::backticked_remove_backslashes`
    /// and creates a `TokenIter` which will yield the collected tokens, and maintain
    /// the correct position of where each token appears in the original source,
    /// regardless of how many backslashes may have been removed since then.
    fn create_token_iter(mut iter: Balanced<'a>)
        -> Result<TokenIter<std_iter::Empty<Token>>, UnmatchedError>
    {
        let mut all_chunks = Vec::new();
        let mut chunk_start = iter.pos();
        let mut chunk = Vec::new();

        loop {
            match iter.next() {
                Some(Ok(Backslash)) => {
                    let next_pos = iter.pos();
                    match iter.next() {
                        Some(Ok(tok@Dollar))    |
                        Some(Ok(tok@Backtick))  |
                        Some(Ok(tok@Backslash)) => {
                            all_chunks.push((chunk, chunk_start));
                            chunk_start = next_pos;
                            chunk = vec!(tok);
                        },

                        Some(tok) => {
                            chunk.push(Backslash);
                            chunk.push(try!(tok));
                        },

                        None => chunk.push(Backslash),
                    }
                },

                Some(tok) => chunk.push(try!(tok)),
                None => break,
            }
        }

        if !chunk.is_empty() {
            all_chunks.push((chunk, chunk_start));
        }

        let mut tok_iter = TokenIter::with_position(std_iter::empty(), iter.pos());
        while let Some((chunk, chunk_end)) = all_chunks.pop() {
            tok_iter.backup_buffered_tokens(chunk, chunk_end);
        }
        Ok(tok_iter)
    }
}

impl<'a> Iterator for BacktickBackslashRemover<'a> {
    type Item = Result<Token, UnmatchedError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.peeked.is_some() {
            return self.peeked.take();
        } else if self.done {
            return None;
        }

        match self.iter.next() {
            Some(Ok(Backslash)) => {
                match self.iter.next() {
                    ret@Some(Ok(Dollar))    |
                    ret@Some(Ok(Backtick))  |
                    ret@Some(Ok(Backslash)) => ret,

                    Some(t) => {
                        debug_assert!(self.peeked.is_none());
                        self.peeked = Some(t);
                        Some(Ok(Backslash))
                    },

                    None => {
                        self.done = true;
                        Some(Ok(Backslash))
                    },
                }
            },

            Some(t) => Some(t),
            None => {
                self.done = true;
                None
            },
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // The number of tokens we actually yield will never be
        // more than those of the underlying iterator, and will
        // probably be less, but this is a good enough estimate.
        self.iter.size_hint()
    }
}
