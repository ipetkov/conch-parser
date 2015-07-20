//! An module for easily iterating over a `Token` stream.

use syntax::parse::SourcePos;
use syntax::token::Token;
use syntax::token::Token::*;

/// Indicates an error such that EOF was encountered while some unmatched
/// tokens were still pending. The error stores the unmatched token
/// and the position where it appears in the source.
pub struct UnmatchedError(pub Token, pub SourcePos);

/// A Token iterator that keeps track of how many lines have been read.
pub struct TokenIter<I: Iterator<Item = Token>> {
    /// The underlying token iterator being wrapped.
    iter: I,
    /// Any tokens that were previously yielded but to be consumed later
    prev_buffered: Vec<Token>,
    /// Any tokens that have been peeked from the `iter` or `prev_buffered`
    /// but not yet consumed
    peek_buf: Vec<Token>,
    /// The current position in the source that we have consumed up to
    pos: SourcePos,
    /// The position in the source where we will be once `prev_buffered`
    /// is completely exhausted.
    post_buf_pos: Option<SourcePos>,
}

impl<I: Iterator<Item = Token>> Iterator for TokenIter<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        let next = if !self.peek_buf.is_empty() {
            self.peek_buf.remove(0)
        } else {
            match self.next_internal() {
                Some(t) => t,
                None => return None,
            }
        };

        self.pos.advance(&next);
        Some(next)
    }
}

impl<I: Iterator<Item = Token>> TokenIter<I> {
    /// Creates a new TokenIter from another Token iterator.
    pub fn new(iter: I) -> TokenIter<I> {
        TokenIter {
            iter: iter,
            prev_buffered: Vec::new(),
            peek_buf: Vec::new(),
            pos: SourcePos {
                byte: 0,
                line: 1,
                col: 1,
            },
            post_buf_pos: None,
        }
    }

    /// Allows the caller to peek at the next token without consuming it.
    #[inline]
    pub fn peek(&mut self) -> Option<&Token> {
        let slice = self.multipeek(1);
        if slice.is_empty() {
            None
        } else {
            Some(&slice[0])
        }
    }

    /// Allows the caller to peek several tokens at a time. All results will
    /// begin with the same token until iterator is advanced through `next`.
    /// Subsequent `next` operations on the iterator will be `O(n)`, so
    /// the caller should multipeek as few tokens as they absolutely need.
    pub fn multipeek(&mut self, amt: usize) -> &[Token] {
        // Fill up the peek buffer if needed
        while self.peek_buf.len() < amt {
            match self.next_internal() {
                Some(t) => self.peek_buf.push(t),
                None => break,
            }
        }

        let upper = ::std::cmp::min(amt, self.peek_buf.len());
        &self.peek_buf[0..upper]
    }

    /// Gives precedence to previously buffered tokens,
    /// then tokens yielded from the wrapped iterator.
    #[inline]
    pub fn next_internal(&mut self) -> Option<Token> {
        self.prev_buffered.pop().or_else(|| {
            self.post_buf_pos.take().and_then(|p| { self.pos = p; Some(()) });
            self.iter.next()
        })
    }

    /// Accepts a vector of tokens to be yielded completely before the inner
    /// iterator is advanced further. The provided `post_buf_pos` indicates
    /// what the iterator's position should be when the buffer of tokens is
    /// exhausted completely.
    pub fn backup_buffered_tokens(&mut self, mut buf: Vec<Token>, post_buf_pos: SourcePos) {
        debug_assert!(self.prev_buffered.is_empty());
        debug_assert_eq!(self.post_buf_pos, None);
        buf.shrink_to_fit();
        buf.reverse();
        self.prev_buffered = buf;
        self.post_buf_pos = Some(post_buf_pos)
    }

    /// Returns the iterator's current position in the source.
    #[inline]
    pub fn pos(&self) -> SourcePos { self.pos }

    /// Returns an iterator that yields tokens up to when a (closing) single quote
    /// is reached (assuming that the caller has reached the opening quote and
    /// wishes to continue up to but not including the closing quote).
    pub fn single_quoted<'a>(&'a mut self) -> Balanced<'a, I> {
        Balanced::new(self.by_ref(), Some(SingleQuote), true)
    }

    /// Returns an iterator that yields tokens up to when a (closing) double quote
    /// is reached (assuming that the caller has reached the opening quote and
    /// wishes to continue up to but not including the closing quote).
    pub fn double_quoted<'a>(&'a mut self) -> Balanced<'a, I> {
        Balanced::new(self.by_ref(), Some(DoubleQuote), true)
    }

    /// Returns an iterator that yields at least one token, but continues to yield
    /// tokens until all matching cases of single/double quotes, backticks,
    /// ${ }, $( ), or ( ) are found.
    pub fn balanced<'a>(&'a mut self) -> Balanced<'a, I> {
        Balanced::new(self.by_ref(), None, false)
    }
}

/// An iterator that yields at least one token, but continues to yield
/// tokens until all matching cases of single/double quotes, backticks,
/// ${ }, $( ), or ( ) are found.
pub struct Balanced<'a, I> where I: 'a + Iterator<Item=Token> {
    iter: &'a mut TokenIter<I>,
    escaped: Option<Token>,
    stack: Vec<(Token, SourcePos)>,
    skip_last_delimeter: bool,
    done: bool,
}

impl<'a, I: 'a + Iterator<Item=Token>> Balanced<'a, I> {
    /// Constructs a new balanced iterator.
    ///
    /// If no delimeter is given, a single token will be yielded, unless the
    /// first found token is an opening one (e.g. "), making the iterator yield
    /// tokens until its matching delimeter is found.
    ///
    /// The caller can also choose if the final delimeter (before the iterator
    /// stops yielding tokens completely) should be yielded at all through the
    /// `skip_last_delimeter` parameter.
    fn new(iter: &'a mut TokenIter<I>, delim: Option<Token>, skip_last_delimeter: bool) -> Self {
        Balanced {
            escaped: None,
            stack: delim.map_or(Vec::new(), |d| vec!((d, iter.pos()))),
            done: false,
            skip_last_delimeter: skip_last_delimeter,
            iter: iter,
        }
    }
}

impl<'a, I: 'a + Iterator<Item=Token>> Iterator for Balanced<'a, I> {
    type Item = Result<Token, UnmatchedError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.escaped.is_some() {
            return self.escaped.take().map(Ok);
        } else if self.done {
            return None;
        } else if self.stack.last().map(|t| &t.0) == self.iter.peek() {
            let ret = self.iter.next().map(Ok);
            self.stack.pop();
            self.done |= self.stack.is_empty();
            return if self.skip_last_delimeter && self.stack.is_empty() {
                None
            } else {
                ret
            };
        }

        // Tokens between single quotes have no special meaning
        // so we should make sure we don't treat anything specially.
        if let Some(&(SingleQuote, pos)) = self.stack.last() {
            return match self.iter.next() {
                // Closing SingleQuote should have been captured above
                Some(t) => Some(Ok(t)),
                // Make sure we indicate errors on missing closing quotes
                None => Some(Err(UnmatchedError(SingleQuote, pos))),
            }
        }

        let cur_pos = self.iter.pos();
        match self.iter.next() {
            Some(Backslash) => {
                debug_assert_eq!(self.escaped, None);
                self.escaped = self.iter.next();
                // Make sure we stop yielding tokens after the stored escaped token
                // otherwise we risk consuming one token too many!
                self.done |= self.stack.is_empty();
                Some(Ok(Backslash))
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
                Some((delim, pos)) => Some(Err(UnmatchedError(delim, pos))),
            },
        }
    }
}
