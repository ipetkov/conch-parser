//! An module for easily iterating over a `Token` stream.

use std::collections::VecDeque;
use std::iter as std_iter;
use syntax::parse::SourcePos;
use syntax::token::Token;
use syntax::token::Token::*;

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

/// A Token iterator that keeps track of how many lines have been read.
#[derive(Debug)]
pub struct TokenIter<I: Iterator<Item = Token>> {
    /// The underlying token iterator being wrapped.
    iter: I,
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

impl<I: Iterator<Item = Token>> TokenIter<I> {
    /// Creates a new TokenIter from another Token iterator.
    pub fn new(iter: I) -> TokenIter<I> {
        TokenIter {
            iter: iter,
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

    /// Allows the caller to peek at the next token without consuming it.
    #[inline]
    pub fn peek(&mut self) -> Option<&Token> {
        let slice = self.peek_many(1);
        if slice.is_empty() {
            None
        } else {
            Some(slice[0])
        }
    }

    /// Allows the caller to peek multiple tokens at a time, returning a vector of borrowed tokens.
    pub fn peek_many(&mut self, amt: usize) -> Vec<&Token> {
        let mut tok_count = self.peek_buf.iter().filter(|t| t.is_tok()).count();

        // Fill up the peek buffer if needed
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

    /// Returns the iterator's current position in the source.
    #[inline]
    pub fn pos(&self) -> SourcePos { self.pos }

    /// Returns an iterator that yields tokens up to when a (closing) single quote
    /// is reached (assuming that the caller has reached the opening quote and
    /// wishes to continue up to but not including the closing quote).
    pub fn single_quoted(&mut self, pos: SourcePos) -> Balanced<I> {
        Balanced::new(self.by_ref(), Some(SingleQuote), true, pos)
    }

    /// Returns an iterator that yields tokens up to when a (closing) double quote
    /// is reached (assuming that the caller has reached the opening quote and
    /// wishes to continue up to but not including the closing quote).
    pub fn double_quoted(&mut self, pos: SourcePos) -> Balanced<I> {
        Balanced::new(self.by_ref(), Some(DoubleQuote), true, pos)
    }

    /// Returns an iterator that yields tokens up to when a (closing) backtick
    /// is reached (assuming that the caller has reached the opening backtick and
    /// wishes to continue up to but not including the closing backtick).
    pub fn backticked(&mut self, pos: SourcePos) -> Balanced<I> {
        Balanced::new(self.by_ref(), Some(Backtick), true, pos)
    }

    /// Returns an iterator that yields tokens up to when a (closing) backtick
    /// is reached (assuming that the caller has reached the opening backtick and
    /// wishes to continue up to but not including the closing backtick).
    /// Any backslashes followed by \, $, or ` are removed from the stream.
    pub fn backticked_remove_backslashes(&mut self, pos: SourcePos) -> BacktickBackslashRemover<I> {
        BacktickBackslashRemover::new(self.backticked(pos))
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

    /// Returns an iterator that yields at least one token, but continues to yield
    /// tokens until all matching cases of single/double quotes, backticks,
    /// ${ }, $( ), or ( ) are found.
    pub fn balanced(&mut self) -> Balanced<I> {
        let pos = self.pos();
        Balanced::new(self.by_ref(), None, false, pos)
    }
}

/// An iterator that yields at least one token, but continues to yield
/// tokens until all matching cases of single/double quotes, backticks,
/// ${ }, $( ), or ( ) are found.
pub struct Balanced<'a, I> where I: 'a + Iterator<Item=Token> {
    /// The underlying token iterator.
    iter: &'a mut TokenIter<I>,
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
    fn new(iter: &'a mut TokenIter<I>,
           delim: Option<Token>,
           skip_last_delimeter: bool,
           pos: SourcePos)
        -> Self
    {
        Balanced {
            escaped: None,
            stack: delim.map_or(Vec::new(), |d| vec!((d, pos))),
            done: false,
            skip_last_delimeter: skip_last_delimeter,
            pos: iter.pos(),
            iter: iter,
        }
    }

    /// Returns the iterator's current position in the source.
    #[inline]
    fn pos(&self) -> SourcePos { self.pos }
}

impl<'a, I: 'a + Iterator<Item=Token>> Iterator for Balanced<'a, I> {
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
            self.done |= self.stack.is_empty();
            self.pos = self.iter.pos();
            return if self.skip_last_delimeter && self.stack.is_empty() {
                None
            } else {
                ret
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

pub struct BacktickBackslashRemover<'a, I> where I: 'a + Iterator<Item=Token> {
    /// The underlying token iterator.
    iter: Balanced<'a, I>,
    /// Any token we had to peek after a backslash but haven't yielded yet.
    peeked: Option<Result<Token, UnmatchedError>>,
    /// Makes the iterator *fused* by yielding None forever after we are done.
    done: bool,
}

impl<'a, I: 'a + Iterator<Item=Token>> BacktickBackslashRemover<'a, I> {
    /// Constructs a new balanced backtick iterator which removes all backslashes
    /// from the stream thar are followed by \, $, or `.
    fn new(iter: Balanced<'a, I>) -> Self {
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
    fn create_token_iter(mut iter: Balanced<'a, I>)
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

impl<'a, I: 'a + Iterator<Item=Token>> Iterator for BacktickBackslashRemover<'a, I> {
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
