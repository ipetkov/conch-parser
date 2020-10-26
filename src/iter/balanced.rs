use crate::error::UnmatchedError;
use crate::iter::{PeekablePositionIterator, PositionIterator};
use crate::parse::SourcePos;
use crate::token::Token;

/// An iterator that yields at least one token, but continues to yield
/// tokens until all matching cases of single/double quotes, backticks,
/// `${ }`, `$( )`, or `( )` are found.
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub struct Balanced<I> {
    /// The underlying token iterator.
    iter: I,
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

impl<I> Balanced<I>
where
    I: PeekablePositionIterator<Item = Token>,
{
    /// Constructs a new balanced iterator.
    ///
    /// If no delimeter is given, a single token will be yielded, unless the
    /// first found token is an opening one (e.g. "), making the iterator yield
    /// tokens until its matching delimeter is found (the matching delimeter *will*
    /// be consumed).
    ///
    /// If a delimeter (and its position) is specified, tokens are yielded *up to*
    /// the delimeter, but the delimeter will be silently consumed.
    fn new(mut iter: I, opening_token: Option<Token>) -> Self {
        let mut stack = Vec::new();

        let skip_last_delimeter = match opening_token {
            None => false,
            Some(t) => {
                let tok_pos = iter.pos();
                let next = iter.next();
                if Some(&t) != next.as_ref() {
                    panic!("expected {:?} but got {:?}", t, next);
                }

                stack.push((t, tok_pos));
                true
            }
        };

        let pos = iter.pos();

        Self {
            iter,
            escaped: None,
            stack,
            skip_last_delimeter,
            done: false,
            pos,
        }
    }

    /// Returns an iterator that yields at least one token, but continues to yield
    /// tokens until all matching cases of single/double quotes, backticks,
    /// `${ }`, `$( )`, or `( )` are found.
    pub fn balanced(iter: I) -> Self {
        Self::new(iter, None)
    }

    /// Returns an iterator that yields tokens up to when a (closing) single quote
    /// is reached (assuming that the caller has reached the opening quote and
    /// wishes to continue up to but not including the closing quote).
    ///
    /// # Panics
    ///
    /// Panics if the next token of `iter` is not `'`. Caller should ensure
    /// a single quote token is available to consume.
    pub fn single_quoted(iter: I) -> Self {
        Self::new(iter, Some(Token::SingleQuote))
    }

    /// Returns an iterator that yields tokens up to when a (closing) double quote
    /// is reached (assuming that the caller has reached the opening quote and
    /// wishes to continue up to but not including the closing quote).
    ///
    /// # Panics
    ///
    /// Panics if the next token of `iter` is not `"`. Caller should ensure
    /// a double quote token is available to consume.
    pub fn double_quoted(iter: I) -> Self {
        Self::new(iter, Some(Token::DoubleQuote))
    }

    /// Returns an iterator that yields tokens up to when a (closing) backtick
    /// is reached (assuming that the caller has reached the opening backtick and
    /// wishes to continue up to but not including the closing backtick).
    ///
    /// # Panics
    ///
    /// Panics if the next token of `iter` is not `` ` ``. Caller should ensure
    /// a backtick token is available to consume.
    pub fn backticked(iter: I) -> Self {
        Self::new(iter, Some(Token::Backtick))
    }
}

impl<I> PositionIterator for Balanced<I>
where
    I: PeekablePositionIterator<Item = Token>,
{
    fn pos(&self) -> SourcePos {
        self.pos
    }
}

impl<I> Iterator for Balanced<I>
where
    I: PeekablePositionIterator<Item = Token>,
{
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
        if let Some(&(Token::SingleQuote, pos)) = self.stack.last() {
            let ret = match self.iter.next() {
                // Closing SingleQuote should have been captured above
                Some(t) => Some(Ok(t)),
                // Make sure we indicate errors on missing closing quotes
                None => Some(Err(UnmatchedError {
                    token: Token::SingleQuote,
                    pos,
                })),
            };

            self.pos = self.iter.pos();
            return ret;
        }

        let cur_pos = self.iter.pos();
        let ret = match self.iter.next() {
            Some(Token::Backslash) => {
                // Make sure that we indicate our position as before the escaped token,
                // and NOT as the underlying iterator's position, which will indicate the
                // position AFTER the escaped token (which we are buffering ourselves)
                self.pos = self.iter.pos();

                debug_assert_eq!(self.escaped, None);
                self.escaped = self.iter.next().map(|t| (t, self.iter.pos()));
                // Make sure we stop yielding tokens after the stored escaped token
                // otherwise we risk consuming one token too many!
                self.done |= self.stack.is_empty();
                return Some(Ok(Token::Backslash));
            }

            Some(Token::Backtick) => {
                self.stack.push((Token::Backtick, cur_pos));
                Some(Ok(Token::Backtick))
            }

            Some(Token::SingleQuote) => {
                let inside_doublequote = self
                    .stack
                    .last()
                    .map(|(t, _)| matches!(t, Token::DoubleQuote))
                    .unwrap_or(false);

                if !inside_doublequote {
                    self.stack.push((Token::SingleQuote, cur_pos));
                }

                Some(Ok(Token::SingleQuote))
            }

            Some(Token::DoubleQuote) => {
                self.stack.push((Token::DoubleQuote, cur_pos));
                Some(Ok(Token::DoubleQuote))
            }

            Some(Token::ParenOpen) => {
                self.stack.push((Token::ParenClose, cur_pos));
                Some(Ok(Token::ParenOpen))
            }

            Some(Token::Dollar) => {
                let cur_pos = self.iter.pos(); // Want the pos of curly or paren, not $ here
                match self.iter.peek() {
                    Some(&Token::CurlyOpen) => self.stack.push((Token::CurlyClose, cur_pos)),
                    Some(&Token::ParenOpen) => {} // Already handled by paren case above

                    // We have nothing further to match
                    _ => {
                        self.done |= self.stack.is_empty();
                    }
                }
                Some(Ok(Token::Dollar))
            }

            Some(t) => {
                // If we aren't looking for any more delimeters we should only
                // consume a single token (since its balanced by nature)
                self.done |= self.stack.is_empty();
                Some(Ok(t))
            }

            None => match self.stack.pop() {
                // Its okay to hit EOF if everything is balanced so far
                None => {
                    self.done = true;
                    None
                }
                // But its not okay otherwise
                Some((Token::ParenClose, pos)) => Some(Err(UnmatchedError {
                    token: Token::ParenOpen,
                    pos,
                })),
                Some((Token::CurlyClose, pos)) => Some(Err(UnmatchedError {
                    token: Token::CurlyOpen,
                    pos,
                })),
                Some((delim, pos)) => Some(Err(UnmatchedError { token: delim, pos })),
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
