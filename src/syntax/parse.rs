//! The definition of a parser (and related methods) for the shell language.

use self::ErrorKind::*;
use syntax::ast;
use syntax::token::Token;
use syntax::token::Token::*;

/// An alias over `parse::Error` to avoid writing it out each time.
pub type Result<T> = ::std::result::Result<T, Error>;

/// Specifies the exact error that occured during parsing.
#[derive(Debug)]
pub enum ErrorKind {
    /// Encountered a token not appropriate for the current context.
    Unexpected(Token),
    /// Encountered the end of input while expecting additional tokens.
    UnexpectedEOF,
}

/// The error type which is returned from parsing shell commands.
#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
    line: u64,
}

impl Error {
    /// Returns the corresponding `ErrorKind` for this error.
    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }

    /// The line number of the input where the error occured.
    pub fn line(&self) -> u64 {
        self.line
    }
}

impl ::std::error::Error for Error {
    fn description(&self) -> &str {
        match self.kind {
            Unexpected(_) => "unexpected token found",
            UnexpectedEOF => "unexpected end of input",
        }
    }
}

impl ::std::fmt::Display for Error {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match self.kind {
            Unexpected(ref t) => write!(fmt, "found unexpected token '{}' on line {}", t, self.line),
            UnexpectedEOF => fmt.write_str("unexpected end of input"),
        }
    }
}

/// A Token iterator that keeps track of how many lines have been read.
struct TokenIter<I: Iterator<Item = Token>> {
    iter: ::std::iter::Peekable<I>,
    line: u64,
}

impl<I: Iterator<Item = Token>> Iterator for TokenIter<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        let next = match self.iter.next() {
            Some(t) => t,
            None => return None,
        };

        let newlines = match next {
            // Most of these should not have any newlines
            // embedded within them, but permitting external
            // tokenizers means we should sanity check anyway.
            Name(ref s)         |
            Comment(ref s)      |
            Literal(ref s)      |
            Whitespace(ref s)   |
            Assignment(ref s)   |
            SingleQuoted(ref s) => s.chars().filter(|&c| c == '\n').count() as u64,

            Newline => 1,
            _ => 0,
        };

        self.line += newlines;
        Some(next)
    }
}

impl<I: Iterator<Item = Token>> TokenIter<I> {
    /// Creates a new TokenIter from another Token iterator.
    fn new(iter: I) -> TokenIter<I> {
        TokenIter { iter: iter.peekable(), line: 1 }
    }

    /// Allows the caller to peek at the next token without consuming it.
    #[inline]
    fn peek(&mut self) -> Option<&Token> {
        self.iter.peek()
    }
}

/// A parser for the shell language.
pub struct Parser<I: Iterator<Item = Token>> {
    iter: TokenIter<I>,
}

impl<T: Iterator<Item = Token>> Iterator for Parser<T> {
    type Item = ast::Command;

    fn next(&mut self) -> Option<Self::Item> {
        self.complete_command().unwrap()
    }
}

impl<T: Iterator<Item = Token>> Parser<T> {
    /// Creates a new Parser from a Token iterator.
    pub fn new(t: T) -> Parser<T> {
        Parser { iter: TokenIter::new(t) }
    }

    pub fn complete_command(&mut self) -> Result<Option<ast::Command>> {
        loop {
            match self.iter.peek() {
                Some(&Newline)       |
                Some(&Comment(_))    |
                Some(&Whitespace(_)) => { self.iter.next(); },
                _ => break,
            }
        }

        let cmd = match self.iter.peek() {
            Some(_) => Some(try!(self.and_or())),
            None => None,
        };

        Ok(cmd)
    }

    /// Parses compound AND/OR commands.
    ///
    /// Commands are left associative. For example "foo || bar && baz"
    /// parses to And(Or(foo, bar), baz).
    pub fn and_or(&mut self) -> Result<ast::Command> {
        let mut cmd = try!(self.pipeline());

        loop {
            self.linebreak();

            match self.iter.peek() {
                Some(&OrIf)  |
                Some(&AndIf) => {},
                _ => break,
            }


            let ty = self.iter.next().unwrap();
            self.linebreak();
            let boxed = Box::new(cmd);
            let next = Box::new(try!(self.pipeline()));

            cmd = match ty {
                AndIf => ast::Command::And(boxed, next),
                OrIf  => ast::Command::Or(boxed, next),
                _ => unreachable!(),
            };
        }

        Ok(cmd)
    }

    /// Parses either a single command or a pipeline of commands.
    ///
    /// For example: "[!] foo [| bar [| ...]]".
    pub fn pipeline(&mut self) -> Result<ast::Command> {
        let bang = match self.iter.peek() {
            Some(&Bang) => { self.iter.next(); true }
            _ => false,
        };

        let mut cmds = Vec::new();

        loop {
            cmds.push(try!(self.command()));

            if let Some(&Pipe) = self.iter.peek() {
                self.iter.next();
                self.linebreak();
            } else {
                break;
            }
        }

        // Command::Pipe is the only AST node which allows for a status
        // negation, so we are forced to use it even if we have a single
        // command. Otherwise there is no need to wrap it further.
        if cmds.len() == 1 && !bang {
            Ok(cmds.pop().unwrap())
        } else {
            Ok(ast::Command::Pipe(bang, cmds))
        }
    }

    pub fn command(&mut self) -> Result<ast::Command> {
        self.simple_command()
    }

    /// Tries to parse a simple command, e.g. "cmd arg1 arg2".
    ///
    /// An error will be returned if not even a command name can be found, thus
    /// caller should be expecting the presense of a simple command with certainty.
    pub fn simple_command(&mut self) -> Result<ast::Command> {
        let cmd = match try!(self.word()) {
            Some(w) => w,
            None => return Err(Error {
                line: self.iter.line,
                kind: self.iter.peek().map_or(UnexpectedEOF, |t| Unexpected(t.clone())),
            }),
        };

        let mut args = Vec::new();
        while let Some(w) = try!(self.word()) {
            args.push(w);
        }

        Ok(ast::Command::Simple { cmd: cmd, args: args })
    }

    /// Parses a whitespace delimited chunk of text, honoring space quoting rules.
    ///
    /// Since there are a large number of possible tokens that constitute a word,
    /// (such as literals, paramters, variables, etc.) the caller may not know
    /// for sure whether to expect a word, thus an optional result is returned
    /// in the event that no word exists.
    ///
    /// Note that an error can still arise if partial tokens are present
    /// (e.g. malformed parameter).
    pub fn word(&mut self) -> Result<Option<ast::Word>> {
        self.skip_whitespace();

        let mut words = Vec::new();
        loop {
            match self.iter.peek() {
                Some(&Name(_))    |
                Some(&Literal(_)) => {},
                _ => break,
            }

            match self.iter.next() {
                Some(Name(s))    |
                Some(Literal(s)) => words.push(ast::Word::Literal(s)),
                _ => unreachable!(),
            }
        }

        let ret = if words.len() == 0 {
            None
        } else if words.len() == 1 {
            Some(words.pop().unwrap())
        } else {
            Some(ast::Word::Concat(words))
        };

        // Fastforward through any whitespace for sanity
        self.skip_whitespace();
        Ok(ret)
    }

    /// Skips over any encountered whitespace, however,
    /// any `Token::Newline`s or `Token::Comment`s are preserved.
    #[inline]
    pub fn skip_whitespace(&mut self) {
        while let Some(&Whitespace(_)) = self.iter.peek() {
            self.iter.next();
        }
    }

    /// Parses zero or more `Token::Newline`s, skipping whitespace and preserving `Token::Comment`s.
    pub fn linebreak(&mut self) -> Vec<ast::Newline> {
        let mut lines = Vec::new();

        loop {
            match self.iter.peek() {
                Some(&Newline)       |
                Some(&Comment(_))    |
                Some(&Whitespace(_)) => {},
                _ => break,
            }

            match self.iter.next() {
                Some(Newline) => lines.push(ast::Newline(None)),
                Some(Comment(s)) => lines.push(ast::Newline(Some(s))),
                Some(Whitespace(_)) => {},
                _ => unreachable!(),
            }
        }

        lines
    }
}

