//! The definition of a parser (and related methods) for the shell language.

use std::error::Error;
use std::fmt;
use std::str::FromStr;
use syntax::ast;
use syntax::ast::builder::{self, Builder};
use syntax::token::Token;
use syntax::token::Token::*;

/// A parser which will use a default AST builder implementation,
/// yielding results in terms of types defined in the `ast` module.
pub type DefaultParser<I> = Parser<I, builder::DefaultBuilder>;

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct SourcePos {
    pub byte: u64,
    pub line: u64,
    pub col: u64,
}

/// The error type which is returned from parsing shell commands.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParseError<T: Error> {
    /// Encountered a word that could not be interpreted as a valid file descriptor.
    /// Stores the start and end position of the invalid word.
    BadFd(SourcePos, SourcePos),
    /// Encountered a `Token::Literal` where expecting a `Token::Name`.
    BadIdent(String, SourcePos),
    /// Encountered a bad token inside of `${...}` (or lack of a token).
    BadSubst(Option<Token>, SourcePos),
    /// Encountered EOF while looking for a match for the specified token.
    /// Stores position of opening token.
    Unmatched(Token, SourcePos),
    /// Encountered a token not appropriate for the current context.
    Unexpected(Token, SourcePos),
    /// Encountered the end of input while expecting additional tokens.
    UnexpectedEOF,
    /// An external error returned by the AST builder.
    External(T),
}

impl<T: Error> Error for ParseError<T> {
    fn description(&self) -> &str {
        match *self {
            ParseError::BadFd(..)       => "bad file descriptor found",
            ParseError::BadIdent(..)    => "bad identifier found",
            ParseError::BadSubst(..)    => "bad substitution found",
            ParseError::Unmatched(..)   => "unmatched token",
            ParseError::Unexpected(..)  => "unexpected token found",
            ParseError::UnexpectedEOF   => "unexpected end of input",
            ParseError::External(ref e) => e.description(),
        }
    }

    fn cause(&self) -> Option<&Error> {
        match *self {
            ParseError::BadFd(..)      |
            ParseError::BadIdent(..)   |
            ParseError::BadSubst(..)   |
            ParseError::Unmatched(..)  |
            ParseError::Unexpected(..) |
            ParseError::UnexpectedEOF => None,
            ParseError::External(ref e) => Some(e),
        }
    }
}

impl<T: Error> fmt::Display for ParseError<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ParseError::BadFd(ref start, ref end)  =>
                write!(fmt, "file descriptor found between lines {} - {} cannot possibly be a valid", start, end),
            ParseError::BadIdent(ref id, pos)      => write!(fmt, "not a valid identifier {}: {}", pos, id),
            ParseError::BadSubst(None, pos)        => write!(fmt, "bad substitution {}: empty body", pos),
            ParseError::BadSubst(Some(ref t), pos) => write!(fmt, "bad substitution {}: invalid token: {}", pos, t),
            ParseError::Unmatched(ref t, pos)      => write!(fmt, "unmatched `{}` starting on line {}", t, pos),
            ParseError::Unexpected(ref t, pos)     => write!(fmt, "found unexpected token on line {}: {}", pos, t),

            ParseError::UnexpectedEOF => fmt.write_str("unexpected end of input"),
            ParseError::External(ref e) => write!(fmt, "{}", e),
        }
    }
}

impl fmt::Display for SourcePos {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}:{}", self.line, self.col)
    }
}

impl<T: Error> ::std::convert::From<T> for ParseError<T> {
    fn from(err: T) -> ParseError<T> {
        ParseError::External(err)
    }
}

/// Used to indicate what kind of compound command could be parsed next.
enum CompoundCmdKeyword {
    For,
    Case,
    If,
    While,
    Until,
    Brace,
    Subshell,
}

/// A Token iterator that keeps track of how many lines have been read.
struct TokenIter<I: Iterator<Item = Token>> {
    iter: I,
    peek_buf: Vec<Token>,
    pos: SourcePos,
}

impl<I: Iterator<Item = Token>> Iterator for TokenIter<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        let next = if !self.peek_buf.is_empty() {
            self.peek_buf.remove(0)
        } else {
            match self.iter.next() {
                Some(t) => t,
                None => return None,
            }
        };

        let newlines = match next {
            // Most of these should not have any newlines
            // embedded within them, but permitting external
            // tokenizers means we should sanity check anyway.
            Name(ref s)       |
            Literal(ref s)    |
            Whitespace(ref s) |
            Assignment(ref s) => s.chars().filter(|&c| c == '\n').count() as u64,

            Newline => 1,
            _ => 0,
        };

        let tok_len = next.len() as u64;
        self.pos.byte = tok_len;
        self.pos.line += newlines;
        self.pos.col = if newlines == 0 { self.pos.col + tok_len } else { 0 };
        Some(next)
    }
}

impl<I: Iterator<Item = Token>> TokenIter<I> {
    /// Creates a new TokenIter from another Token iterator.
    fn new(iter: I) -> TokenIter<I> {
        TokenIter {
            iter: iter,
            peek_buf: Vec::new(),
            pos: SourcePos {
                byte: 0,
                line: 1,
                col: 1,
            }
        }
    }

    /// Allows the caller to peek at the next token without consuming it.
    #[inline]
    fn peek(&mut self) -> Option<&Token> {
        let slice = self.multipeek(1);
        if slice.is_empty() {
            None
        } else {
            Some(&slice[0])
        }
    }

    /// Allows the caller to peek several tokens at a time. All results will
    /// begin with the same token until iterator is advanced through `next`.
    fn multipeek(&mut self, amt: usize) -> &[Token] {
        // Fill up the peek buffer if needed
        while self.peek_buf.len() < amt {
            match self.iter.next() {
                Some(t) => self.peek_buf.push(t),
                None => break,
            }
        }

        let upper = ::std::cmp::min(amt, self.peek_buf.len());
        &self.peek_buf[0..upper]
    }
}

impl<I: Iterator<Item = Token>, B: Builder> Iterator for Parser<I, B> {
    type Item = B::Command;

    fn next(&mut self) -> Option<Self::Item> {
        match self.complete_command() {
            Ok(r) => r,
            Err(e) => panic!("error: {}", e),
        }
    }
}

/// A parser for the shell language. It will parse shell commands from a
/// stream of shell `Token`s, and pass them to an AST builder.
pub struct Parser<I: Iterator<Item = Token>, B: Builder> {
    iter: TokenIter<I>,
    builder: B,
}

impl<I: Iterator<Item = Token>, B: Builder + Default> Parser<I, B> {
    /// Creates a new Parser from a Token iterator.
    pub fn new(iter: I) -> Parser<I, B> {
        Parser::with_builder(iter, Default::default())
    }
}

impl<I: Iterator<Item = Token>, B: Builder> Parser<I, B> {
    /// Construct an `Unexpected` error using the given token. If `None` specified, the next
    /// token in the iterator will be used (or `UnexpectedEOF` if none left).
    fn make_unexpected_err(&mut self, tok: Option<Token>) -> ParseError<B::Err> {
        tok.or_else(|| self.iter.next())
           .map_or(ParseError::UnexpectedEOF, |t| ParseError::Unexpected(t, self.iter.pos))
    }

    /// Construct a `BadFd` error using the given start position of a word,
    /// indicating that the word cannot possibly respresent a valid file
    /// descriptor to be used with a redirection.
    fn make_bad_fd_err(&mut self, start: SourcePos) -> ParseError<B::Err> {
        ParseError::BadFd(start, self.iter.pos)
    }

    /// Construct a `BadIdent` error using the given string, indicating that the literal
    /// does not respresent a valid name.
    fn make_bad_ident_err(&mut self, s: String) -> ParseError<B::Err> {
        ParseError::BadIdent(s, self.iter.pos)
    }

    /// Construct a `BadSubst` error using the given offending token.
    fn make_bad_substitution_err(&mut self, tok: Option<Token>) -> ParseError<B::Err> {
        ParseError::BadSubst(tok, self.iter.pos)
    }

    /// Construct an `Unmatched` error using the given token.
    fn make_unmatched_err(&mut self, tok: Token, start: SourcePos) -> ParseError<B::Err> {
        ParseError::Unmatched(tok, start)
    }

    /// Creates a new Parser from a Token iterator and provided AST builder.
    pub fn with_builder(iter: I, builder: B) -> Parser<I, B> {
        Parser {
            iter: TokenIter::new(iter),
            builder: builder,
        }
    }

    /// Parses a single complete command.
    ///
    /// For example, `foo && bar; baz` will yield two complete
    /// commands: `And(foo, bar)`, and `Simple(baz)`.
    pub fn complete_command(&mut self) -> Result<Option<B::Command>, ParseError<B::Err>> {
        let pre_cmd_comments = self.linebreak();

        if self.iter.peek().is_none() {
            try!(self.builder.comments(pre_cmd_comments));
            return Ok(None);
        }

        let cmd = try!(self.and_or());

        let sep = match self.iter.peek() {
            Some(&Semi) => { self.iter.next(); builder::SeparatorKind::Semi },
            Some(&Amp)  => { self.iter.next(); builder::SeparatorKind::Amp },

            _ => if let Some(n) = self.newline() {
                builder::SeparatorKind::Newline(n)
            } else {
                builder::SeparatorKind::Other
            },
        };

        let post_cmd_comments = self.linebreak();
        Ok(Some(try!(self.builder.complete_command(pre_cmd_comments, cmd, sep, post_cmd_comments))))
    }

    /// Parses compound AND/OR commands.
    ///
    /// Commands are left associative. For example `foo || bar && baz`
    /// parses to `And(Or(foo, bar), baz)`.
    pub fn and_or(&mut self) -> Result<B::Command, ParseError<B::Err>> {
        let mut cmd = try!(self.pipeline());

        loop {
            self.skip_whitespace();
            let kind = match self.iter.peek() {
                Some(&OrIf)  => {
                    self.iter.next();
                    builder::AndOrKind::Or
                },

                Some(&AndIf) => {
                    self.iter.next();
                    builder::AndOrKind::And
                },

                _ => break,
            };

            let post_sep_comments = self.linebreak();
            let next = try!(self.pipeline());
            cmd = try!(self.builder.and_or(cmd, kind, post_sep_comments, next));
        }

        Ok(cmd)
    }

    /// Parses either a single command or a pipeline of commands.
    ///
    /// For example `[!] foo | bar`.
    pub fn pipeline(&mut self) -> Result<B::Command, ParseError<B::Err>> {
        self.skip_whitespace();

        let bang = match self.iter.peek() {
            Some(&Bang) => { self.iter.next(); true }
            _ => false,
        };

        let mut cmds = Vec::new();

        loop {
            // We've already passed an apropriate spot for !, so it
            // is an error if it appears before the start of a command.
            if let Some(&Bang) = self.iter.peek() {
                return Err(self.make_unexpected_err(None));
            }

            let cmd = try!(self.command());

            if let Some(&Pipe) = self.iter.peek() {
                self.iter.next();
                cmds.push((self.linebreak(), cmd));
            } else {
                cmds.push((Vec::new(), cmd));
                break;
            }
        }

        Ok(try!(self.builder.pipeline(bang, cmds)))
    }

    /// Parses any command which itself is not a pipeline or an AND/OR command.
    pub fn command(&mut self) -> Result<B::Command, ParseError<B::Err>> {
        if let Some(kw) = self.next_compound_command_type() {
            return self.compound_command_internal(Some(kw))
        }

        if self.peek_reserved_word(&["function"]).is_some() {
            return self.function_declaration();
        }

        match self.iter.multipeek(5) {
            [Name(_), ParenOpen, ParenClose, ..]                               |
            [Name(_), ParenOpen, Whitespace(_), ParenClose, ..]                |
            [Name(_), Whitespace(_), ParenOpen, ParenClose, ..]                |
            [Name(_), Whitespace(_), ParenOpen, Whitespace(_), ParenClose, ..] => self.function_declaration(),

            _ => self.simple_command(),
        }
    }

    /// Tries to parse a simple command, e.g. `cmd arg1 arg2 >redirect`.
    ///
    /// A valid command is expected to have at least an executable name, or a single
    /// variable assignment or redirection. Otherwise an error will be returned.
    pub fn simple_command(&mut self) -> Result<B::Command, ParseError<B::Err>> {
        let mut cmd: Option<B::Word> = None;
        let mut args = Vec::new();
        let mut vars = Vec::new();
        let mut io = Vec::new();

        loop {
            if let Some(&Assignment(_)) = self.iter.peek() {
                if let Some(Assignment(var)) = self.iter.next() {
                    let value = if let Some(&Whitespace(_)) = self.iter.peek() {
                        None
                    } else {
                        try!(self.word())
                    };
                    vars.push((var, value));
                } else {
                    unreachable!();
                }

                // Make sure we continue checking for assignments,
                // otherwise it they can be interpreted as literal words.
                continue;
            }

            // If we find a redirect we should keep checking for
            // more redirects or assignments. Otherwise we will either
            // run into the command name or the end of the simple command.
            let exec = match try!(self.redirect()) {
                Some(Ok(redirect)) => { io.push(redirect); continue; },
                Some(Err(w)) => w,
                None => break,
            };

            // Since there are no more assignments or redirects present
            // it must be the first real word, and thus the executable name.
            cmd = Some(exec);
            break;
        }

        // Now that all assignments are taken care of, any other occurances of `=` will be
        // treated as literals when we attempt to parse a word out.
        loop {
            match try!(self.redirect()) {
                Some(Ok(redirect)) => { io.push(redirect); continue; },
                Some(Err(w)) => if cmd.is_none() { cmd = Some(w); } else { args.push(w) },
                None => break,
            }
        }

        // "Blank" commands are only allowed if redirection occurs
        // or if there is some variable assignment
        if cmd.is_none() {
            debug_assert!(args.is_empty());
            if vars.is_empty() && io.is_empty() {
                try!(Err(self.make_unexpected_err(None)));
            }
        }

        Ok(try!(self.builder.simple_command(vars, cmd, args, io)))
    }

    /// Parses a continuous list of redirections and will error if any words
    /// that are not valid file descriptors are found. Essentially used for
    /// parsing redirection lists after a compound command like `while` or `if`.
    pub fn redirect_list(&mut self) -> Result<Vec<B::Redirect>, ParseError<B::Err>> {
        let mut list = Vec::new();
        loop {
            let start_pos = self.iter.pos;
            match try!(self.redirect()) {
                Some(Ok(io)) => list.push(io),
                Some(Err(_)) => return Err(self.make_bad_fd_err(start_pos)),
                None => break,
            }
        }

        Ok(list)
    }

    /// Parses a redirection token an any source file descriptor and
    /// path/destination descriptor as appropriate, e.g. `>out`, `1>& 2`, or `2>&-`.
    ///
    /// Since the source descriptor can be any arbitrarily complicated word,
    /// it makes it difficult to reliably peek forward whether a valid redirection
    /// exists without consuming anything. Thus this method may return a simple word
    /// if no redirection is found.
    ///
    /// Thus, unless a parse error is occured, the return value will be an optional
    /// redirect or word if either is found. In other words, `Ok(Some(Ok(redirect)))`
    /// will result if a redirect is found, `Ok(Some(Err(word)))` if a word is found,
    /// or `Ok(None)` if neither is found.
    pub fn redirect(&mut self) -> Result<Option<::std::result::Result<B::Redirect, B::Word>>, ParseError<B::Err>> {
        fn is_maybe_numeric<C>(word: &builder::WordKind<C>, escapes_allowed: bool) -> bool {
            match *word {
                builder::WordKind::Star     |
                builder::WordKind::Question |
                builder::WordKind::Tilde    => false,

                // Literals and single quotes can be statically checked
                // if they have non-numeric characters
                builder::WordKind::Literal(ref s) |
                builder::WordKind::SingleQuoted(ref s) => s.chars().all(|c| c.is_digit(10)),

                builder::WordKind::Escaped(ref s) => escapes_allowed && s.chars().all(|c| c.is_digit(10)),

                builder::WordKind::Concat(ref fragments) |
                builder::WordKind::DoubleQuoted(ref fragments) =>
                    fragments.iter().all(|f| is_maybe_numeric(f, escapes_allowed)),

                // These could end up evaluating to a numeric,
                // but we'll have to see at runtime.
                builder::WordKind::Param(_) |
                builder::WordKind::Subst(_) |
                builder::WordKind::CommandSubst(_) => true,
            }
        }

        let src_fd = match try!(self.word_preserve_trailing_whitespace_raw()) {
            None => None,
            Some(w) => if is_maybe_numeric(&w, false) {
                Some(try!(self.builder.word(w)))
            } else {
                return Ok(Some(Err(try!(self.builder.word(w)))))
            },
        };

        let redir_tok = match self.iter.peek() {
            Some(&Less)      |
            Some(&Great)     |
            Some(&DGreat)    |
            Some(&Clobber)   |
            Some(&LessAnd)   |
            Some(&GreatAnd)  |
            Some(&LessGreat) => self.iter.next().unwrap(),

            _ => match src_fd {
                Some(w) => return Ok(Some(Err(w))),
                None => return Ok(None),
            },
        };

        let path_start_pos = self.iter.pos;
        let (is_num, path) = match try!(self.word_preserve_trailing_whitespace_raw()) {
            Some(p) => (is_maybe_numeric(&p, true), p),
            None => return Err(self.make_unexpected_err(None)),
        };

        self.skip_whitespace();

        let close = match path {
            builder::WordKind::Literal(ref s) if s == "-" => true,
            _ => false,
        };

        let path = try!(self.builder.word(path));

        let redirect = match redir_tok {
            Less      => builder::RedirectKind::Read(src_fd, path),
            Great     => builder::RedirectKind::Write(src_fd, path),
            DGreat    => builder::RedirectKind::Append(src_fd, path),
            Clobber   => builder::RedirectKind::Clobber(src_fd, path),
            LessGreat => builder::RedirectKind::ReadWrite(src_fd, path),

            LessAnd   if close  => builder::RedirectKind::CloseRead(src_fd),
            GreatAnd  if close  => builder::RedirectKind::CloseWrite(src_fd),
            LessAnd   if is_num => builder::RedirectKind::DupRead(src_fd, path),
            GreatAnd  if is_num => builder::RedirectKind::DupWrite(src_fd, path),

            // Duplication fd is not valid
            LessAnd  |
            GreatAnd => return Err(self.make_bad_fd_err(path_start_pos)),

            _ => unreachable!(),
        };

        Ok(Some(Ok(try!(self.builder.redirect(redirect)))))
    }

    /// Parses a whitespace delimited chunk of text, honoring space quoting rules,
    /// and skipping leading and trailing whitespace.
    ///
    /// Since there are a large number of possible tokens that constitute a word,
    /// (such as literals, paramters, variables, etc.) the caller may not know
    /// for sure whether to expect a word, thus an optional result is returned
    /// in the event that no word exists.
    ///
    /// Note that an error can still arise if partial tokens are present
    /// (e.g. malformed parameter). Also note that any `Token::Assignment` tokens
    /// will be treated as literals, since assignments can only come before
    /// the command or arguments, and should be handled externally.
    pub fn word(&mut self) -> Result<Option<B::Word>, ParseError<B::Err>> {
        let ret = try!(self.word_preserve_trailing_whitespace());
        self.skip_whitespace();
        Ok(ret)
    }

    /// Identical to `Parser::word()` but preserves trailing whitespace after the word.
    pub fn word_preserve_trailing_whitespace(&mut self) -> Result<Option<B::Word>, ParseError<B::Err>> {
        let w = match try!(self.word_preserve_trailing_whitespace_raw()) {
            Some(w) => Some(try!(self.builder.word(w))),
            None => None,
        };
        Ok(w)
    }

    /// Identical to `Parser::word_preserve_trailing_whitespace()` but does
    /// not pass the result to the AST builder.
    fn word_preserve_trailing_whitespace_raw(&mut self)
        -> Result<Option<builder::WordKind<B::Command>>, ParseError<B::Err>>
    {
        self.word_raw(false)
    }

    /// Identical to `Parser::word_preserve_trailing_whitespace_raw()` but will
    /// stop at `}` if parsing a word/pattern in a parameter substitution.
    fn word_raw(&mut self, param_subst_mode: bool)
        -> Result<Option<builder::WordKind<B::Command>>, ParseError<B::Err>>
    {
        self.skip_whitespace();

        // Make sure we don't consume comments,
        // e.g. if a # is at the start of a word.
        if let Some(&Pound) = self.iter.peek() {
            // Comments aren't recognized when parsing
            // words in parameter substitutions
            if !param_subst_mode {
                return Ok(None);
            }
        }

        let mut words = Vec::new();
        loop {
            match self.iter.peek() {
                Some(&CurlyOpen)          |
                Some(&SingleQuote)        |
                Some(&DoubleQuote)        |
                Some(&Backtick)           |
                Some(&Pound)              |
                Some(&Star)               |
                Some(&Question)           |
                Some(&Tilde)              |
                Some(&Bang)               |
                Some(&Backslash)          |
                Some(&Percent)            |
                Some(&Assignment(_))      |
                Some(&Name(_))            |
                Some(&Literal(_))         => {},

                Some(&Dollar)             |
                Some(&ParamAt)            |
                Some(&ParamDash)          |
                Some(&ParamPositional(_)) => {
                    words.push(try!(self.parameter_raw()));
                    continue;
                },

                Some(&Newline)       |
                Some(&ParenOpen)     |
                Some(&ParenClose)    |
                Some(&Semi)          |
                Some(&Amp)           |
                Some(&Pipe)          |
                Some(&AndIf)         |
                Some(&OrIf)          |
                Some(&DSemi)         |
                Some(&Less)          |
                Some(&Great)         |
                Some(&DLess)         |
                Some(&DGreat)        |
                Some(&GreatAnd)      |
                Some(&LessAnd)       |
                Some(&DLessDash)     |
                Some(&Clobber)       |
                Some(&LessGreat)     |
                Some(&Whitespace(_)) => break,

                // When parsing parameter substitutions } *should* be a delimiter
                Some(&CurlyClose) => if param_subst_mode { break } else {},

                None => break,
            }

            let start_pos = self.iter.pos;
            let w = match self.iter.next().unwrap() {
                // Assignments are only treated as such if they occur beforea command is
                // found. Any "Assignments" afterward should be treated as literals.
                //
                // Unless we are explicitly parsing a brace group, `{` and `}` should
                // be treated as literals.
                //
                // Also, comments are only recognized where a Newline is valid, thus '#'
                // becomes a literal if it occurs in the middle of a word.
                tok@Bang          |
                tok@Pound         |
                tok@Percent       |
                tok@CurlyOpen     |
                tok@CurlyClose    |
                tok@Assignment(_) => builder::WordKind::Literal(tok.to_string()),

                Name(s)    |
                Literal(s) => builder::WordKind::Literal(s),

                Star     => builder::WordKind::Star,
                Question => builder::WordKind::Question,
                Tilde    => builder::WordKind::Tilde,

                Backslash => match self.iter.next() {
                    Some(Newline) => break, // escaped newlines become whitespace and a delimiter
                    Some(t) => builder::WordKind::Escaped(t.to_string()),
                    None => break, // Can't escape EOF, just ignore the slash
                },

                SingleQuote => {
                    let mut buf = String::new();
                    loop {
                        match self.iter.next() {
                            // Make sure we actually find the closing quote before EOF
                            Some(SingleQuote) => break,
                            Some(t) => buf.push_str(&t.to_string()),
                            None => return Err(self.make_unmatched_err(SingleQuote, start_pos)),
                        }
                    }

                    builder::WordKind::SingleQuoted(buf)
                },

                DoubleQuote => {
                    let mut words = Vec::new();
                    let mut buf = String::new();
                    loop {
                        // Make sure we don't consume any $ (or any specific parameter token)
                        // we find since the `parameter` method expects to consume them.
                        match self.iter.peek() {
                            Some(&Dollar)             |
                            Some(&ParamAt)            |
                            Some(&ParamDash)          |
                            Some(&ParamPositional(_)) => {
                                if !buf.is_empty() {
                                    words.push(builder::WordKind::Literal(buf));
                                    buf = String::new();
                                }
                                words.push(try!(self.parameter_raw()));
                                continue;
                            },

                            _ => {},
                        }

                        match self.iter.next() {
                            Some(DoubleQuote) => {
                                if !buf.is_empty() {
                                    words.push(builder::WordKind::Literal(buf));
                                }

                                break;
                            },

                            Some(Backtick) => unimplemented!(),

                            // Backslashes only escape a few tokens when double quoted
                            Some(Backslash) => match self.iter.peek() {
                                Some(&Dollar)      |
                                Some(&Backtick)    |
                                Some(&DoubleQuote) |
                                Some(&Backslash)   |
                                Some(&Newline)     => {
                                    if !buf.is_empty() {
                                        words.push(builder::WordKind::Literal(buf));
                                        buf = String::new();
                                    }
                                    words.push(builder::WordKind::Escaped(self.iter.next().unwrap().to_string()));
                                },

                                _ => buf.push_str(&Backslash.to_string()),
                            },

                            Some(Dollar) => unreachable!(), // Sanity
                            Some(t) => buf.push_str(&t.to_string()),
                            None => return Err(self.make_unmatched_err(DoubleQuote, start_pos)),
                        }
                    }

                    builder::WordKind::DoubleQuoted(words)
                },

                Backtick    => unimplemented!(),

                // Parameters should have been
                // handled while peeking above.
                Dollar             |
                ParamAt            |
                ParamDash          |
                ParamPositional(_) => unreachable!(),

                // All word delimiters should have
                // broken the loop while peeking above.
                Newline       |
                ParenOpen     |
                ParenClose    |
                Semi          |
                Amp           |
                Pipe          |
                AndIf         |
                OrIf          |
                DSemi         |
                Less          |
                Great         |
                DLess         |
                DGreat        |
                GreatAnd      |
                LessAnd       |
                DLessDash     |
                Clobber       |
                LessGreat     |
                Whitespace(_) => unreachable!(),
            };

            words.push(w);
        }

        let ret = if words.len() == 0 {
            None
        } else if words.len() == 1 {
            Some(words.pop().unwrap())
        } else {
            Some(builder::WordKind::Concat(words))
        };

        Ok(ret)
    }

    /// Parses a parameters such as `$$`, `$1`, `$foo`, etc, or
    /// parameter substitutions such as `$(cmd)`, `${param-word}`, etc.
    ///
    /// Since it is possible that a leading `$` is not followed by a valid
    /// parameter, the `$` should be treated as a literal. Thus this method
    /// returns an `Word`, which will capture both cases where a literal or
    /// parameter is parsed.
    pub fn parameter(&mut self) -> Result<B::Word, ParseError<B::Err>> {
        let param = try!(self.parameter_raw());
        Ok(try!(self.builder.word(param)))
    }

    /// Identical to `Parser::parameter()` but does not pass the result to the AST builder.
    fn parameter_raw(&mut self) -> Result<builder::WordKind<B::Command>, ParseError<B::Err>> {
        use syntax::ast::Parameter;
        use syntax::ast::builder::WordKind;
        use syntax::ast::builder::ParameterSubstitutionKind::*;

        match self.iter.next() {
            Some(ParamAt)            => return Ok(WordKind::Param(Parameter::At)),
            Some(ParamDash)          => return Ok(WordKind::Param(Parameter::Dash)),
            Some(ParamPositional(p)) => return Ok(WordKind::Param(Parameter::Positional(p as u32))),

            Some(Token::Dollar) => match self.iter.peek() {
                Some(&Star)      |
                Some(&Pound)     |
                Some(&Question)  |
                Some(&Dollar)    |
                Some(&Bang)      |
                Some(&Name(_))   |
                Some(&ParenOpen) |
                Some(&CurlyOpen) => {},
                _ => return Ok(WordKind::Literal(Dollar.to_string())),
            },

            t => return Err(self.make_unexpected_err(t)),
        }

        let start_pos = self.iter.pos;
        let param = match self.iter.next() {
            Some(Star)     => Parameter::Star,
            Some(Pound)    => Parameter::Pound,
            Some(Question) => Parameter::Question,
            Some(Dollar)   => Parameter::Dollar,
            Some(Bang)     => Parameter::Bang,
            Some(Name(n))  => Parameter::Var(n),

            Some(CurlyOpen) => {
                let param = if let Some(&Pound) = self.iter.peek() {
                    self.iter.next();
                    match self.iter.peek() {
                        Some(&Percent) => {
                            self.iter.next();
                            if let Some(&Percent) = self.iter.peek() {
                                self.iter.next();
                                Err(RemoveLargestSuffix(Parameter::Pound, try!(self.param_word())))
                            } else {
                                Err(RemoveSmallestSuffix(Parameter::Pound, try!(self.param_word())))
                            }
                        },

                        Some(&Pound) => {
                            self.iter.next();
                            if let Some(&Pound) = self.iter.peek() {
                                self.iter.next();
                                Err(RemoveLargestPrefix(Parameter::Pound, try!(self.param_word())))
                            } else {
                                match try!(self.param_word()) {
                                    w@Some(_) => Err(RemoveSmallestPrefix(Parameter::Pound, w)),
                                    None => Err(Len(Parameter::Pound)),
                                }
                            }
                        },

                        Some(&CurlyClose) => Ok(Parameter::Pound),
                        _ => Err(Len(try!(self.parameter_inner()))),
                    }
                } else {
                    let param = try!(self.parameter_inner());
                    if let Some(&Percent) = self.iter.peek() {
                        self.iter.next();
                        if let Some(&Percent) = self.iter.peek() {
                            self.iter.next();
                            Err(RemoveLargestSuffix(param, try!(self.param_word())))
                        } else {
                            Err(RemoveSmallestSuffix(param, try!(self.param_word())))
                        }
                    } else if let Some(&Pound) = self.iter.peek() {
                        self.iter.next();
                        if let Some(&Pound) = self.iter.peek() {
                            self.iter.next();
                            Err(RemoveLargestPrefix(param, try!(self.param_word())))
                        } else {
                            Err(RemoveSmallestPrefix(param, try!(self.param_word())))
                        }
                    } else {
                        Ok(param)
                    }
                };

                match self.iter.next() {
                    Some(CurlyClose) => match param {
                        Ok(param)  => param,
                        Err(subst) => return Ok(WordKind::Subst(subst)),
                    },
                    t => return Err(self.make_unexpected_err(t)),
                }
            },

            Some(ParenOpen) => {
                self.skip_whitespace();
                let cmds = if let Some(&ParenClose) = self.iter.peek() {
                    Vec::new()
                } else {
                    try!(self.command_list(&[], &[ParenClose]))
                };

                match self.iter.next() {
                    Some(ParenClose) => return Ok(WordKind::Subst(Command(cmds))),
                    Some(t) => return Err(self.make_unexpected_err(Some(t))),
                    None => return Err(self.make_unmatched_err(ParenOpen, start_pos)),
                }
            },

            t => return Err(self.make_unexpected_err(t)),
        };

        Ok(WordKind::Param(param))
    }

    /// Parses a valid parameter that can appear inside a set of curly braces.
    fn parameter_inner(&mut self) -> Result<ast::Parameter, ParseError<B::Err>> {
        use syntax::ast::Parameter;

        let param = match self.iter.next() {
            Some(Star)          => Parameter::Star,
            Some(Pound)         => Parameter::Pound,
            Some(Question)      => Parameter::Question,
            Some(Dollar)        => Parameter::Dollar,
            Some(Bang)          => Parameter::Bang,

            Some(Name(ref s)) | Some(Literal(ref s)) if s == "@" => Parameter::At,
            Some(Name(ref s)) | Some(Literal(ref s)) if s == "-" => Parameter::Dash,

            Some(Name(n)) => Parameter::Var(n),
            Some(Literal(s)) => match u32::from_str(&s) {
                Ok(n)  => Parameter::Positional(n),
                Err(_) => return Err(self.make_bad_substitution_err(Some(Literal(s)))),
            },

            t => return Err(self.make_bad_substitution_err(t)),
        };

        Ok(param)
    }

    /// Parses a word that can appear at the end of a parameter substitution.
    ///
    /// Words in parameter substitutions are slightly different than normal: they can
    /// contain whitespace and `}` tokens should delimit the word (whereas they are
    /// normally considered a literal).
    fn param_word(&mut self) -> Result<Option<Box<builder::WordKind<B::Command>>>, ParseError<B::Err>> {
        let mut words = Vec::new();
        loop {
            let space = self.capture_whitespace();
            let found = if space.is_empty() {
                false
            } else {
                words.reserve(space.len());
                for s in space { words.push(s) }
                true
            };

            match try!(self.word_raw(true)) {
                Some(builder::WordKind::Concat(cw)) => {
                    words.reserve(cw.len());
                    for w in cw { words.push(w) }
                },
                Some(w) => words.push(w),
                None => if !found { break },
            }
        }

        let ret = if words.is_empty() {
            None
        } else if words.len() == 1 {
            Some(words.pop().unwrap())
        } else {
            Some(builder::WordKind::Concat(words))
        };

        Ok(ret.map(Box::new))
    }

    /// Parses any number of sequential commands between the `do` and `done`
    /// reserved words. Each of the reserved words must be a literal token, and cannot be
    /// quoted or concatenated.
    pub fn do_group(&mut self) -> Result<Vec<B::Command>, ParseError<B::Err>> {
        let start_pos = self.iter.pos;
        try!(self.reserved_word(&["do"]));
        let result = try!(self.command_list(&["done"], &[]));
        if self.iter.peek() == None {
            return Err(self.make_unmatched_err(Literal(String::from("do")), start_pos));
        }
        try!(self.reserved_word(&["done"]));
        Ok(result)
    }

    /// Parses any number of sequential commands between balanced `{` and `}`
    /// reserved words. Each of the reserved words must be a literal token, and cannot be quoted.
    pub fn brace_group(&mut self) -> Result<Vec<B::Command>, ParseError<B::Err>> {
        // CurlyClose must be encountered as a stand alone word,
        // even though it is represented as its own token
        let start_pos = self.iter.pos;
        try!(self.reserved_token(&[CurlyOpen]));
        let cmds = try!(self.command_list(&[], &[CurlyClose]));
        if self.iter.peek() == None {
            return Err(self.make_unmatched_err(CurlyClose, start_pos));
        }
        try!(self.reserved_token(&[CurlyClose]));
        Ok(cmds)
    }

    /// Parses any number of sequential commands between balanced `(` and `)`.
    ///
    /// It is considered an error if no commands are present inside the subshell.
    pub fn subshell(&mut self) -> Result<Vec<B::Command>, ParseError<B::Err>> {
        let start_pos = self.iter.pos;
        match self.iter.next() {
            Some(ParenOpen) => {},
            t => return Err(self.make_unexpected_err(t)),
        }

        // Paren's are always special tokens, hence they aren't
        // reserved words, and thus the `command_list` method doesn't apply.
        let mut cmds = Vec::new();
        loop {
            if let Some(&ParenClose) = self.iter.peek() { break; }
            match try!(self.complete_command()) {
                Some(c) => cmds.push(c),
                None => break,
            }
        }

        match self.iter.next() {
            Some(ParenClose) if !cmds.is_empty() => Ok(cmds),
            Some(t) => Err(self.make_unexpected_err(Some(t))),
            None => Err(self.make_unmatched_err(ParenClose, start_pos)),
        }
    }

    /// Peeks at the next token (after skipping whitespace) to determine
    /// if (and which) compound command may follow.
    fn next_compound_command_type(&mut self) -> Option<CompoundCmdKeyword> {
        if let Some(&ParenOpen) = self.iter.peek() {
            Some(CompoundCmdKeyword::Subshell)
        } else if let Some(_) = self.peek_reserved_token(&[CurlyOpen]) {
            Some(CompoundCmdKeyword::Brace)
        } else {
            match self.peek_reserved_word(&["for", "case", "if", "while", "until"]) {
                Some("for")   => Some(CompoundCmdKeyword::For),
                Some("case")  => Some(CompoundCmdKeyword::Case),
                Some("if")    => Some(CompoundCmdKeyword::If),
                Some("while") => Some(CompoundCmdKeyword::While),
                Some("until") => Some(CompoundCmdKeyword::Until),
                _ => None,
            }
        }
    }

    /// Parses compound commands like `for`, `case`, `if`, `while`, `until`,
    /// brace groups, or subshells, including any redirection lists to be applied to them.
    pub fn compound_command(&mut self) -> Result<B::Command, ParseError<B::Err>> {
        self.compound_command_internal(None)
    }

    /// Slightly optimized version of `Parse::compound_command` that will not
    /// check an upcoming reserved word if the caller already knows the answer.
    fn compound_command_internal(&mut self, kw: Option<CompoundCmdKeyword>) -> Result<B::Command, ParseError<B::Err>> {
        let cmd = match kw.or_else(|| self.next_compound_command_type()) {
            Some(CompoundCmdKeyword::If) => {
                let (branches, els) = try!(self.if_command());
                let io = try!(self.redirect_list());
                try!(self.builder.if_command(branches, els, io))
            },

            Some(CompoundCmdKeyword::While) |
            Some(CompoundCmdKeyword::Until) => {
                let (until, guard, body) = try!(self.loop_command());
                let io = try!(self.redirect_list());
                try!(self.builder.loop_command(until, guard, body, io))
            },

            Some(CompoundCmdKeyword::For) => {
                let (var, post_var_comments, words, post_word_comments, body) = try!(self.for_command());
                let io = try!(self.redirect_list());
                try!(self.builder.for_command(var, post_var_comments, words, post_word_comments, body, io))
            },

            Some(CompoundCmdKeyword::Case) => {
                let (word, post_word_comments, branches, post_branch_comments) = try!(self.case_command());
                let io = try!(self.redirect_list());
                try!(self.builder.case_command(word, post_word_comments, branches, post_branch_comments, io))
            },

            Some(CompoundCmdKeyword::Brace) => {
                let cmds = try!(self.brace_group());
                let io = try!(self.redirect_list());
                try!(self.builder.brace_group(cmds, io))
            },

            Some(CompoundCmdKeyword::Subshell) => {
                let cmds = try!(self.subshell());
                let io = try!(self.redirect_list());
                try!(self.builder.subshell(cmds, io))
            },

            None => return Err(self.make_unexpected_err(None)),
        };

        Ok(cmd)
    }

    /// Parses loop commands like `while` and `until` but does not parse any
    /// redirections that may follow.
    ///
    /// Since they are compound commands (and can have redirections applied to
    /// the entire loop) this method returns the relevant parts of the loop command,
    /// without constructing an AST node, it so that the caller can do so with redirections.
    ///
    /// Return structure is `Result(loop_kind, guard_commands, body_commands)`.
    pub fn loop_command(&mut self) -> Result<(builder::LoopKind, Vec<B::Command>, Vec<B::Command>), ParseError<B::Err>> {
        let kind = match try!(self.reserved_word(&["while", "until"])) {
            "while" => builder::LoopKind::While,
            "until" => builder::LoopKind::Until,
            _ => unreachable!(),
        };
        let guard = try!(self.command_list(&["do"], &[]));
        Ok((kind, guard, try!(self.do_group())))
    }

    /// Parses a single `if` command but does not parse any redirections that may follow.
    ///
    /// Since `if` is a compound command (and can have redirections applied to it) this
    /// method returns the relevant parts of the `if` command, without constructing an
    /// AST node, it so that the caller can do so with redirections.
    ///
    /// Return structure is `Result( (condition, body)+, else_part )`.
    pub fn if_command(&mut self) -> Result<(
        Vec<(Vec<B::Command>, Vec<B::Command>)>,
        Option<Vec<B::Command>>), ParseError<B::Err>>
    {
        let start_pos = self.iter.pos;
        try!(self.reserved_word(&["if"]));

        let mut branches = Vec::new();
        loop {
            let guard = try!(self.command_list(&["then"], &[]));
            try!(self.reserved_word(&["then"]));

            let body = try!(self.command_list(&["elif", "else", "fi"], &[]));
            branches.push((guard, body));

            if self.iter.peek() == None {
                return Err(self.make_unmatched_err(Literal(String::from("if")), start_pos))
            }
            let els = match try!(self.reserved_word(&["elif", "else", "fi"])) {
                "elif" => continue,
                "else" => {
                    let els = try!(self.command_list(&["fi"], &[]));
                    if self.iter.peek() == None {
                        return Err(self.make_unmatched_err(Literal(String::from("if")), start_pos))
                    }
                    try!(self.reserved_word(&["fi"]));
                    Some(els)
                },
                "fi" => None,
                _ => unreachable!(),
            };

            return Ok((branches, els))
        }
    }

    /// Parses a single `for` command but does not parse any redirections that may follow.
    ///
    /// Since `for` is a compound command (and can have redirections applied to it) this
    /// method returns the relevant parts of the `for` command, without constructing an
    /// AST node, it so that the caller can do so with redirections.
    ///
    /// Return structure is `Result(var_name, comments_after_var, in_words, comments_after_words, body)`.
    pub fn for_command(&mut self) -> Result<(
        String,
        Vec<ast::Newline>,
        Option<Vec<B::Word>>,
        Option<Vec<ast::Newline>>,
        Vec<B::Command>), ParseError<B::Err>>
    {
        try!(self.reserved_word(&["for"]));

        self.skip_whitespace();
        let var = match self.iter.next() {
            Some(Name(v)) => v,
            t => return Err(self.make_unexpected_err(t)),
        };

        let post_var_comments = self.linebreak();
        let (words, post_word_comments) = if self.peek_reserved_word(&["in"]).is_some() {
            try!(self.reserved_word(&["in"]));

            let mut words = Vec::new();
            while let Some(w) = try!(self.word()) {
                words.push(w);
            }

            let found_semi = if let Some(&Semi) = self.iter.peek() {
                self.iter.next();
                true
            } else {
                false
            };

            // We need either a newline or a ; to separate the words from the body
            // Thus if neither is found it is considered an error
            let post_word_comments = self.linebreak();
            if !found_semi && post_word_comments.is_empty() {
                return Err(self.make_unexpected_err(None));
            }

            (Some(words), Some(post_word_comments))
        } else {
            (None, None)
        };

        let body = try!(self.do_group());
        Ok((var, post_var_comments, words, post_word_comments, body))
    }

    /// Parses a single `case` command but does not parse any redirections that may follow.
    ///
    /// Since `case` is a compound command (and can have redirections applied to it) this
    /// method returns the relevant parts of the `case` command, without constructing an
    /// AST node, it so that the caller can do so with redirections.
    ///
    /// Return structure is `Result( word_to_match, comments_after_word,
    /// ( (pre_pat_comments, pattern_alternatives+, post_pat_comments), cmds_to_run_on_match)* )`.
    pub fn case_command(&mut self) -> Result<(
            B::Word,
            Vec<ast::Newline>,
            Vec<( (Vec<ast::Newline>, Vec<B::Word>, Vec<ast::Newline>), Vec<B::Command> )>,
            Vec<ast::Newline>
        ), ParseError<B::Err>>
    {
        try!(self.reserved_word(&["case"]));
        let word = match try!(self.word()) {
            Some(w) => w,
            None => return Err(self.make_unexpected_err(None)),
        };

        let post_word_comments = self.linebreak();
        try!(self.reserved_word(&["in"]));
        let mut pre_esac_comments = None;

        let mut branches = Vec::new();
        loop {
            let pre_pat_comments = self.linebreak();
            if self.peek_reserved_word(&["esac"]).is_some() {
                // Make sure we don't lose the captured comments if there are no body
                debug_assert_eq!(pre_esac_comments, None);
                pre_esac_comments = Some(pre_pat_comments);
                break;
            }

            if let Some(&ParenOpen) = self.iter.peek() {
                self.iter.next();
            }

            let mut patterns = Vec::new();
            loop {
                match try!(self.word()) {
                    Some(p) => patterns.push(p),
                    None => return Err(self.make_unexpected_err(None)),
                }

                match self.iter.next() {
                    Some(Pipe) => continue,
                    Some(ParenClose) if !patterns.is_empty() => break,
                    t => return Err(self.make_unexpected_err(t)),
                }
            }

            // NB: we must capture linebreaks here since `peek_reserved_word`
            // will not consume them, and it could mistake a reserved word for a command.
            let patterns = (pre_pat_comments, patterns, self.linebreak());

            // DSemi's are always special tokens, hence they aren't
            // reserved words, and thus the `command_list` method doesn't apply.
            let mut cmds = Vec::new();
            loop {
                // Make sure we check for both delimiters
                if self.peek_reserved_word(&["esac"]).is_some() { break; }
                if let Some(&DSemi) = self.iter.peek() { break; }

                match try!(self.complete_command()) {
                    Some(c) => cmds.push(c),
                    None => break,
                }
            }

            branches.push((patterns, cmds));

            match self.iter.peek() {
                Some(&DSemi) => {
                    self.iter.next();
                    continue;
                },
                _ => break,
            }
        }
        let remaining_comments = self.linebreak();
        let pre_esac_comments = match pre_esac_comments {
            Some(mut comments) => {
                comments.reserve(remaining_comments.len());
                for c in remaining_comments {
                    comments.push(c);
                }
                comments
            },
            None => remaining_comments,
        };

        try!(self.reserved_word(&["esac"]));

        Ok((word, post_word_comments, branches, pre_esac_comments))
    }

    /// Parses a single function declaration.
    ///
    /// A function declaration must either begin with the `function` reserved word, or
    /// the name of the function must be followed by `()`. Whitespace is allowed between
    /// the name and `(`, and whitespace is allowed between `()`.
    fn function_declaration(&mut self) -> Result<B::Command, ParseError<B::Err>> {
        let found_fn = match self.peek_reserved_word(&["function"]) {
            Some(_) => { self.iter.next(); true },
            None => false,
        };

        self.skip_whitespace();
        let name = match self.iter.next() {
            Some(Name(n)) => n,
            Some(Literal(s)) => return Err(self.make_bad_ident_err(s)),
            t => return Err(self.make_unexpected_err(t)),
        };

        // There must be whitespace after the function name, UNLESS we find `()` immediately after,
        // or we hit a newline if we have the `function` keyword (and parens are not needed).
        match self.iter.multipeek(3) {
            [Whitespace(_), ..]                        |
            [ParenOpen, ParenClose, ..]                |
            [ParenOpen, Whitespace(_), ParenClose, ..] => {},
            [Newline, ..] if found_fn                  => {},

            _ => return Err(self.make_unexpected_err(None)),
        }

        self.skip_whitespace();
        match self.iter.multipeek(3) {
            [ParenOpen, Whitespace(_), ParenClose, ..] => {
                self.iter.next();
                self.iter.next();
                self.iter.next();
            },

            [ParenOpen, ParenClose, ..] => {
                self.iter.next();
                self.iter.next();
            },

            // If no `function` keyword, we must find `()`
            _ => if !found_fn { return Err(self.make_unexpected_err(None)) },
        }

        let body = match try!(self.complete_command()) {
            Some(c) => c,
            None => return Err(self.make_unexpected_err(None)),
        };

        Ok(try!(self.builder.function_declaration(name, body)))
    }

    /// Skips over any encountered whitespace but preserves newlines.
    #[inline]
    pub fn skip_whitespace(&mut self) {
        loop {
            while let Some(&Whitespace(_)) = self.iter.peek() {
                self.iter.next();
            }

            match self.iter.multipeek(2) {
                [Backslash, Newline, ..] => {
                    self.iter.next();
                    self.iter.next();
                },
                _ => break,
            }
        }
    }

    /// Captures any encountered whitespace and newlines. Comments are NOT recognized.
    fn capture_whitespace(&mut self) -> Vec<builder::WordKind<B::Command>> {
        let mut vec = Vec::new();
        loop {
            while let Some(&Whitespace(_)) = self.iter.peek() {
                if let Some(Whitespace(w)) = self.iter.next() {
                    vec.push(builder::WordKind::Literal(w));
                }
            }

            match self.iter.multipeek(2) {
                [Backslash, Newline, ..] => {
                    self.iter.next();
                    vec.push(builder::WordKind::Escaped(self.iter.next().unwrap().to_string()));
                },
                _ => break,
            }
        }

        vec
    }

    /// Parses zero or more `Token::Newline`s, skipping whitespace but capturing comments.
    #[inline]
    pub fn linebreak(&mut self) -> Vec<ast::Newline> {
        let mut lines = Vec::new();
        while let Some(n) = self.newline() {
            lines.push(n);
        }
        lines
    }

    /// Tries to parse a `Token::Newline` (or a comment) after skipping whitespace.
    pub fn newline(&mut self) -> Option<ast::Newline> {
        self.skip_whitespace();

        match self.iter.peek() {
            Some(&Pound) => {
                let comment = self.iter.by_ref()
                    .take_while(|t| t != &Newline)
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .concat();

                Some(ast::Newline(Some(comment)))
            },

            Some(&Newline) => {
                self.iter.next();
                Some(ast::Newline(None))
            },

            _ => return None,
        }
    }

    /// Checks that one of the specified tokens appears as a reserved word.
    ///
    /// The token must be followed by a token which delimits a word when it is
    /// unquoted/unescaped.
    ///
    /// If a reserved word is found, the token which it matches will be
    /// returned in case the caller cares which specific reserved word was found.
    pub fn peek_reserved_token<'a>(&mut self, tokens: &'a [Token]) -> Option<&'a Token> {
        let care_about_whitespace = tokens.iter().any(|tok| {
            if let &Whitespace(_) = tok {
                true
            } else {
                false
            }
        });

        // If the caller cares about whitespace as a reserved word we should
        // do a reserved word check without skipping any leading whitespace.
        // If we don't find anything the first time (or if the caller does
        // not care about whitespace tokens) we will skip the whitespace
        // and try again.
        let num_tries = if care_about_whitespace {
            2
        } else {
            self.skip_whitespace();
            1
        };

        for _ in 0..num_tries {
            {
                let tok = match self.iter.multipeek(2) {
                    // Don't forget about delimiting through EOF!
                    [ref kw] => kw,
                    [ref kw, ref delim] if delim.is_word_delimiter() => kw,
                    _ => continue,
                };

                match tokens.iter().find(|&t| t == tok) {
                    ret@Some(_) => return ret,
                    None => {},
                }
            }

            self.skip_whitespace();
        }

        None
    }

    /// Checks that one of the specified strings appears as a reserved word.
    ///
    /// The word must appear as a single token, unquoted and unescaped, and
    /// must be followed by a token which delimits a word when it is
    /// unquoted/unescaped. The reserved word may appear as a `Token::Name`
    /// or a `Token::Literal`.
    ///
    /// If a reserved word is found, the string which it matches will be
    /// returned in case the caller cares which specific reserved word was found.
    pub fn peek_reserved_word<'a>(&mut self, words: &'a [&str]) -> Option<&'a str> {
        self.skip_whitespace();
        let tok = match self.iter.multipeek(2) {
            // Don't forget about delimiting through EOF!
            [ref kw] => kw,
            [ref kw, ref delim] if delim.is_word_delimiter() => kw,
            _ => return None,
        };

        match *tok {
            Name(ref kw) |
            Literal(ref kw) => words.iter().find(|&w| w == kw).map(|kw| *kw),
            _ => None,
        }
    }

    /// Checks that one of the specified tokens appears as a reserved word
    /// and consumes it, returning the token it matched in case the caller
    /// cares which specific reserved word was found.
    pub fn reserved_token(&mut self, tokens: &[Token]) -> Result<Token, ParseError<B::Err>> {
        match self.peek_reserved_token(tokens) {
            Some(_) => Ok(self.iter.next().unwrap()),
            None => Err(self.make_unexpected_err(None)),
        }
    }

    /// Checks that one of the specified strings appears as a reserved word
    /// and consumes it, returning the string it matched in case the caller
    /// cares which specific reserved word was found.
    pub fn reserved_word<'a>(&mut self, words: &'a [&str]) -> Result<&'a str, ParseError<B::Err>> {
        match self.peek_reserved_word(words) {
            Some(s) => { self.iter.next(); Ok(s) },
            None => Err(self.make_unexpected_err(None)),
        }
    }

    /// Parses commands until a reserved word or reserved token (or EOF)
    /// is reached, without consuming the reserved word.
    ///
    /// The reserved word/token **must** appear after a complete command
    /// separator (e.g. `;`, `&`, or a newline), otherwise it will be
    /// parsed as part of the command.
    ///
    /// It is considered an error if no commands are present.
    pub fn command_list(&mut self, words: &[&str], tokens: &[Token]) -> Result<Vec<B::Command>, ParseError<B::Err>> {
        let mut cmds = Vec::new();
        loop {
            if self.peek_reserved_word(words).is_some() || self.peek_reserved_token(tokens).is_some() {
                break;
            }

            match try!(self.complete_command()) {
                Some(c) => cmds.push(c),
                None => break,
            }
        }

        if cmds.is_empty() {
            Err(self.make_unexpected_err(None))
        } else {
            Ok(cmds)
        }
    }
}

#[cfg(test)]
pub mod test {
    use syntax::lexer::Lexer;

    use syntax::ast::*;
    use syntax::ast::Command::*;
    use syntax::ast::CompoundCommand::*;
    use syntax::parse::*;
    use syntax::token::Token;

    pub fn make_parser(src: &str) -> DefaultParser<Lexer<::std::str::Chars>> {
        DefaultParser::new(Lexer::new(src.chars()))
    }

    fn make_parser_from_tokens(src: Vec<Token>) -> DefaultParser<::std::vec::IntoIter<Token>> {
        DefaultParser::new(src.into_iter())
    }

    fn cmd_args_unboxed(cmd: &str, args: &[&str]) -> Command {
        Simple(Box::new(SimpleCommand {
            cmd: Some(Word::Literal(String::from(cmd))),
            args: args.iter().map(|&a| Word::Literal(String::from(a))).collect(),
            vars: vec!(),
            io: vec!(),
        }))
    }

    fn cmd_unboxed(cmd: &str) -> Command {
        cmd_args_unboxed(cmd, &[])
    }

    fn cmd(cmd: &str) -> Box<Command> {
        Box::new(cmd_unboxed(cmd))
    }

    pub fn sample_simple_command() -> (Option<Word>, Vec<Word>, Vec<(String, Option<Word>)>, Vec<Redirect>) {
        (
            Some(Word::Literal(String::from("foo"))),
            vec!(
                Word::Literal(String::from("bar")),
                Word::Literal(String::from("baz")),
            ),
            vec!(
                (String::from("var"), Some(Word::Literal(String::from("val")))),
                (String::from("ENV"), Some(Word::Literal(String::from("true")))),
                (String::from("BLANK"), None),
            ),
            vec!(
                Redirect::Clobber(Some(Word::Literal(String::from("2"))), Word::Literal(String::from("clob"))),
                Redirect::ReadWrite(Some(Word::Literal(String::from("3"))), Word::Literal(String::from("rw"))),
                Redirect::Read(None, Word::Literal(String::from("in"))),
            ),
        )
    }

    #[test]
    fn test_linebreak_valid_with_comments_and_whitespace() {
        let mut p = make_parser("\n\t\t\t\n # comment1\n#comment2\n   \n");
        assert_eq!(p.linebreak(), vec!(
                Newline(None),
                Newline(None),
                Newline(Some(String::from("# comment1"))),
                Newline(Some(String::from("#comment2"))),
                Newline(None)
            )
        );
    }

    #[test]
    fn test_linebreak_valid_empty() {
        let mut p = make_parser("");
        assert_eq!(p.linebreak(), vec!());
    }

    #[test]
    fn test_linebreak_valid_nonnewline() {
        let mut p = make_parser("hello world");
        assert_eq!(p.linebreak(), vec!());
    }

    #[test]
    fn test_linebreak_valid_eof_instead_of_newline() {
        let mut p = make_parser("#comment");
        assert_eq!(p.linebreak(), vec!(Newline(Some(String::from("#comment")))));
    }

    #[test]
    fn test_linebreak_single_quote_insiginificant() {
        let mut p = make_parser("#unclosed quote ' comment");
        assert_eq!(p.linebreak(), vec!(Newline(Some(String::from("#unclosed quote ' comment")))));
    }

    #[test]
    fn test_linebreak_double_quote_insiginificant() {
        let mut p = make_parser("#unclosed quote \" comment");
        assert_eq!(p.linebreak(), vec!(Newline(Some(String::from("#unclosed quote \" comment")))));
    }

    #[test]
    fn test_linebreak_escaping_newline_insignificant() {
        let mut p = make_parser("#comment escapes newline\\\n");
        assert_eq!(p.linebreak(), vec!(Newline(Some(String::from("#comment escapes newline\\")))));
    }

    #[test]
    fn test_skip_whitespace_preserve_newline() {
        let mut p = make_parser("    \t\t \t \t\n   ");
        p.skip_whitespace();
        assert_eq!(p.linebreak().len(), 1);
    }

    #[test]
    fn test_skip_whitespace_preserve_comments() {
        let mut p = make_parser("    \t\t \t \t#comment\n   ");
        p.skip_whitespace();
        assert_eq!(p.linebreak().pop().unwrap(), Newline(Some(String::from("#comment"))));
    }

    #[test]
    fn test_skip_whitespace_comments_capture_all_up_to_newline() {
        let mut p = make_parser("#comment&&||;;()<<-\n");
        assert_eq!(p.linebreak().pop().unwrap(), Newline(Some(String::from("#comment&&||;;()<<-"))));
    }

    #[test]
    fn test_skip_whitespace_comments_may_end_with_eof() {
        let mut p = make_parser("#comment");
        assert_eq!(p.linebreak().pop().unwrap(), Newline(Some(String::from("#comment"))));
    }

    #[test]
    fn test_skip_whitespace_skip_escapes_dont_affect_newlines() {
        let mut p = make_parser("  \t \\\n  \\\n#comment\n");
        p.skip_whitespace();
        assert_eq!(p.linebreak().pop().unwrap(), Newline(Some(String::from("#comment"))));
    }

    #[test]
    fn test_skip_whitespace_skips_escaped_newlines() {
        let mut p = make_parser("\\\n\\\n   \\\n");
        p.skip_whitespace();
        assert_eq!(p.linebreak(), vec!());
    }

    #[test]
    fn test_and_or_correct_associativity() {
        let mut p = make_parser("foo || bar && baz");
        let correct = And(Box::new(Or(cmd("foo"), cmd("bar"))), cmd("baz"));
        assert_eq!(correct, p.and_or().unwrap());
    }

    #[test]
    fn test_and_or_valid_with_newlines_after_operator() {
        let mut p = make_parser("foo ||\n\n\n\nbar && baz");
        let correct = And(Box::new(Or(cmd("foo"), cmd("bar"))), cmd("baz"));
        assert_eq!(correct, p.and_or().unwrap());
    }

    #[test]
    fn test_and_or_invalid_with_newlines_before_operator() {
        let mut p = make_parser("foo || bar\n\n&& baz");
        p.and_or().unwrap();     // Successful parse Or(foo, bar)
        p.and_or().unwrap_err(); // Fail to parse "&& baz" which is an error
    }

    #[test]
    fn test_pipeline_valid_bang() {
        let mut p = make_parser("! foo | bar | baz");
        let correct = Pipe(true, vec!(cmd_unboxed("foo"), cmd_unboxed("bar"), cmd_unboxed("baz")));
        assert_eq!(correct, p.and_or().unwrap());
    }

    #[test]
    fn test_pipeline_valid_bangs_in_and_or() {
        let mut p = make_parser("! foo | bar || ! baz && ! foobar");
        let correct = And(
            Box::new(Or(Box::new(Pipe(true, vec!(cmd_unboxed("foo"), cmd_unboxed("bar")))), Box::new(Pipe(true, vec!(cmd_unboxed("baz")))))),
            Box::new(Pipe(true, vec!(cmd_unboxed("foobar"))))
        );
        assert_eq!(correct, p.and_or().unwrap());
    }

    #[test]
    fn test_pipeline_no_bang_single_cmd_optimize_wrapper_out() {
        let mut p = make_parser("foo");
        let parse = p.pipeline().unwrap();
        if let Pipe(..) = parse {
            panic!("Parser::pipeline should not create a wrapper if no ! present and only a single command");
        }
    }

    #[test]
    fn test_pipeline_invalid_multiple_bangs_in_same_pipeline() {
        let mut p = make_parser("! foo | bar | ! baz");
        p.pipeline().unwrap_err();
    }

    #[test]
    fn test_comment_cannot_start_mid_whitespace_delimited_word() {
        let mut p = make_parser("hello#world");
        let word = p.word().unwrap().expect("no valid word was discovered");
        assert_eq!(word, Word::Concat(vec!(
                    Word::Literal(String::from("hello")),
                    Word::Literal(String::from("#")),
                    Word::Literal(String::from("world")),
        )));
    }

    #[test]
    fn test_comment_can_start_if_whitespace_before_pound() {
        let mut p = make_parser("hello #world");
        p.word().unwrap().expect("no valid word was discovered");
        let comment = p.linebreak();
        assert_eq!(comment, vec!(Newline(Some(String::from("#world")))));
    }

    #[test]
    fn test_complete_command_job() {
        let mut p = make_parser("foo && bar & baz");
        let cmd1 = p.complete_command().unwrap().expect("failed to parse first command");
        let cmd2 = p.complete_command().unwrap().expect("failed to parse second command");

        let correct1 = Job(Box::new(And(cmd("foo"), cmd("bar"))));
        let correct2 = cmd_unboxed("baz");

        assert_eq!(correct1, cmd1);
        assert_eq!(correct2, cmd2);
    }

    #[test]
    fn test_complete_command_non_eager_parse() {
        let mut p = make_parser("foo && bar; baz\n\nqux");
        let cmd1 = p.complete_command().unwrap().expect("failed to parse first command");
        let cmd2 = p.complete_command().unwrap().expect("failed to parse second command");
        let cmd3 = p.complete_command().unwrap().expect("failed to parse third command");

        let correct1 = And(cmd("foo"), cmd("bar"));
        let correct2 = cmd_unboxed("baz");
        let correct3 = cmd_unboxed("qux");

        assert_eq!(correct1, cmd1);
        assert_eq!(correct2, cmd2);
        assert_eq!(correct3, cmd3);
    }

    #[test]
    fn test_complete_command_valid_no_input() {
        let mut p = make_parser("");
        p.complete_command().ok().expect("no input caused an error");
    }

    #[test]
    fn test_parameter_short() {
        let words = vec!(
            Word::Param(Parameter::At),
            Word::Param(Parameter::Star),
            Word::Param(Parameter::Pound),
            Word::Param(Parameter::Question),
            Word::Param(Parameter::Dash),
            Word::Param(Parameter::Dollar),
            Word::Param(Parameter::Bang),
            Word::Param(Parameter::Positional(3)),
        );

        let mut p = make_parser("$@$*$#$?$-$$$!$3$");
        for param in words {
            assert_eq!(p.parameter().unwrap(), param);
        }

        assert_eq!(Word::Literal(String::from("$")), p.parameter().unwrap());
        p.parameter().unwrap_err(); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_short_in_curlies() {
        let words = vec!(
            Word::Param(Parameter::At),
            Word::Param(Parameter::Star),
            Word::Param(Parameter::Pound),
            Word::Param(Parameter::Question),
            Word::Param(Parameter::Dash),
            Word::Param(Parameter::Dollar),
            Word::Param(Parameter::Bang),
            Word::Param(Parameter::Var(String::from("foo"))),
            Word::Param(Parameter::Positional(3)),
            Word::Param(Parameter::Positional(1000)),
        );

        let mut p = make_parser("${@}${*}${#}${?}${-}${$}${!}${foo}${3}${1000}");
        for param in words {
            assert_eq!(p.parameter().unwrap(), param);
        }

        p.parameter().unwrap_err(); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_command_substitution() {
        let correct = Word::Subst(ParameterSubstitution::Command(vec!(
            cmd_args_unboxed("echo", &["hello"]),
            cmd_args_unboxed("echo", &["world"]),
        )));

        assert_eq!(correct, make_parser("$(echo hello; echo world)").parameter().unwrap());
    }

    #[test]
    fn test_parameter_command_substitution_valid_empty_substitution() {
        assert_eq!(Word::Subst(ParameterSubstitution::Command(vec!())), make_parser("$()").parameter().unwrap());
    }

    #[test]
    fn test_parameter_literal_dollar_if_no_param() {
        let mut p = make_parser("$^asdf");
        assert_eq!(Word::Literal(String::from("$")), p.parameter().unwrap());
        assert_eq!(p.word().unwrap().unwrap(), Word::Literal(String::from("^asdf")));
    }

    #[test]
    fn test_parameter_substitution() {
        let words = vec!(
            Word::Subst(ParameterSubstitution::Len(Parameter::At)),
            Word::Subst(ParameterSubstitution::Len(Parameter::Star)),
            Word::Subst(ParameterSubstitution::Len(Parameter::Pound)),
            Word::Subst(ParameterSubstitution::Len(Parameter::Question)),
            Word::Subst(ParameterSubstitution::Len(Parameter::Dash)),
            Word::Subst(ParameterSubstitution::Len(Parameter::Dollar)),
            Word::Subst(ParameterSubstitution::Len(Parameter::Bang)),
            Word::Subst(ParameterSubstitution::Len(Parameter::Var(String::from("foo")))),
            Word::Subst(ParameterSubstitution::Len(Parameter::Positional(3))),
            Word::Subst(ParameterSubstitution::Len(Parameter::Positional(1000))),
            Word::Subst(ParameterSubstitution::Command(vec!(cmd_args_unboxed("echo", &["foo"])))),
        );

        let mut p = make_parser("${#@}${#*}${##}${#?}${#-}${#$}${#!}${#foo}${#3}${#1000}$(echo foo)");
        for param in words {
            assert_eq!(param, p.parameter().unwrap());
        }

        p.parameter().unwrap_err(); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_smallest_suffix() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = Word::Literal(String::from("foo"));

        let substs = vec!(
            RemoveSmallestSuffix(At, Some(Box::new(word.clone()))),
            RemoveSmallestSuffix(Star, Some(Box::new(word.clone()))),
            RemoveSmallestSuffix(Pound, Some(Box::new(word.clone()))),
            RemoveSmallestSuffix(Question, Some(Box::new(word.clone()))),
            RemoveSmallestSuffix(Dash, Some(Box::new(word.clone()))),
            RemoveSmallestSuffix(Dollar, Some(Box::new(word.clone()))),
            RemoveSmallestSuffix(Bang, Some(Box::new(word.clone()))),
            RemoveSmallestSuffix(Positional(0), Some(Box::new(word.clone()))),
            RemoveSmallestSuffix(Positional(10), Some(Box::new(word.clone()))),
            RemoveSmallestSuffix(Positional(100), Some(Box::new(word.clone()))),
            RemoveSmallestSuffix(Var(String::from("foo_bar123")), Some(Box::new(word.clone()))),

            RemoveSmallestSuffix(At, None),
            RemoveSmallestSuffix(Star, None),
            RemoveSmallestSuffix(Pound, None),
            RemoveSmallestSuffix(Question, None),
            RemoveSmallestSuffix(Dash, None),
            RemoveSmallestSuffix(Dollar, None),
            RemoveSmallestSuffix(Bang, None),
            RemoveSmallestSuffix(Positional(0), None),
            RemoveSmallestSuffix(Positional(10), None),
            RemoveSmallestSuffix(Positional(100), None),
            RemoveSmallestSuffix(Var(String::from("foo_bar123")), None),
        );

        let src = "${@%foo}${*%foo}${#%foo}${?%foo}${-%foo}${$%foo}${!%foo}${0%foo}${10%foo}${100%foo}${foo_bar123%foo}${@%}${*%}${#%}${?%}${-%}${$%}${!%}${0%}${10%}${100%}${foo_bar123%}";
        let mut p = make_parser(src);

        for s in substs {
            assert_eq!(Word::Subst(s), p.parameter().unwrap());
        }

        p.parameter().unwrap_err(); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_largest_suffix() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = Word::Literal(String::from("foo"));

        let substs = vec!(
            RemoveLargestSuffix(At, Some(Box::new(word.clone()))),
            RemoveLargestSuffix(Star, Some(Box::new(word.clone()))),
            RemoveLargestSuffix(Pound, Some(Box::new(word.clone()))),
            RemoveLargestSuffix(Question, Some(Box::new(word.clone()))),
            RemoveLargestSuffix(Dash, Some(Box::new(word.clone()))),
            RemoveLargestSuffix(Dollar, Some(Box::new(word.clone()))),
            RemoveLargestSuffix(Bang, Some(Box::new(word.clone()))),
            RemoveLargestSuffix(Positional(0), Some(Box::new(word.clone()))),
            RemoveLargestSuffix(Positional(10), Some(Box::new(word.clone()))),
            RemoveLargestSuffix(Positional(100), Some(Box::new(word.clone()))),
            RemoveLargestSuffix(Var(String::from("foo_bar123")), Some(Box::new(word.clone()))),

            RemoveLargestSuffix(At, None),
            RemoveLargestSuffix(Star, None),
            RemoveLargestSuffix(Pound, None),
            RemoveLargestSuffix(Question, None),
            RemoveLargestSuffix(Dash, None),
            RemoveLargestSuffix(Dollar, None),
            RemoveLargestSuffix(Bang, None),
            RemoveLargestSuffix(Positional(0), None),
            RemoveLargestSuffix(Positional(10), None),
            RemoveLargestSuffix(Positional(100), None),
            RemoveLargestSuffix(Var(String::from("foo_bar123")), None),
        );

        let src = "${@%%foo}${*%%foo}${#%%foo}${?%%foo}${-%%foo}${$%%foo}${!%%foo}${0%%foo}${10%%foo}${100%%foo}${foo_bar123%%foo}${@%%}${*%%}${#%%}${?%%}${-%%}${$%%}${!%%}${0%%}${10%%}${100%%}${foo_bar123%%}";
        let mut p = make_parser(src);

        for s in substs {
            assert_eq!(Word::Subst(s), p.parameter().unwrap());
        }

        p.parameter().unwrap_err(); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_smallest_prefix() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = Word::Literal(String::from("foo"));

        let substs = vec!(
            RemoveSmallestPrefix(At, Some(Box::new(word.clone()))),
            RemoveSmallestPrefix(Star, Some(Box::new(word.clone()))),
            RemoveSmallestPrefix(Pound, Some(Box::new(word.clone()))),
            RemoveSmallestPrefix(Question, Some(Box::new(word.clone()))),
            RemoveSmallestPrefix(Dash, Some(Box::new(word.clone()))),
            RemoveSmallestPrefix(Dollar, Some(Box::new(word.clone()))),
            RemoveSmallestPrefix(Bang, Some(Box::new(word.clone()))),
            RemoveSmallestPrefix(Positional(0), Some(Box::new(word.clone()))),
            RemoveSmallestPrefix(Positional(10), Some(Box::new(word.clone()))),
            RemoveSmallestPrefix(Positional(100), Some(Box::new(word.clone()))),
            RemoveSmallestPrefix(Var(String::from("foo_bar123")), Some(Box::new(word.clone()))),

            RemoveSmallestPrefix(At, None),
            RemoveSmallestPrefix(Star, None),
            //RemoveSmallestPrefix(Pound, None), // ${##} should parse as Len(#)
            RemoveSmallestPrefix(Question, None),
            RemoveSmallestPrefix(Dash, None),
            RemoveSmallestPrefix(Dollar, None),
            RemoveSmallestPrefix(Bang, None),
            RemoveSmallestPrefix(Positional(0), None),
            RemoveSmallestPrefix(Positional(10), None),
            RemoveSmallestPrefix(Positional(100), None),
            RemoveSmallestPrefix(Var(String::from("foo_bar123")), None),
        );

        let src = "${@#foo}${*#foo}${##foo}${?#foo}${-#foo}${$#foo}${!#foo}${0#foo}${10#foo}${100#foo}${foo_bar123#foo}${@#}${*#}${?#}${-#}${$#}${!#}${0#}${10#}${100#}${foo_bar123#}";
        let mut p = make_parser(src);

        for s in substs {
            assert_eq!(Word::Subst(s), p.parameter().unwrap());
        }

        p.parameter().unwrap_err(); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_largest_prefix() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = Word::Literal(String::from("foo"));

        let substs = vec!(
            RemoveLargestPrefix(At, Some(Box::new(word.clone()))),
            RemoveLargestPrefix(Star, Some(Box::new(word.clone()))),
            RemoveLargestPrefix(Pound, Some(Box::new(word.clone()))),
            RemoveLargestPrefix(Question, Some(Box::new(word.clone()))),
            RemoveLargestPrefix(Dash, Some(Box::new(word.clone()))),
            RemoveLargestPrefix(Dollar, Some(Box::new(word.clone()))),
            RemoveLargestPrefix(Bang, Some(Box::new(word.clone()))),
            RemoveLargestPrefix(Positional(0), Some(Box::new(word.clone()))),
            RemoveLargestPrefix(Positional(10), Some(Box::new(word.clone()))),
            RemoveLargestPrefix(Positional(100), Some(Box::new(word.clone()))),
            RemoveLargestPrefix(Var(String::from("foo_bar123")), Some(Box::new(word.clone()))),

            RemoveLargestPrefix(At, None),
            RemoveLargestPrefix(Star, None),
            RemoveLargestPrefix(Pound, None),
            RemoveLargestPrefix(Question, None),
            RemoveLargestPrefix(Dash, None),
            RemoveLargestPrefix(Dollar, None),
            RemoveLargestPrefix(Bang, None),
            RemoveLargestPrefix(Positional(0), None),
            RemoveLargestPrefix(Positional(10), None),
            RemoveLargestPrefix(Positional(100), None),
            RemoveLargestPrefix(Var(String::from("foo_bar123")), None),
        );

        let src = "${@##foo}${*##foo}${###foo}${?##foo}${-##foo}${$##foo}${!##foo}${0##foo}${10##foo}${100##foo}${foo_bar123##foo}${@##}${*##}${###}${?##}${-##}${$##}${!##}${0##}${10##}${100##}${foo_bar123##}";
        let mut p = make_parser(src);

        for s in substs {
            assert_eq!(Word::Subst(s), p.parameter().unwrap());
        }

        p.parameter().unwrap_err(); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_words_can_have_spaces_and_escaped_curlies() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = Box::new(Word::Concat(vec!(
            Word::Literal(String::from("foo")),
            Word::Literal(String::from("{")),
            Word::Escaped(String::from("}")),
            Word::Literal(String::from(" \t\r ")),
            Word::Escaped(String::from("\n")),
            Word::Literal(String::from("bar")),
            Word::Literal(String::from(" \t\r ")),
        )));

        let substs = vec!(
            RemoveSmallestSuffix(Var(String::from("foo_bar123")), Some(word.clone())),
            RemoveLargestSuffix(Var(String::from("foo_bar123")), Some(word.clone())),
            RemoveSmallestPrefix(Var(String::from("foo_bar123")), Some(word.clone())),
            RemoveLargestPrefix(Var(String::from("foo_bar123")), Some(word.clone())),
        );

        let src = vec!(
            "%",
            "%%",
            "#",
            "##",
        );

        for (i, s) in substs.into_iter().enumerate() {
            let src = format!("${{foo_bar123{}foo{{\\}} \t\r \\\nbar \t\r }}", src[i]);
            let mut p = make_parser(&src);
            assert_eq!(Word::Subst(s), p.parameter().unwrap());
            p.parameter().unwrap_err(); // Stream should be exhausted
        }
    }

    #[test]
    fn test_parameter_substitution_words_can_be_parameters_or_substitutions_as_well() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = Box::new(Word::Concat(vec!(
            Word::Param(At),
            Word::Subst(RemoveLargestPrefix(
                Var(String::from("foo")),
                Some(Box::new(Word::Literal(String::from("bar"))))
            )),
        )));

        let substs = vec!(
            RemoveSmallestSuffix(Var(String::from("foo_bar123")), Some(word.clone())),
            RemoveLargestSuffix(Var(String::from("foo_bar123")), Some(word.clone())),
            RemoveSmallestPrefix(Var(String::from("foo_bar123")), Some(word.clone())),
            RemoveLargestPrefix(Var(String::from("foo_bar123")), Some(word.clone())),
        );

        let src = vec!(
            "%",
            "%%",
            "#",
            "##",
        );

        for (i, s) in substs.into_iter().enumerate() {
            let src = format!("${{foo_bar123{}$@${{foo##bar}}}}", src[i]);
            let mut p = make_parser(&src);
            assert_eq!(Word::Subst(s), p.parameter().unwrap());
            p.parameter().unwrap_err(); // Stream should be exhausted
        }
    }

    #[test]
    fn test_redirect_valid_close_without_whitespace() {
        let mut p = make_parser(">&-");
        assert_eq!(Some(Ok(Redirect::CloseWrite(None))), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_close_with_whitespace() {
        let mut p = make_parser("<&       -");
        assert_eq!(Some(Ok(Redirect::CloseRead(None))), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_return_word_if_no_redirect() {
        let mut p = make_parser("hello");
        assert_eq!(Some(Err(Word::Literal(String::from("hello")))), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_return_word_if_src_fd_is_definitely_non_numeric() {
        let mut p = make_parser("123$$'foo'>out");
        let correct = Word::Concat(vec!(
            Word::Literal(String::from("123")),
            Word::Param(Parameter::Dollar),
            Word::SingleQuoted(String::from("foo")),
        ));
        assert_eq!(Some(Err(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_return_word_if_src_fd_has_escaped_numerics() {
        let mut p = make_parser("\\2>");
        let correct = Word::Escaped(String::from("2"));
        assert_eq!(Some(Err(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_return_redirect_if_src_fd_is_possibly_numeric() {
        let mut p = make_parser("123$$$(echo 2)>out");
        let correct = Redirect::Write(
            Some(Word::Concat(vec!(
                Word::Literal(String::from("123")),
                Word::Param(Parameter::Dollar),
                Word::Subst(ParameterSubstitution::Command(vec!(cmd_args_unboxed("echo", &["2"])))),
            ))),
            Word::Literal(String::from("out"))
        );
        assert_eq!(Some(Ok(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_dst_fd_can_have_escaped_numerics() {
        let mut p = make_parser(">\\2");
        let correct = Redirect::Write(
            None,
            Word::Escaped(String::from("2")),
        );
        assert_eq!(Some(Ok(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_invalid_dup_if_dst_fd_is_definitely_non_numeric() {
        let mut p = make_parser(">&123$$'foo'");
        p.redirect().unwrap_err();
    }

    #[test]
    fn test_redirect_valid_dup_return_redirect_if_dst_fd_is_possibly_numeric() {
        let mut p = make_parser(">&123$$$(echo 2)");
        let correct = Redirect::DupWrite(
            None,
            Word::Concat(vec!(
                Word::Literal(String::from("123")),
                Word::Param(Parameter::Dollar),
                Word::Subst(ParameterSubstitution::Command(vec!(cmd_args_unboxed("echo", &["2"])))),
            )),
        );
        assert_eq!(Some(Ok(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_invalid_close_without_whitespace() {
        let mut p = make_parser(">&-asdf");
        p.redirect().unwrap_err();
    }

    #[test]
    fn test_redirect_invalid_close_with_whitespace() {
        let mut p = make_parser("<&       -asdf");
        p.redirect().unwrap_err();
    }

    #[test]
    fn test_redirect_fd_immediately_preceeding_redirection() {
        let mut p = make_parser("foo 1>>out");
        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some(Word::Literal(String::from("foo"))),
            args: vec!(),
            vars: vec!(),
            io: vec!(Redirect::Append(Some(Word::Literal(String::from("1"))), Word::Literal(String::from("out")))),
        })));
    }

    #[test]
    fn test_redirect_fd_must_immediately_preceed_redirection() {
        let mut p = make_parser("foo 1 <>out");
        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some(Word::Literal(String::from("foo"))),
            args: vec!(Word::Literal(String::from("1"))),
            vars: vec!(),
            io: vec!(Redirect::ReadWrite(None, Word::Literal(String::from("out")))),
        })));
    }

    #[test]
    fn test_redirect_valid_dup_with_fd() {
        let mut p = make_parser("foo 1>&2");
        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some(Word::Literal(String::from("foo"))),
            args: vec!(),
            vars: vec!(),
            io: vec!(Redirect::DupWrite(Some(Word::Literal(String::from("1"))), Word::Literal(String::from("2")))),
        })));
    }

    #[test]
    fn test_redirect_valid_dup_without_fd() {
        let mut p = make_parser("foo 1 <&2");
        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some(Word::Literal(String::from("foo"))),
            args: vec!(Word::Literal(String::from("1"))),
            vars: vec!(),
            io: vec!(Redirect::DupRead(None, Word::Literal(String::from("2")))),
        })));
    }

    #[test]
    fn test_redirect_valid_dup_with_whitespace() {
        let mut p = make_parser("foo 1<& 2");
        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some(Word::Literal(String::from("foo"))),
            args: vec!(),
            vars: vec!(),
            io: vec!(Redirect::DupRead(Some(Word::Literal(String::from("1"))), Word::Literal(String::from("2")))),
        })));
    }

    #[test]
    fn test_redirect_valid_single_quoted_fd() {
        let correct = Redirect::Append(
            Some(Word::SingleQuoted(String::from("1"))),
            Word::Literal(String::from("out"))
        );
        assert_eq!(Some(Ok(correct)), make_parser("'1'>>out").redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_double_quoted_fd() {
        let correct = Redirect::Append(
            Some(Word::DoubleQuoted(vec!(Word::Literal(String::from("1"))))),
            Word::Literal(String::from("out"))
        );
        assert_eq!(Some(Ok(correct)), make_parser("\"1\">>out").redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_single_quoted_dup_fd() {
        let correct = Redirect::DupWrite(Some(Word::Literal(String::from("1"))), Word::SingleQuoted(String::from("2")));
        assert_eq!(Some(Ok(correct)), make_parser("1>&'2'").redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_double_quoted_dup_fd() {
        let correct = Redirect::DupWrite(None, Word::DoubleQuoted(vec!(Word::Literal(String::from("2")))));
        assert_eq!(Some(Ok(correct)), make_parser(">&\"2\"").redirect().unwrap());
    }

    #[test]
    fn test_redirect_src_fd_need_not_be_single_token() {
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("foo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("12")),
            Token::Literal(String::from("34")),
            Token::LessAnd,
            Token::Literal(String::from("-")),
        ));

        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some(Word::Literal(String::from("foo"))),
            args: vec!(),
            vars: vec!(),
            io: vec!(Redirect::CloseRead(Some(Word::Concat(vec!(
                Word::Literal(String::from("12")),
                Word::Literal(String::from("34")),
            ))))),
        })));
    }

    #[test]
    fn test_redirect_dst_fd_need_not_be_single_token() {
        let mut p = make_parser_from_tokens(vec!(
            Token::GreatAnd,
            Token::Literal(String::from("12")),
            Token::Literal(String::from("34")),
        ));

        let correct = Redirect::DupWrite(None, Word::Concat(vec!(
            Word::Literal(String::from("12")),
            Word::Literal(String::from("34")),
        )));

        assert_eq!(Some(Ok(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_accept_literal_and_name_tokens() {
        let mut p = make_parser_from_tokens(vec!(
            Token::GreatAnd,
            Token::Literal(String::from("12")),
        ));
        assert_eq!(Some(Ok(Redirect::DupWrite(None, Word::Literal(String::from("12"))))), p.redirect().unwrap());

        let mut p = make_parser_from_tokens(vec!(
            Token::GreatAnd,
            Token::Name(String::from("12")),
        ));
        assert_eq!(Some(Ok(Redirect::DupWrite(None, Word::Literal(String::from("12"))))), p.redirect().unwrap());
    }

    #[test]
    fn test_simple_command_valid_assignments_at_start_of_command() {
        let mut p = make_parser("var=val ENV=true BLANK= foo bar baz");
        let (cmd, args, vars, _) = sample_simple_command();
        let correct = Simple(Box::new(SimpleCommand { cmd: cmd, args: args, vars: vars, io: vec!() }));
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_assignments_after_start_of_command_should_be_args() {
        let mut p = make_parser("var=val ENV=true BLANK= foo var2=val2 bar baz var3=val3");
        let (cmd, mut args, vars, _) = sample_simple_command();
        args.insert(0, Word::Concat(vec!(Word::Literal(String::from("var2=")), Word::Literal(String::from("val2")))));
        args.push(Word::Concat(vec!(Word::Literal(String::from("var3=")), Word::Literal(String::from("val3")))));
        let correct = Simple(Box::new(SimpleCommand { cmd: cmd, args: args, vars: vars, io: vec!() }));
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_redirections_at_start_of_command() {
        let mut p = make_parser("2>|clob 3<>rw <in var=val ENV=true BLANK= foo bar baz");
        let (cmd, args, vars, io) = sample_simple_command();
        let correct = Simple(Box::new(SimpleCommand { cmd: cmd, args: args, vars: vars, io: io }));
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_redirections_at_end_of_command() {
        let mut p = make_parser("var=val ENV=true BLANK= foo bar baz 2>|clob 3<>rw <in");
        let (cmd, args, vars, io) = sample_simple_command();
        let correct = Simple(Box::new(SimpleCommand { cmd: cmd, args: args, vars: vars, io: io }));
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_redirections_throughout_the_command() {
        let mut p = make_parser("2>|clob var=val 3<>rw ENV=true BLANK= foo bar <in baz 4>&-");
        let (cmd, args, vars, mut io) = sample_simple_command();
        io.push(Redirect::CloseWrite(Some(Word::Literal(String::from("4")))));
        let correct = Simple(Box::new(SimpleCommand { cmd: cmd, args: args, vars: vars, io: io }));
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    #[ignore]
    fn test_heredoc_recognition() {
        //let mut p = make_parser("cat <<eof1; cat <<eof2
        //hello
        //eof1
        //world
        //eof2");
        panic!("placeholder: heredoc recognition not yet implemented");
    }

    #[test]
    #[ignore]
    fn test_heredoc_tab_removal_recognition() {
        //let mut p = make_parser("cat <<eof1; cat <<eof2
        //\t\thello
        //eof1
        //\t\tworld
        //eof2");
        panic!("placeholder: heredoc recognition not yet implemented");
    }

    #[test]
    fn test_redirect_list_valid() {
        let mut p = make_parser("1>>out <& 2 2>&-");
        let io = p.redirect_list().unwrap();
        assert_eq!(io, vec!(
            Redirect::Append(Some(Word::Literal(String::from("1"))), Word::Literal(String::from("out"))),
            Redirect::DupRead(None, Word::Literal(String::from("2"))),
            Redirect::CloseWrite(Some(Word::Literal(String::from("2")))),
        ));
    }

    #[test]
    fn test_redirect_list_rejects_non_fd_words() {
        let mut p = make_parser("1>>out <in 2>&- abc");
        p.redirect_list().unwrap_err();
        let mut p = make_parser("1>>out abc<in 2>&-");
        p.redirect_list().unwrap_err();
        let mut p = make_parser("1>>out abc <in 2>&-");
        p.redirect_list().unwrap_err();
    }

    #[test]
    fn test_do_group_valid() {
        let mut p = make_parser("do foo\nbar; baz; done");
        let correct = vec!(cmd_unboxed("foo"), cmd_unboxed("bar"), cmd_unboxed("baz"));
        assert_eq!(correct, p.do_group().unwrap());
    }

    #[test]
    fn test_do_group_invalid_missing_separator() {
        let mut p = make_parser("do foo\nbar; baz done");
        p.do_group().unwrap_err();
    }

    #[test]
    fn test_do_group_valid_keyword_delimited_by_separator() {
        let mut p = make_parser("do foo done; done");
        let correct = vec!(cmd_args_unboxed("foo", &["done"]));
        assert_eq!(correct, p.do_group().unwrap());
    }

    #[test]
    fn test_do_group_invalid_missing_keyword() {
        let mut p = make_parser("foo\nbar; baz; done");
        p.do_group().unwrap_err();
        let mut p = make_parser("do foo\nbar; baz");
        p.do_group().unwrap_err();
    }

    #[test]
    fn test_do_group_invalid_quoted() {
        let cmds = [
            "'do' foo\nbar; baz; done",
            "do foo\nbar; baz; 'done'",
            "\"do\" foo\nbar; baz; done",
            "do foo\nbar; baz; \"done\"",
        ];

        for c in cmds.into_iter() {
            match make_parser(c).do_group() {
                Err(_) => {},
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            }
        }
    }

    #[test]
    fn test_do_group_invalid_concat() {
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("d")),
            Token::Literal(String::from("o")),
            Token::Newline,
            Token::Literal(String::from("foo")),
            Token::Newline,
            Token::Literal(String::from("done")),
        ));
        p.do_group().unwrap_err();
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("do")),
            Token::Newline,
            Token::Literal(String::from("foo")),
            Token::Newline,
            Token::Literal(String::from("do")),
            Token::Literal(String::from("ne")),
        ));
        p.do_group().unwrap_err();
    }

    #[test]
    fn test_do_group_should_recognize_literals_and_names() {
        for do_tok in vec!(Token::Literal(String::from("do")), Token::Name(String::from("do"))) {
            for done_tok in vec!(Token::Literal(String::from("done")), Token::Name(String::from("done"))) {
                let mut p = make_parser_from_tokens(vec!(
                    do_tok.clone(),
                    Token::Newline,
                    Token::Literal(String::from("foo")),
                    Token::Newline,
                    done_tok
                ));
                p.do_group().unwrap();
            }
        }
    }

    #[test]
    fn test_do_group_invalid_missing_body() {
        let mut p = make_parser("do\ndone");
        p.loop_command().unwrap_err();
    }

    #[test]
    fn test_brace_group_valid() {
        let mut p = make_parser("{ foo\nbar; baz; }");
        let correct = vec!(cmd_unboxed("foo"), cmd_unboxed("bar"), cmd_unboxed("baz"));
        assert_eq!(correct, p.brace_group().unwrap());
    }

    #[test]
    fn test_brace_group_invalid_missing_separator() {
        let mut p = make_parser("{ foo\nbar; baz }");
        p.brace_group().unwrap_err();
    }

    #[test]
    fn test_brace_group_invalid_start_must_be_whitespace_delimited() {
        let mut p = make_parser("{foo\nbar; baz; }");
        p.brace_group().unwrap_err();
    }

    #[test]
    fn test_brace_group_invalid_end_must_be_whitespace_and_separator_delimited() {
        let mut p = make_parser("{ foo\nbar}; baz; }");
        p.brace_group().unwrap();
        assert_eq!(p.complete_command().unwrap(), None); // Ensure stream is empty
        let mut p = make_parser("{ foo\nbar; }baz; }");
        p.brace_group().unwrap();
        assert_eq!(p.complete_command().unwrap(), None); // Ensure stream is empty
    }

    #[test]
    fn test_brace_group_valid_keyword_delimited_by_separator() {
        let mut p = make_parser("{ foo }; }");
        let correct = vec!(cmd_args_unboxed("foo", &["}"]));
        assert_eq!(correct, p.brace_group().unwrap());
    }

    #[test]
    fn test_brace_group_invalid_missing_keyword() {
        let mut p = make_parser("{ foo\nbar; baz");
        p.brace_group().unwrap_err();
        let mut p = make_parser("foo\nbar; baz; }");
        p.brace_group().unwrap_err();
    }

    #[test]
    fn test_brace_group_invalid_quoted() {
        let cmds = [
            "'{' foo\nbar; baz; }",
            "{ foo\nbar; baz; '}'",
            "\"{\" foo\nbar; baz; }",
            "{ foo\nbar; baz; \"}\"",
        ];

        for c in cmds.into_iter() {
            match make_parser(c).brace_group() {
                Err(_) => {},
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            }
        }
    }

    #[test]
    fn test_brace_group_invalid_missing_body() {
        let mut p = make_parser("{\n}");
        p.loop_command().unwrap_err();
    }

    #[test]
    fn test_subshell_valid() {
        let mut p = make_parser("( foo\nbar; baz; )");
        let correct = vec!(cmd_unboxed("foo"), cmd_unboxed("bar"), cmd_unboxed("baz"));
        assert_eq!(correct, p.subshell().unwrap());
    }

    #[test]
    fn test_subshell_valid_separator_not_needed() {
        let mut p = make_parser("( foo )");
        let correct = vec!(cmd_unboxed("foo"));
        assert_eq!(correct, p.subshell().unwrap());
    }

    #[test]
    fn test_subshell_space_between_parens_not_needed() {
        let mut p = make_parser("(foo )");
        p.subshell().unwrap();
        let mut p = make_parser("( foo)");
        p.subshell().unwrap();
        let mut p = make_parser("(foo)");
        p.subshell().unwrap();
    }

    #[test]
    fn test_subshell_invalid_missing_keyword() {
        let mut p = make_parser("( foo\nbar; baz");
        p.subshell().unwrap_err();
        let mut p = make_parser("foo\nbar; baz; )");
        p.subshell().unwrap_err();
    }

    #[test]
    fn test_subshell_invalid_quoted() {
        let cmds = [
            "'(' foo\nbar; baz; )",
            "( foo\nbar; baz; ')'",
            "\"(\" foo\nbar; baz; )",
            "( foo\nbar; baz; \")\"",
        ];

        for c in cmds.into_iter() {
            match make_parser(c).subshell() {
                Err(_) => {},
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            }
        }
    }

    #[test]
    fn test_subshell_invalid_missing_body() {
        let mut p = make_parser("(\n)");
        p.loop_command().unwrap_err();
        let mut p = make_parser("()");
        p.loop_command().unwrap_err();
    }

    #[test]
    fn test_loop_command_while_valid() {
        let mut p = make_parser("while guard1; guard2; do foo\nbar; baz; done");
        let (until, guards, cmds) = p.loop_command().unwrap();

        let correct_guards = vec!(cmd_unboxed("guard1"), cmd_unboxed("guard2"));
        let correct_cmds = vec!(cmd_unboxed("foo"), cmd_unboxed("bar"), cmd_unboxed("baz"));

        assert_eq!(until, builder::LoopKind::While);
        assert_eq!(correct_guards, guards);
        assert_eq!(correct_cmds, cmds);
    }

    #[test]
    fn test_loop_command_until_valid() {
        let mut p = make_parser("until guard1\n guard2\n do foo\nbar; baz; done");
        let (until, guards, cmds) = p.loop_command().unwrap();

        let correct_guards = vec!(cmd_unboxed("guard1"), cmd_unboxed("guard2"));
        let correct_cmds = vec!(cmd_unboxed("foo"), cmd_unboxed("bar"), cmd_unboxed("baz"));

        assert_eq!(until, builder::LoopKind::Until);
        assert_eq!(correct_guards, guards);
        assert_eq!(correct_cmds, cmds);
    }

    #[test]
    fn test_loop_command_invalid_missing_separator() {
        let mut p = make_parser("while guard do foo\nbar; baz; done");
        p.loop_command().unwrap_err();
        let mut p = make_parser("while guard; do foo\nbar; baz done");
        p.loop_command().unwrap_err();
    }

    #[test]
    fn test_loop_command_invalid_missing_keyword() {
        let mut p = make_parser("guard; do foo\nbar; baz; done");
        p.loop_command().unwrap_err();
    }

    #[test]
    fn test_loop_command_invalid_missing_guard() {
        // With command separator between loop and do keywords
        let mut p = make_parser("while; do foo\nbar; baz; done");
        p.loop_command().unwrap_err();
        let mut p = make_parser("until; do foo\nbar; baz; done");
        p.loop_command().unwrap_err();

        // Without command separator between loop and do keywords
        let mut p = make_parser("while do foo\nbar; baz; done");
        p.loop_command().unwrap_err();
        let mut p = make_parser("until do foo\nbar; baz; done");
        p.loop_command().unwrap_err();
    }

    #[test]
    fn test_loop_command_invalid_quoted() {
        let cmds = [
            "'while' guard do foo\nbar; baz; done",
            "'until' guard do foo\nbar; baz; done",
            "\"while\" guard do foo\nbar; baz; done",
            "\"until\" guard do foo\nbar; baz; done",
        ];

        for c in cmds.into_iter() {
            match make_parser(c).loop_command() {
                Err(_) => {},
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            }
        }
    }

    #[test]
    fn test_loop_command_invalid_concat() {
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("whi")),
            Token::Literal(String::from("le")),
            Token::Newline,
            Token::Literal(String::from("guard")),
            Token::Newline,
            Token::Literal(String::from("do")),
            Token::Literal(String::from("foo")),
            Token::Newline,
            Token::Literal(String::from("done")),
        ));
        p.loop_command().unwrap_err();
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("un")),
            Token::Literal(String::from("til")),
            Token::Newline,
            Token::Literal(String::from("guard")),
            Token::Newline,
            Token::Literal(String::from("do")),
            Token::Literal(String::from("foo")),
            Token::Newline,
            Token::Literal(String::from("done")),
        ));
        p.loop_command().unwrap_err();
    }

    #[test]
    fn test_loop_command_should_recognize_literals_and_names() {
        for kw in vec!(
            Token::Literal(String::from("while")),
            Token::Name(String::from("while")),
            Token::Literal(String::from("until")),
            Token::Name(String::from("until")))
        {
            let mut p = make_parser_from_tokens(vec!(
                kw,
                Token::Newline,
                Token::Literal(String::from("guard")),
                Token::Newline,
                Token::Literal(String::from("do")),
                Token::Newline,
                Token::Literal(String::from("foo")),
                Token::Newline,
                Token::Literal(String::from("done")),
            ));
            p.loop_command().unwrap();
        }
    }

    #[test]
    fn test_if_command_valid_with_else() {
        let mut p = make_parser("if guard1 <in; >out guard2; then body1 >|clob\n elif guard3; then body2 2>>app; else else; fi");
        let (branches, els) = p.if_command().unwrap();
        if let [(ref cond1, ref body1), (ref cond2, ref body2)] = &branches[..] {
            if let ([Simple(ref guard1), Simple(ref guard2)], [Simple(ref body1)],
                    [Simple(ref guard3)], [Simple(ref body2)]) = (&cond1[..], &body1[..], &cond2[..], &body2[..])
            {
                assert_eq!(guard1.cmd.as_ref().unwrap(), &Word::Literal(String::from("guard1")));
                assert_eq!(guard2.cmd.as_ref().unwrap(), &Word::Literal(String::from("guard2")));
                assert_eq!(guard3.cmd.as_ref().unwrap(), &Word::Literal(String::from("guard3")));
                assert_eq!(body1.cmd.as_ref().unwrap(),  &Word::Literal(String::from("body1")));
                assert_eq!(body2.cmd.as_ref().unwrap(),  &Word::Literal(String::from("body2")));

                assert_eq!(guard1.io, vec!(Redirect::Read(None, Word::Literal(String::from("in")))));
                assert_eq!(guard2.io, vec!(Redirect::Write(None, Word::Literal(String::from("out")))));
                assert_eq!(body1.io,  vec!(Redirect::Clobber(None, Word::Literal(String::from("clob")))));
                assert_eq!(body2.io,  vec!(Redirect::Append(Some(Word::Literal(String::from("2"))), Word::Literal(String::from("app")))));

                let els = els.as_ref().unwrap();
                assert_eq!(els.len(), 1);
                if let Simple(ref els) = els[0] {
                    assert_eq!(els.cmd.as_ref().unwrap(), &Word::Literal(String::from("else")));
                    return;
                }
            }
        }

        panic!("Incorrect parse result for Parse::if_command:\n{:#?}", (branches, els));
    }

    #[test]
    fn test_if_command_valid_without_else() {
        let mut p = make_parser("if guard1 <in; >out guard2; then body1 >|clob\n elif guard3; then body2 2>>app; fi");
        let (branches, els) = p.if_command().unwrap();
        if let [(ref cond1, ref body1), (ref cond2, ref body2)] = &branches[..] {
            if let ([Simple(ref guard1), Simple(ref guard2)], [Simple(ref body1)],
                    [Simple(ref guard3)], [Simple(ref body2)]) = (&cond1[..], &body1[..], &cond2[..], &body2[..])
            {
                assert_eq!(guard1.cmd.as_ref().unwrap(), &Word::Literal(String::from("guard1")));
                assert_eq!(guard2.cmd.as_ref().unwrap(), &Word::Literal(String::from("guard2")));
                assert_eq!(guard3.cmd.as_ref().unwrap(), &Word::Literal(String::from("guard3")));
                assert_eq!(body1.cmd.as_ref().unwrap(),  &Word::Literal(String::from("body1")));
                assert_eq!(body2.cmd.as_ref().unwrap(),  &Word::Literal(String::from("body2")));

                assert_eq!(guard1.io, vec!(Redirect::Read(None, Word::Literal(String::from("in")))));
                assert_eq!(guard2.io, vec!(Redirect::Write(None, Word::Literal(String::from("out")))));
                assert_eq!(body1.io,  vec!(Redirect::Clobber(None, Word::Literal(String::from("clob")))));
                assert_eq!(body2.io,  vec!(Redirect::Append(Some(Word::Literal(String::from("2"))), Word::Literal(String::from("app")))));

                assert_eq!(els, None);
                return;
            }
        }

        panic!("Incorrect parse result for Parse::if_command:\n{:#?}", (branches, els));
    }

    #[test]
    fn test_if_command_invalid_body_can_be_empty() {
        let mut p = make_parser("if guard; then; else else part; fi");
        p.if_command().unwrap_err();
    }

    #[test]
    fn test_if_command_invalid_else_part_can_be_empty() {
        let mut p = make_parser("if guard; then body; else; fi");
        p.if_command().unwrap_err();
    }

    #[test]
    fn test_if_command_invalid_missing_separator() {
        let mut p = make_parser("if guard; then body1; elif guard2; then body2; else else fi");
        p.if_command().unwrap_err();
    }

    #[test]
    fn test_if_command_invalid_missing_keyword() {
        let mut p = make_parser("guard1; then body1; elif guard2; then body2; else else; fi");
        p.if_command().unwrap_err();
        let mut p = make_parser("if guard1; then body1; elif guard2; then body2; else else;");
        p.if_command().unwrap_err();
    }

    #[test]
    fn test_if_command_invalid_missing_guard() {
        let mut p = make_parser("if; then body1; elif guard2; then body2; else else; fi");
        p.if_command().unwrap_err();
    }

    #[test]
    fn test_if_command_invalid_missing_body() {
        let mut p = make_parser("if guard; then; elif guard2; then body2; else else; fi");
        p.if_command().unwrap_err();
        let mut p = make_parser("if guard1; then body1; elif; then body2; else else; fi");
        p.if_command().unwrap_err();
        let mut p = make_parser("if guard1; then body1; elif guard2; then body2; else; fi");
        p.if_command().unwrap_err();
    }

    #[test]
    fn test_if_command_invalid_quoted() {
        let cmds = [
            "'if' guard1; then body1; elif guard2; then body2; else else; fi",
            "if guard1; then body1; elif guard2; then body2; else else; 'fi'",
            "\"if\" guard1; then body1; elif guard2; then body2; else else; fi",
            "if guard1; then body1; elif guard2; then body2; else else; \"fi\"",
        ];

        for c in cmds.into_iter() {
            match make_parser(c).if_command() {
                Err(_) => {},
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            }
        }
    }

    #[test]
    fn test_if_command_invalid_concat() {
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("i")), Token::Literal(String::from("f")),
            Token::Newline, Token::Literal(String::from("guard1")), Token::Newline,
            Token::Literal(String::from("then")),
            Token::Newline, Token::Literal(String::from("body1")), Token::Newline,
            Token::Literal(String::from("elif")),
            Token::Newline, Token::Literal(String::from("guard2")), Token::Newline,
            Token::Literal(String::from("then")),
            Token::Newline, Token::Literal(String::from("body2")), Token::Newline,
            Token::Literal(String::from("else")),
            Token::Newline, Token::Literal(String::from("else part")), Token::Newline,
            Token::Literal(String::from("fi")),
        ));
        p.if_command().unwrap_err();

        // Splitting up `then`, `elif`, and `else` tokens makes them
        // get interpreted as arguments, so an explicit error may not be raised
        // although the command will be malformed

        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("if")),
            Token::Newline, Token::Literal(String::from("guard1")), Token::Newline,
            Token::Literal(String::from("then")),
            Token::Newline, Token::Literal(String::from("body1")), Token::Newline,
            Token::Literal(String::from("elif")),
            Token::Newline, Token::Literal(String::from("guard2")), Token::Newline,
            Token::Literal(String::from("then")),
            Token::Newline, Token::Literal(String::from("body2")), Token::Newline,
            Token::Literal(String::from("else")),
            Token::Newline, Token::Literal(String::from("else part")), Token::Newline,
            Token::Literal(String::from("f")), Token::Literal(String::from("i")),
        ));
        p.if_command().unwrap_err();
    }

    #[test]
    fn test_if_command_should_recognize_literals_and_names() {
        for if_tok in vec!(Token::Literal(String::from("if")), Token::Name(String::from("if"))) {
            for then_tok in vec!(Token::Literal(String::from("then")), Token::Name(String::from("then"))) {
                for elif_tok in vec!(Token::Literal(String::from("elif")), Token::Name(String::from("elif"))) {
                    for else_tok in vec!(Token::Literal(String::from("else")), Token::Name(String::from("else"))) {
                        for fi_tok in vec!(Token::Literal(String::from("fi")), Token::Name(String::from("fi"))) {
                            let mut p = make_parser_from_tokens(vec!(
                                    if_tok.clone(),
                                    Token::Whitespace(String::from(" ")),

                                    Token::Literal(String::from("guard1")),
                                    Token::Newline,

                                    then_tok.clone(),
                                    Token::Newline,
                                    Token::Literal(String::from("body1")),

                                    elif_tok.clone(),
                                    Token::Whitespace(String::from(" ")),

                                    Token::Literal(String::from("guard2")),
                                    Token::Newline,
                                    then_tok.clone(),
                                    Token::Whitespace(String::from(" ")),
                                    Token::Literal(String::from("body2")),

                                    else_tok.clone(),
                                    Token::Whitespace(String::from(" ")),

                                    Token::Whitespace(String::from(" ")),
                                    Token::Literal(String::from("else part")),
                                    Token::Newline,

                                    fi_tok,
                            ));
                            p.if_command().unwrap();
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_braces_literal_unless_brace_group_expected() {
        let source = "echo {} } {";
        let mut p = make_parser(source);
        assert_eq!(p.word().unwrap().unwrap(), Word::Literal(String::from("echo")));
        assert_eq!(p.word().unwrap().unwrap(), Word::Concat(vec!(
                    Word::Literal(String::from("{")),
                    Word::Literal(String::from("}")),
        )));
        assert_eq!(p.word().unwrap().unwrap(), Word::Literal(String::from("}")));
        assert_eq!(p.word().unwrap().unwrap(), Word::Literal(String::from("{")));

        let mut p = make_parser(source);
        if let Simple(_) = p.complete_command().unwrap().unwrap() {
            return;
        } else {
            panic!("Parsing of {} did not yield a simple command", source);
        }
    }

    #[test]
    fn test_for_command_valid_with_words() {
        let mut p = make_parser("for var #comment1\nin one two three\n#comment2\n\ndo echo $var; done");
        let (var, var_comment, words, word_comment, body) = p.for_command().unwrap();
        assert_eq!(var, "var");
        assert_eq!(var_comment, vec!(Newline(Some(String::from("#comment1")))));
        assert_eq!(words.unwrap(), vec!(
            Word::Literal(String::from("one")),
            Word::Literal(String::from("two")),
            Word::Literal(String::from("three")),
        ));
        assert_eq!(word_comment, Some(vec!(
            Newline(None),
            Newline(Some(String::from("#comment2"))),
            Newline(None),
        )));

        if let [Simple(ref echo)] = &body[..] {
            assert_eq!(echo.cmd.as_ref().unwrap(), &Word::Literal(String::from("echo")));
            assert_eq!(echo.args, vec!(Word::Param(Parameter::Var(String::from("var")))));
            return;
        }

        panic!("Incorrect parse result for body from Parse::for_command:\n{:#?}", body);
    }

    #[test]
    fn test_for_command_valid_without_words() {
        let mut p = make_parser("for var #comment\ndo echo $var; done");
        let (var, var_comment, words, word_comment, body) = p.for_command().unwrap();
        assert_eq!(var, "var");
        assert_eq!(var_comment, vec!(Newline(Some(String::from("#comment")))));
        assert_eq!(words, None);
        assert_eq!(word_comment, None);

        if let [Simple(ref echo)] = &body[..] {
            assert_eq!(echo.cmd.as_ref().unwrap(), &Word::Literal(String::from("echo")));
            assert_eq!(echo.args, vec!(Word::Param(Parameter::Var(String::from("var")))));
            return;
        }

        panic!("Incorrect parse result for body from Parse::for_command:\n{:#?}", body);
    }

    #[test]
    fn test_for_command_valid_with_in_but_no_words_with_separator() {
        let mut p = make_parser("for var in\ndo echo $var; done");
        p.for_command().unwrap();
        let mut p = make_parser("for var in;do echo $var; done");
        p.for_command().unwrap();
    }

    #[test]
    fn test_for_command_valid_with_separator() {
        let mut p = make_parser("for var in one two three\ndo echo $var; done");
        p.for_command().unwrap();
        let mut p = make_parser("for var in one two three;do echo $var; done");
        p.for_command().unwrap();
    }

    #[test]
    fn test_for_command_invalid_with_in_no_words_no_with_separator() {
        let mut p = make_parser("for var in do echo $var; done");
        p.for_command().unwrap_err();
    }

    #[test]
    fn test_for_command_invalid_missing_separator() {
        let mut p = make_parser("for var in one two three do echo $var; done");
        p.for_command().unwrap_err();
    }

    #[test]
    fn test_for_command_invalid_amp_not_valid_separator() {
        let mut p = make_parser("for var in one two three& do echo $var; done");
        p.for_command().unwrap_err();
    }

    #[test]
    fn test_for_command_invalid_missing_keyword() {
        let mut p = make_parser("var in one two three\ndo echo $var; done");
        p.for_command().unwrap_err();
    }

    #[test]
    fn test_for_command_invalid_missing_var() {
        let mut p = make_parser("for in one two three\ndo echo $var; done");
        p.for_command().unwrap_err();
    }

    #[test]
    fn test_for_command_invalid_missing_body() {
        let mut p = make_parser("for var in one two three\n");
        p.for_command().unwrap_err();
    }

    #[test]
    fn test_for_command_invalid_quoted() {
        let cmds = [
            "'for' var in one two three\ndo echo $var; done",
            "for var 'in' one two three\ndo echo $var; done",
            "\"for\" var in one two three\ndo echo $var; done",
            "for var \"in\" one two three\ndo echo $var; done",
        ];

        for c in cmds.into_iter() {
            match make_parser(c).for_command() {
                Err(_) => {},
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            }
        }
    }

    #[test]
    fn test_for_command_invalid_var_must_be_name() {
        let mut p = make_parser("for 123var in one two three\ndo echo $var; done");
        p.for_command().unwrap_err();
        let mut p = make_parser("for 'var' in one two three\ndo echo $var; done");
        p.for_command().unwrap_err();
        let mut p = make_parser("for \"var\" in one two three\ndo echo $var; done");
        p.for_command().unwrap_err();
        let mut p = make_parser("for var&*^ in one two three\ndo echo $var; done");
        p.for_command().unwrap_err();
    }

    #[test]
    fn test_for_command_invalid_concat() {
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("fo")), Token::Literal(String::from("r")),
            Token::Whitespace(String::from(" ")), Token::Name(String::from("var")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("in")),
            Token::Literal(String::from("one")), Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("two")), Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("three")), Token::Whitespace(String::from(" ")),
            Token::Newline,

            Token::Literal(String::from("do")), Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("echo")), Token::Whitespace(String::from(" ")),
            Token::Dollar, Token::Literal(String::from("var")),
            Token::Newline,
            Token::Literal(String::from("done")),
        ));
        p.for_command().unwrap_err();

        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("for")),
            Token::Whitespace(String::from(" ")), Token::Name(String::from("var")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("i")), Token::Literal(String::from("n")),
            Token::Literal(String::from("one")), Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("two")), Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("three")), Token::Whitespace(String::from(" ")),
            Token::Newline,

            Token::Literal(String::from("do")), Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("echo")), Token::Whitespace(String::from(" ")),
            Token::Dollar, Token::Literal(String::from("var")),
            Token::Newline,
            Token::Literal(String::from("done")),
        ));
        p.for_command().unwrap_err();
    }

    #[test]
    fn test_for_command_should_recognize_literals_and_names() {
        for for_tok in vec!(Token::Literal(String::from("for")), Token::Name(String::from("for"))) {
            for in_tok in vec!(Token::Literal(String::from("in")), Token::Name(String::from("in"))) {
                let mut p = make_parser_from_tokens(vec!(
                    for_tok.clone(),
                    Token::Whitespace(String::from(" ")),

                    Token::Name(String::from("var")),
                    Token::Whitespace(String::from(" ")),

                    in_tok.clone(),
                    Token::Whitespace(String::from(" ")),
                    Token::Literal(String::from("one")),
                    Token::Whitespace(String::from(" ")),
                    Token::Literal(String::from("two")),
                    Token::Whitespace(String::from(" ")),
                    Token::Literal(String::from("three")),
                    Token::Whitespace(String::from(" ")),
                    Token::Newline,

                    Token::Literal(String::from("do")),
                    Token::Whitespace(String::from(" ")),

                    Token::Literal(String::from("echo")),
                    Token::Whitespace(String::from(" ")),
                    Token::Dollar,
                    Token::Name(String::from("var")),
                    Token::Newline,

                    Token::Literal(String::from("done")),
                ));
                p.for_command().unwrap();
            }
        }
    }

    #[test]
    fn test_function_declaration_valid() {
        let correct = Command::Function(
            String::from("foo"),
            Box::new(Compound(
                Box::new(CompoundCommand::Brace(vec!(Simple(Box::new(SimpleCommand {
                    cmd: Some(Word::Literal(String::from("echo"))),
                    args: vec!(Word::Literal(String::from("body"))),
                    vars: vec!(),
                    io: vec!(),
                }))))),
                vec!()
            ))
        );

        assert_eq!(correct, make_parser("function foo()      { echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo ()     { echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo (    ) { echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo(    )  { echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo        { echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo()               { echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo ()              { echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo (    )          { echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo(    )           { echo body; }").function_declaration().unwrap());

        assert_eq!(correct, make_parser("function foo()     \n{ echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo ()    \n{ echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo (    )\n{ echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo(    ) \n{ echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo       \n{ echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo()              \n{ echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo ()             \n{ echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo (    )         \n{ echo body; }").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo(    )          \n{ echo body; }").function_declaration().unwrap());
    }

    #[test]
    fn test_function_declaration_valid_body_need_not_be_a_compound_command() {
        let correct = Command::Function(
            String::from("foo"),
            Box::new(Simple(Box::new(SimpleCommand {
                cmd: Some(Word::Literal(String::from("echo"))),
                args: vec!(Word::Literal(String::from("body"))),
                vars: vec!(),
                io: vec!(),
            })))
        );

        assert_eq!(correct, make_parser("function foo()      echo body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo ()     echo body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo (    ) echo body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo(    )  echo body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo        echo body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo()               echo body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo ()              echo body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo (    )          echo body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo(    )           echo body;").function_declaration().unwrap());

        assert_eq!(correct, make_parser("function foo()     \necho body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo ()    \necho body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo (    )\necho body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo(    ) \necho body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo       \necho body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo()              \necho body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo ()             \necho body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo (    )         \necho body;").function_declaration().unwrap());
        assert_eq!(correct, make_parser("foo(    )          \necho body;").function_declaration().unwrap());
    }

    #[test]
    fn test_function_declaration_invalid_newline_in_declaration() {
        let mut p = make_parser("function\nname() { echo body; }");
        p.function_declaration().unwrap_err();
        let mut p = make_parser("function name\n() { echo body; }");
        p.function_declaration().unwrap_err();
    }

    #[test]
    fn test_function_declaration_invalid_missing_space_after_fn_keyword_and_no_parens() {
        let mut p = make_parser("functionname { echo body; }");
        p.function_declaration().unwrap_err();
    }

    #[test]
    fn test_function_declaration_invalid_missing_fn_keyword_and_parens() {
        let mut p = make_parser("name { echo body; }");
        p.function_declaration().unwrap_err();
    }

    #[test]
    fn test_function_declaration_invalid_missing_space_after_name_no_parens() {
        let mut p = make_parser("function name{ echo body; }");
        p.function_declaration().unwrap_err();
        let mut p = make_parser("function name( echo body; )");
        p.function_declaration().unwrap_err();
    }

    #[test]
    fn test_function_declaration_invalid_missing_name() {
        let mut p = make_parser("function { echo body; }");
        p.function_declaration().unwrap_err();
        let mut p = make_parser("function () { echo body; }");
        p.function_declaration().unwrap_err();
        let mut p = make_parser("() { echo body; }");
        p.function_declaration().unwrap_err();
    }

    #[test]
    fn test_function_declaration_invalid_missing_body() {
        let mut p = make_parser("function name");
        p.function_declaration().unwrap_err();
        let mut p = make_parser("function name()");
        p.function_declaration().unwrap_err();
        let mut p = make_parser("name()");
        p.function_declaration().unwrap_err();
    }

    #[test]
    fn test_function_declaration_invalid_quoted() {
        let cmds = [
            "'function' name { echo body; }",
            "function 'name'() { echo body; }",
            "name'()' { echo body; }",
            "\"function\" name { echo body; }",
            "function \"name\"() { echo body; }",
            "name\"()\" { echo body; }",
        ];

        for c in cmds.into_iter() {
            match make_parser(c).function_declaration() {
                Err(_) => {},
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            }
        }
    }

    #[test]
    fn test_function_declaration_invalid_fn_must_be_name() {
        let mut p = make_parser("function 123fn { echo body; }");
        p.function_declaration().unwrap_err();
        let mut p = make_parser("function 123fn() { echo body; }");
        p.function_declaration().unwrap_err();
        let mut p = make_parser("123fn() { echo body; }");
        p.function_declaration().unwrap_err();
    }

    #[test]
    fn test_function_declaration_invalid_fn_name_must_be_name_token() {
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("function")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("fn_name")),
            Token::Whitespace(String::from(" ")),

            Token::ParenOpen, Token::ParenClose,
            Token::Whitespace(String::from(" ")),
            Token::CurlyOpen,
            Token::Literal(String::from("echo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("fn body")),
            Token::Semi,
            Token::CurlyClose,
        ));
        p.function_declaration().unwrap_err();

        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("function")),
            Token::Whitespace(String::from(" ")),

            Token::Name(String::from("fn_name")),
            Token::Whitespace(String::from(" ")),

            Token::ParenOpen, Token::ParenClose,
            Token::Whitespace(String::from(" ")),
            Token::CurlyOpen,
            Token::Literal(String::from("echo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("fn body")),
            Token::Semi,
            Token::CurlyClose,
        ));
        p.function_declaration().unwrap();
    }

    #[test]
    fn test_function_declaration_invalid_concat() {
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("func")), Token::Literal(String::from("tion")),
            Token::Whitespace(String::from(" ")),

            Token::Name(String::from("fn_name")),
            Token::Whitespace(String::from(" ")),

            Token::ParenOpen, Token::ParenClose,
            Token::Whitespace(String::from(" ")),
            Token::CurlyOpen,
            Token::Literal(String::from("echo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("fn body")),
            Token::Semi,
            Token::CurlyClose,
        ));
        p.function_declaration().unwrap_err();
    }

    #[test]
    fn test_function_declaration_should_recognize_literals_and_names_for_fn_keyword() {
        for fn_tok in vec!(Token::Literal(String::from("function")), Token::Name(String::from("function"))) {
            let mut p = make_parser_from_tokens(vec!(
                fn_tok,
                Token::Whitespace(String::from(" ")),

                Token::Name(String::from("fn_name")),
                Token::Whitespace(String::from(" ")),

                Token::ParenOpen, Token::ParenClose,
                Token::Whitespace(String::from(" ")),
                Token::CurlyOpen,
                Token::Literal(String::from("echo")),
                Token::Whitespace(String::from(" ")),
                Token::Literal(String::from("fn body")),
                Token::Semi,
                Token::CurlyClose,
            ));
            p.function_declaration().unwrap();
        }
    }

    #[test]
    fn test_case_command_valid() {
        let correct_word = Word::Literal(String::from("foo"));
        let correct_branches = vec!(
            (
                (vec!(), vec!(Word::Literal(String::from("hello")), Word::Literal(String::from("goodbye"))), vec!()),
                vec!(Simple(Box::new(SimpleCommand {
                    cmd: Some(Word::Literal(String::from("echo"))),
                    args: vec!(Word::Literal(String::from("greeting"))),
                    io: vec!(),
                    vars: vec!(),
                }))),
            ),
            (
                (vec!(), vec!(Word::Literal(String::from("world"))), vec!()),
                vec!(Simple(Box::new(SimpleCommand {
                    cmd: Some(Word::Literal(String::from("echo"))),
                    args: vec!(Word::Literal(String::from("noun"))),
                    io: vec!(),
                    vars: vec!(),
                }))),
            ),
        );

        let correct = (correct_word, vec!(), correct_branches, vec!());

        // `(` before pattern is optional
        assert_eq!(correct, make_parser("case foo in  hello | goodbye) echo greeting;;  world) echo noun;; esac").case_command().unwrap());
        assert_eq!(correct, make_parser("case foo in (hello | goodbye) echo greeting;;  world) echo noun;; esac").case_command().unwrap());
        assert_eq!(correct, make_parser("case foo in (hello | goodbye) echo greeting;; (world) echo noun;; esac").case_command().unwrap());

        // Final `;;` is optional as long as last command is complete
        assert_eq!(correct, make_parser("case foo in hello | goodbye) echo greeting;; world) echo noun\nesac").case_command().unwrap());
        assert_eq!(correct, make_parser("case foo in hello | goodbye) echo greeting;; world) echo noun; esac").case_command().unwrap());
    }

    #[test]
    fn test_case_command_valid_with_comments() {
        let correct_word = Word::Literal(String::from("foo"));
        let correct_post_word = vec!(Newline(Some(String::from("#post_word_a"))), Newline(Some(String::from("#post_word_b"))));
        let correct_branches = vec!(
            (
                (
                    vec!(Newline(Some(String::from("#pre_pat_1a"))), Newline(Some(String::from("#pre_pat_1b")))),
                    vec!(Word::Literal(String::from("hello")), Word::Literal(String::from("goodbye"))),
                    vec!(Newline(Some(String::from("#post_pat_1a"))), Newline(Some(String::from("#post_pat_1b")))),
                ),
                vec!(Simple(Box::new(SimpleCommand {
                    cmd: Some(Word::Literal(String::from("echo"))),
                    args: vec!(Word::Literal(String::from("greeting"))),
                    io: vec!(),
                    vars: vec!(),
                }))),
            ),
            (
                (
                    vec!(Newline(Some(String::from("#pre_pat_2a"))), Newline(Some(String::from("#pre_pat_2b")))),
                    vec!(Word::Literal(String::from("world"))),
                    vec!(Newline(Some(String::from("#post_pat_2a"))), Newline(Some(String::from("#post_pat_2b")))),
                ),
                vec!(Simple(Box::new(SimpleCommand {
                    cmd: Some(Word::Literal(String::from("echo"))),
                    args: vec!(Word::Literal(String::from("noun"))),
                    io: vec!(),
                    vars: vec!(),
                }))),
            ),
        );
        let correct_post_branch = vec!(Newline(Some(String::from("#post_branch_a"))), Newline(Some(String::from("#post_branch_b"))));

        let correct = (correct_word, correct_post_word, correct_branches, correct_post_branch);

        // Various newlines and comments allowed within the command
        let cmd =
            "case foo #post_word_a
            #post_word_b
            in #pre_pat_1a
            #pre_pat_1b
            (hello | goodbye) #post_pat_1a
            #post_pat_1b
            echo greeting #post_cmd
            #post_cmd
            ;; #pre_pat_2a
            #pre_pat_2b
            world) #post_pat_2a
            #post_pat_2b
            echo noun;; #post_branch_a
            #post_branch_b
            esac";

        assert_eq!(correct, make_parser(cmd).case_command().unwrap());
    }

    #[test]
    fn test_case_command_valid_with_comments_no_body() {
        let correct_word = Word::Literal(String::from("foo"));
        let correct_post_word = vec!(Newline(Some(String::from("#post_word_a"))), Newline(Some(String::from("#post_word_b"))));
        let correct_branches = vec!();
        let correct_post_branch = vec!(Newline(Some(String::from("#one"))), Newline(Some(String::from("#two"))), Newline(Some(String::from("#three"))));

        let correct = (correct_word, correct_post_word, correct_branches, correct_post_branch);

        // Various newlines and comments allowed within the command
        let cmd =
            "case foo #post_word_a
            #post_word_b
            in #one
            #two
            #three
            esac";

        assert_eq!(correct, make_parser(cmd).case_command().unwrap());
    }

    #[test]
    fn test_case_command_word_need_not_be_simple_literal() {
        let mut p = make_parser("case 'foo'bar$$ in foo) echo foo;; esac");
        p.case_command().unwrap();
    }

    #[test]
    fn test_case_command_valid_with_no_arms() {
        let mut p = make_parser("case foo in esac");
        p.case_command().unwrap();
    }

    #[test]
    fn test_case_command_valid_branch_with_no_command() {
        let mut p = make_parser("case foo in pat)\nesac");
        p.case_command().unwrap();
        let mut p = make_parser("case foo in pat);;esac");
        p.case_command().unwrap();
    }

    #[test]
    fn test_case_command_invalid_missing_keyword() {
        let mut p = make_parser("foo in foo) echo foo;; bar) echo bar;; esac");
        p.case_command().unwrap_err();
        let mut p = make_parser("case foo foo) echo foo;; bar) echo bar;; esac");
        p.case_command().unwrap_err();
        let mut p = make_parser("case foo in foo) echo foo;; bar) echo bar;;");
        p.case_command().unwrap_err();
    }

    #[test]
    fn test_case_command_invalid_missing_word() {
        let mut p = make_parser("case in foo) echo foo;; bar) echo bar;; esac");
        p.case_command().unwrap_err();
    }

    #[test]
    fn test_case_command_invalid_quoted() {
        let cmds = [
            "'case' foo in foo) echo foo;; bar) echo bar;; esac",
            "case foo 'in' foo) echo foo;; bar) echo bar;; esac",
            "case foo in foo) echo foo;; bar')' echo bar;; 'esac'",
            "\"case\" foo in foo) echo foo;; bar) echo bar;; esac",
            "case foo \"in\" foo) echo foo;; bar) echo bar;; esac",
            "case foo in foo) echo foo;; bar\")\" echo bar;; 'esac'",
        ];

        for c in cmds.into_iter() {
            match make_parser(c).case_command() {
                Err(_) => {},
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            }
        }
    }

    #[test]
    fn test_case_command_invalid_newline_after_case() {
        let mut p = make_parser("case\nfoo in foo) echo foo;; bar) echo bar;; esac");
        p.case_command().unwrap_err();
    }

    #[test]
    fn test_case_command_invalid_concat() {
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("ca")), Token::Literal(String::from("se")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("foo")),
            Token::Literal(String::from("bar")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("in")),
            Token::Literal(String::from("foo")),
            Token::ParenClose,
            Token::Newline,
            Token::Literal(String::from("echo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("foo")),
            Token::Newline,
            Token::Newline,
            Token::DSemi,

            Token::Literal(String::from("esac")),
        ));
        p.case_command().unwrap_err();

        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("case")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("foo")),
            Token::Literal(String::from("bar")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("i")), Token::Literal(String::from("n")),
            Token::Literal(String::from("foo")),
            Token::ParenClose,
            Token::Newline,
            Token::Literal(String::from("echo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("foo")),
            Token::Newline,
            Token::Newline,
            Token::DSemi,

            Token::Literal(String::from("esac")),
        ));
        p.case_command().unwrap_err();

        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("case")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("foo")),
            Token::Literal(String::from("bar")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("in")),
            Token::Literal(String::from("foo")),
            Token::ParenClose,
            Token::Newline,
            Token::Literal(String::from("echo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("foo")),
            Token::Newline,
            Token::Newline,
            Token::DSemi,

            Token::Literal(String::from("es")), Token::Literal(String::from("ac")),
        ));
        p.case_command().unwrap_err();
    }

    #[test]
    fn test_case_command_should_recognize_literals_and_names() {
        let case_str = String::from("case");
        let in_str   = String::from("in");
        let esac_str = String::from("esac");
        for case_tok in vec!(Token::Literal(case_str.clone()), Token::Name(case_str.clone())) {
            for in_tok in vec!(Token::Literal(in_str.clone()), Token::Name(in_str.clone())) {
                for esac_tok in vec!(Token::Literal(esac_str.clone()), Token::Name(esac_str.clone())) {
                    let mut p = make_parser_from_tokens(vec!(
                        case_tok.clone(),
                        Token::Whitespace(String::from(" ")),

                        Token::Literal(String::from("foo")),
                        Token::Literal(String::from("bar")),

                        Token::Whitespace(String::from(" ")),
                        in_tok.clone(),
                        Token::Whitespace(String::from(" ")),

                        Token::Literal(String::from("foo")),
                        Token::ParenClose,
                        Token::Newline,
                        Token::Literal(String::from("echo")),
                        Token::Whitespace(String::from(" ")),
                        Token::Literal(String::from("foo")),
                        Token::Newline,
                        Token::Newline,
                        Token::DSemi,

                        esac_tok
                    ));
                    p.case_command().unwrap();
                }
            }
        }
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_brace() {
        let correct = Compound(Box::new(Brace(vec!(cmd_unboxed("foo")))), vec!());
        assert_eq!(correct, make_parser("{ foo; }").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_subshell() {
        let commands = [
            "(foo)",
            "( foo)",
        ];

        let correct = Compound(Box::new(Subshell(vec!(cmd_unboxed("foo")))), vec!());

        for cmd in commands.iter() {
            match make_parser(cmd).compound_command() {
                Ok(ref result) if result == &correct => {},
                Ok(result) => panic!("Parsed \"{}\" as an unexpected command type:\n{:#?}", cmd, result),
                Err(err) => panic!("Failed to parse \"{}\": {}", cmd, err),
            }
        }
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_while() {
        let correct = Compound(Box::new(While(vec!(cmd_unboxed("guard")), vec!(cmd_unboxed("foo")))), vec!());
        assert_eq!(correct, make_parser("while guard; do foo; done").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_until() {
        let correct = Compound(Box::new(Until(vec!(cmd_unboxed("guard")), vec!(cmd_unboxed("foo")))), vec!());
        assert_eq!(correct, make_parser("until guard; do foo; done").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_for() {
        let correct = Compound(Box::new(For(String::from("var"), Some(vec!()), vec!(cmd_unboxed("foo")))), vec!());
        assert_eq!(correct, make_parser("for var in; do foo; done").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_if() {
        let correct = Compound(Box::new(If(vec!((vec!(cmd_unboxed("guard")), vec!(cmd_unboxed("body")))), None)), vec!());
        assert_eq!(correct, make_parser("if guard; then body; fi").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_case() {
        let correct = Compound(Box::new(Case(Word::Literal(String::from("foo")), vec!())), vec!());
        assert_eq!(correct, make_parser("case foo in esac").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_errors_on_quoted_commands() {
        let cases = [
            "{foo; }", // { is a reserved word, thus concatenating it essentially "quotes" it
            "'{' foo; }",
            "'(' foo; )",
            "'while' guard do foo; done",
            "'until' guard do foo; done",
            "'if' guard; then body; fi",
            "'for' var in; do foo; done",
            "'case' foo in esac",
            "\"{\" foo; }",
            "\"(\" foo; )",
            "\"while\" guard do foo; done",
            "\"until\" guard do foo; done",
            "\"if\" guard; then body; fi",
            "\"for\" var in; do foo; done",
            "\"case\" foo in esac",
        ];

        for cmd in cases.iter() {
            match make_parser(cmd).compound_command() {
                Err(_) => {},
                Ok(result) =>
                    panic!("Parse::compound_command unexpectedly succeeded parsing \"{}\" with result:\n{:#?}",
                           cmd, result),
            }
        }
    }

    #[test]
    fn test_compound_command_captures_redirections_after_command() {
        let cases = [
            "{ foo; } 1>>out <& 2 2>&-",
            "( foo; ) 1>>out <& 2 2>&-",
            "while guard; do foo; done 1>>out <& 2 2>&-",
            "until guard; do foo; done 1>>out <& 2 2>&-",
            "if guard; then body; fi 1>>out <& 2 2>&-",
            "for var in; do foo; done 1>>out <& 2 2>&-",
            "case foo in esac 1>>out <& 2 2>&-",
        ];

        for cmd in cases.iter() {
            match make_parser(cmd).compound_command() {
                Ok(Compound(_, io)) => assert_eq!(io, vec!(
                    Redirect::Append(Some(Word::Literal(String::from("1"))), Word::Literal(String::from("out"))),
                    Redirect::DupRead(None, Word::Literal(String::from("2"))),
                    Redirect::CloseWrite(Some(Word::Literal(String::from("2")))),
                )),

                Ok(result) => panic!("Parsed \"{}\" as an unexpected command type:\n{:#?}", cmd, result),
                Err(err) => panic!("Failed to parse \"{}\": {}", cmd, err),
            }
        }
    }

    #[test]
    fn test_compound_command_should_delegate_literals_and_names_loop() {
        for kw in vec!(
            Token::Literal(String::from("while")),
            Token::Name(String::from("while")),
            Token::Literal(String::from("until")),
            Token::Name(String::from("until")))
        {
            let mut p = make_parser_from_tokens(vec!(
                kw,
                Token::Newline,
                Token::Literal(String::from("guard")),
                Token::Newline,
                Token::Literal(String::from("do")),
                Token::Newline,
                Token::Literal(String::from("foo")),
                Token::Newline,
                Token::Literal(String::from("done")),
            ));
            p.compound_command().unwrap();
        }
    }

    #[test]
    fn test_compound_command_should_delegate_literals_and_names_if() {
        for if_tok in vec!(Token::Literal(String::from("if")), Token::Name(String::from("if"))) {
            for then_tok in vec!(Token::Literal(String::from("then")), Token::Name(String::from("then"))) {
                for elif_tok in vec!(Token::Literal(String::from("elif")), Token::Name(String::from("elif"))) {
                    for else_tok in vec!(Token::Literal(String::from("else")), Token::Name(String::from("else"))) {
                        for fi_tok in vec!(Token::Literal(String::from("fi")), Token::Name(String::from("fi"))) {
                            let mut p = make_parser_from_tokens(vec!(
                                    if_tok.clone(),
                                    Token::Whitespace(String::from(" ")),

                                    Token::Literal(String::from("guard1")),
                                    Token::Newline,

                                    then_tok.clone(),
                                    Token::Newline,
                                    Token::Literal(String::from("body1")),

                                    elif_tok.clone(),
                                    Token::Whitespace(String::from(" ")),

                                    Token::Literal(String::from("guard2")),
                                    Token::Newline,
                                    then_tok.clone(),
                                    Token::Whitespace(String::from(" ")),
                                    Token::Literal(String::from("body2")),

                                    else_tok.clone(),
                                    Token::Whitespace(String::from(" ")),

                                    Token::Whitespace(String::from(" ")),
                                    Token::Literal(String::from("else part")),
                                    Token::Newline,

                                    fi_tok,
                            ));
                            p.compound_command().unwrap();
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_compound_command_should_delegate_literals_and_names_for() {
        for for_tok in vec!(Token::Literal(String::from("for")), Token::Name(String::from("for"))) {
            for in_tok in vec!(Token::Literal(String::from("in")), Token::Name(String::from("in"))) {
                let mut p = make_parser_from_tokens(vec!(
                    for_tok.clone(),
                    Token::Whitespace(String::from(" ")),

                    Token::Name(String::from("var")),
                    Token::Whitespace(String::from(" ")),

                    in_tok.clone(),
                    Token::Whitespace(String::from(" ")),
                    Token::Literal(String::from("one")),
                    Token::Whitespace(String::from(" ")),
                    Token::Literal(String::from("two")),
                    Token::Whitespace(String::from(" ")),
                    Token::Literal(String::from("three")),
                    Token::Whitespace(String::from(" ")),
                    Token::Newline,

                    Token::Literal(String::from("do")),
                    Token::Whitespace(String::from(" ")),

                    Token::Literal(String::from("echo")),
                    Token::Whitespace(String::from(" ")),
                    Token::Dollar,
                    Token::Name(String::from("var")),
                    Token::Newline,

                    Token::Literal(String::from("done")),
                ));
                p.compound_command().unwrap();
            }
        }
    }

    #[test]
    fn test_compound_command_should_delegate_literals_and_names_case() {
        let case_str = String::from("case");
        let in_str   = String::from("in");
        let esac_str = String::from("esac");
        for case_tok in vec!(Token::Literal(case_str.clone()), Token::Name(case_str.clone())) {
            for in_tok in vec!(Token::Literal(in_str.clone()), Token::Name(in_str.clone())) {
                for esac_tok in vec!(Token::Literal(esac_str.clone()), Token::Name(esac_str.clone())) {
                    let mut p = make_parser_from_tokens(vec!(
                        case_tok.clone(),
                        Token::Whitespace(String::from(" ")),

                        Token::Literal(String::from("foo")),
                        Token::Literal(String::from("bar")),

                        Token::Whitespace(String::from(" ")),
                        in_tok.clone(),
                        Token::Whitespace(String::from(" ")),

                        Token::Literal(String::from("foo")),
                        Token::ParenClose,
                        Token::Newline,
                        Token::Literal(String::from("echo")),
                        Token::Whitespace(String::from(" ")),
                        Token::Literal(String::from("foo")),
                        Token::Newline,
                        Token::Newline,
                        Token::DSemi,

                        esac_tok
                    ));
                    p.compound_command().unwrap();
                }
            }
        }
    }

    #[test]
    fn test_command_delegates_valid_commands_brace() {
        let correct = Compound(Box::new(Brace(vec!(cmd_unboxed("foo")))), vec!());
        assert_eq!(correct, make_parser("{ foo; }").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_commands_subshell() {
        let commands = [
            "(foo)",
            "( foo)",
        ];

        let correct = Compound(Box::new(Subshell(vec!(cmd_unboxed("foo")))), vec!());

        for cmd in commands.iter() {
            match make_parser(cmd).command() {
                Ok(ref result) if result == &correct => {},
                Ok(result) => panic!("Parsed \"{}\" as an unexpected command type:\n{:#?}", cmd, result),
                Err(err) => panic!("Failed to parse \"{}\": {}", cmd, err),
            }
        }
    }

    #[test]
    fn test_command_delegates_valid_commands_while() {
        let correct = Compound(Box::new(While(vec!(cmd_unboxed("guard")), vec!(cmd_unboxed("foo")))), vec!());
        assert_eq!(correct, make_parser("while guard; do foo; done").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_commands_until() {
        let correct = Compound(Box::new(Until(vec!(cmd_unboxed("guard")), vec!(cmd_unboxed("foo")))), vec!());
        assert_eq!(correct, make_parser("until guard; do foo; done").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_commands_for() {
        let correct = Compound(Box::new(For(String::from("var"), Some(vec!()), vec!(cmd_unboxed("foo")))), vec!());
        assert_eq!(correct, make_parser("for var in; do foo; done").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_commands_if() {
        let correct = Compound(Box::new(If(vec!((vec!(cmd_unboxed("guard")), vec!(cmd_unboxed("body")))), None)), vec!());
        assert_eq!(correct, make_parser("if guard; then body; fi").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_commands_case() {
        let correct = Compound(Box::new(Case(Word::Literal(String::from("foo")), vec!())), vec!());
        assert_eq!(correct, make_parser("case foo in esac").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_simple_commands() {
        let correct = cmd_args_unboxed("echo", &["foo", "bar"]);
        assert_eq!(correct, make_parser("echo foo bar").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_commands_function() {
        let commands = [
            "function foo()      { echo body; }",
            "function foo ()     { echo body; }",
            "function foo (    ) { echo body; }",
            "function foo(    )  { echo body; }",
            "function foo        { echo body; }",
            "foo()               { echo body; }",
            "foo ()              { echo body; }",
            "foo (    )          { echo body; }",
            "foo(    )           { echo body; }",
        ];

        let correct = Function(String::from("foo"), Box::new(Compound(Box::new(Brace(vec!(cmd_args_unboxed("echo", &["body"])))), vec!())));

        for cmd in commands.iter() {
            match make_parser(cmd).command() {
                Ok(ref result) if result == &correct => {},
                Ok(result) => panic!("Parsed \"{}\" as an unexpected command type:\n{:#?}", cmd, result),
                Err(err) => panic!("Failed to parse \"{}\": {}", cmd, err),
            }
        }
    }

    #[test]
    fn test_command_parses_quoted_compound_commands_as_simple_commands() {
        let cases = [
            "{foo; }", // { is a reserved word, thus concatenating it essentially "quotes" it
            "'{' foo; }",
            "'(' foo; )",
            "'while' guard do foo; done",
            "'until' guard do foo; done",
            "'if' guard; then body; fi",
            "'for' var in; do echo $var; done",
            "'function' name { echo body; }",
            "name'()' { echo body; }",
            "123fn() { echo body; }",
            "'case' foo in esac",
            "\"{\" foo; }",
            "\"(\" foo; )",
            "\"while\" guard do foo; done",
            "\"until\" guard do foo; done",
            "\"if\" guard; then body; fi",
            "\"for\" var in; do echo $var; done",
            "\"function\" name { echo body; }",
            "name\"()\" { echo body; }",
            "\"case\" foo in esac",
        ];

        for cmd in cases.iter() {
            match make_parser(cmd).command() {
                Ok(Simple(_)) => {},
                Ok(result) =>
                    panic!("Parse::command unexpectedly parsed \"{}\" as a non-simple command:\n{:#?}", cmd, result),
                Err(err) => panic!("Parse::command failed to parse \"{}\": {}", cmd, err),
            }
        }
    }

    #[test]
    fn test_command_should_delegate_literals_and_names_loop_while() {
        for kw in vec!(
            Token::Literal(String::from("while")),
            Token::Name(String::from("while"))
        ) {
            let mut p = make_parser_from_tokens(vec!(
                kw,
                Token::Newline,
                Token::Literal(String::from("guard")),
                Token::Newline,
                Token::Literal(String::from("do")),
                Token::Newline,
                Token::Literal(String::from("foo")),
                Token::Newline,
                Token::Literal(String::from("done")),
            ));

            let cmd = p.command().unwrap();
            if let Compound(ref loop_cmd, _) = cmd {
                if let While(..) = **loop_cmd {
                    continue;
                } else {
                    panic!("Parsed an unexpected command:\n{:#?}", cmd)
                }
            }
        }
    }

    #[test]
    fn test_command_should_delegate_literals_and_names_loop_until() {
        for kw in vec!(
            Token::Literal(String::from("until")),
            Token::Name(String::from("until"))
        ) {
            let mut p = make_parser_from_tokens(vec!(
                kw,
                Token::Newline,
                Token::Literal(String::from("guard")),
                Token::Newline,
                Token::Literal(String::from("do")),
                Token::Newline,
                Token::Literal(String::from("foo")),
                Token::Newline,
                Token::Literal(String::from("done")),
            ));

            let cmd = p.command().unwrap();
            if let Compound(ref loop_cmd, _) = cmd {
                if let Until(..) = **loop_cmd {
                    continue;
                } else {
                    panic!("Parsed an unexpected command:\n{:#?}", cmd)
                }
            }
        }
    }

    #[test]
    fn test_command_should_delegate_literals_and_names_if() {
        for if_tok in vec!(Token::Literal(String::from("if")), Token::Name(String::from("if"))) {
            for then_tok in vec!(Token::Literal(String::from("then")), Token::Name(String::from("then"))) {
                for elif_tok in vec!(Token::Literal(String::from("elif")), Token::Name(String::from("elif"))) {
                    for else_tok in vec!(Token::Literal(String::from("else")), Token::Name(String::from("else"))) {
                        for fi_tok in vec!(Token::Literal(String::from("fi")), Token::Name(String::from("fi"))) {
                            let mut p = make_parser_from_tokens(vec!(
                                    if_tok.clone(),
                                    Token::Whitespace(String::from(" ")),

                                    Token::Literal(String::from("guard1")),
                                    Token::Newline,

                                    then_tok.clone(),
                                    Token::Newline,
                                    Token::Literal(String::from("body1")),

                                    elif_tok.clone(),
                                    Token::Whitespace(String::from(" ")),

                                    Token::Literal(String::from("guard2")),
                                    Token::Newline,
                                    then_tok.clone(),
                                    Token::Whitespace(String::from(" ")),
                                    Token::Literal(String::from("body2")),

                                    else_tok.clone(),
                                    Token::Whitespace(String::from(" ")),

                                    Token::Whitespace(String::from(" ")),
                                    Token::Literal(String::from("else part")),
                                    Token::Newline,

                                    fi_tok,
                            ));

                            let cmd = p.command().unwrap();
                            if let Compound(ref if_cmd, _) = cmd {
                                if let If(..) = **if_cmd {
                                    continue;
                                } else {
                                    panic!("Parsed an unexpected command:\n{:#?}", cmd)
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_command_should_delegate_literals_and_names_for() {
        for for_tok in vec!(Token::Literal(String::from("for")), Token::Name(String::from("for"))) {
            for in_tok in vec!(Token::Literal(String::from("in")), Token::Name(String::from("in"))) {
                let mut p = make_parser_from_tokens(vec!(
                    for_tok.clone(),
                    Token::Whitespace(String::from(" ")),

                    Token::Name(String::from("var")),
                    Token::Whitespace(String::from(" ")),

                    in_tok.clone(),
                    Token::Whitespace(String::from(" ")),
                    Token::Literal(String::from("one")),
                    Token::Whitespace(String::from(" ")),
                    Token::Literal(String::from("two")),
                    Token::Whitespace(String::from(" ")),
                    Token::Literal(String::from("three")),
                    Token::Whitespace(String::from(" ")),
                    Token::Newline,

                    Token::Literal(String::from("do")),
                    Token::Whitespace(String::from(" ")),

                    Token::Literal(String::from("echo")),
                    Token::Whitespace(String::from(" ")),
                    Token::Dollar,
                    Token::Name(String::from("var")),
                    Token::Newline,

                    Token::Literal(String::from("done")),
                ));

                let cmd = p.command().unwrap();
                if let Compound(ref for_cmd, _) = cmd {
                    if let For(..) = **for_cmd {
                        continue;
                    } else {
                        panic!("Parsed an unexpected command:\n{:#?}", cmd)
                    }
                }
            }
        }
    }

    #[test]
    fn test_command_should_delegate_literals_and_names_case() {
        let case_str = String::from("case");
        let in_str   = String::from("in");
        let esac_str = String::from("esac");
        for case_tok in vec!(Token::Literal(case_str.clone()), Token::Name(case_str.clone())) {
            for in_tok in vec!(Token::Literal(in_str.clone()), Token::Name(in_str.clone())) {
                for esac_tok in vec!(Token::Literal(esac_str.clone()), Token::Name(esac_str.clone())) {
                    let mut p = make_parser_from_tokens(vec!(
                        case_tok.clone(),
                        Token::Whitespace(String::from(" ")),

                        Token::Literal(String::from("foo")),
                        Token::Literal(String::from("bar")),

                        Token::Whitespace(String::from(" ")),
                        in_tok.clone(),
                        Token::Whitespace(String::from(" ")),

                        Token::Literal(String::from("foo")),
                        Token::ParenClose,
                        Token::Newline,
                        Token::Literal(String::from("echo")),
                        Token::Whitespace(String::from(" ")),
                        Token::Literal(String::from("foo")),
                        Token::Newline,
                        Token::Newline,
                        Token::DSemi,

                        esac_tok
                    ));

                    let cmd = p.command().unwrap();
                    if let Compound(ref case_cmd, _) = cmd {
                        if let Case(..) = **case_cmd {
                            continue;
                        } else {
                            panic!("Parsed an unexpected command:\n{:#?}", cmd)
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_command_should_delegate_literals_and_names_for_function_declaration() {
        for fn_tok in vec!(Token::Literal(String::from("function")), Token::Name(String::from("function"))) {
            let mut p = make_parser_from_tokens(vec!(
                fn_tok,
                Token::Whitespace(String::from(" ")),

                Token::Name(String::from("fn_name")),
                Token::Whitespace(String::from(" ")),

                Token::ParenOpen, Token::ParenClose,
                Token::Whitespace(String::from(" ")),
                Token::CurlyOpen,
                Token::Literal(String::from("echo")),
                Token::Whitespace(String::from(" ")),
                Token::Literal(String::from("fn body")),
                Token::Semi,
                Token::CurlyClose,
            ));
            match p.command() {
                Ok(Function(..)) => {},
                Ok(result) => panic!("Parsed an unexpected command type:\n{:#?}", result),
                Err(err) => panic!("Failed to parse command: {}", err),
            }
        }
    }

    #[test]
    fn test_command_do_not_delegate_functions_only_if_fn_name_is_a_literal_token() {
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("fn_name")),
            Token::Whitespace(String::from(" ")),

            Token::ParenOpen, Token::ParenClose,
            Token::Whitespace(String::from(" ")),
            Token::CurlyOpen,
            Token::Literal(String::from("echo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("fn body")),
            Token::Semi,
            Token::CurlyClose,
        ));
        match p.command() {
            Ok(Simple(..)) => {},
            Ok(result) => panic!("Parsed an unexpected command type:\n{:#?}", result),
            Err(err) => panic!("Failed to parse command: {}", err),
        }
    }

    #[test]
    fn test_command_delegate_functions_only_if_fn_name_is_a_name_token() {
        let mut p = make_parser_from_tokens(vec!(
            Token::Name(String::from("fn_name")),
            Token::Whitespace(String::from(" ")),

            Token::ParenOpen, Token::ParenClose,
            Token::Whitespace(String::from(" ")),
            Token::CurlyOpen,
            Token::Literal(String::from("echo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("fn body")),
            Token::Semi,
            Token::CurlyClose,
        ));
        match p.command() {
            Ok(Function(..)) => {},
            Ok(result) => panic!("Parsed an unexpected command type:\n{:#?}", result),
            Err(err) => panic!("Failed to parse command: {}", err),
        }
    }

    #[test]
    fn test_word_preserve_trailing_whitespace() {
        let mut p = make_parser("test       ");
        p.word_preserve_trailing_whitespace().unwrap();
        assert!(p.iter.next().is_some());
    }

    #[test]
    fn test_word_single_quote_valid() {
        let correct = Word::SingleQuoted(String::from("abc&&||\n\n#comment\nabc"));
        assert_eq!(Some(correct), make_parser("'abc&&||\n\n#comment\nabc'").word().unwrap());
    }

    #[test]
    fn test_word_single_quote_valid_slash_remains_literal() {
        let correct = Word::SingleQuoted(String::from("\\\n"));
        assert_eq!(Some(correct), make_parser("'\\\n'").word().unwrap());
    }

    #[test]
    fn test_word_single_quote_slash_valid_does_not_quote_single_quotes() {
        let correct = Word::SingleQuoted(String::from("hello \\"));
        assert_eq!(Some(correct), make_parser("'hello \\'").word().unwrap());
    }

    #[test]
    fn test_word_single_quote_slash_invalid_missing_close_quote() {
        make_parser("'hello").word().unwrap_err();
    }

    #[test]
    fn test_word_double_quote_valid() {
        let correct = Word::DoubleQuoted(vec!(Word::Literal(String::from("abc&&||\n\n#comment\nabc"))));
        assert_eq!(Some(correct), make_parser("\"abc&&||\n\n#comment\nabc\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_recognizes_parameters() {
        let correct = Word::DoubleQuoted(vec!(
            Word::Literal(String::from("test asdf")),
            Word::Param(Parameter::Var(String::from("foo"))),
            Word::Literal(String::from(" ")),
            Word::Literal(String::from("$")),
        ));

        assert_eq!(Some(correct), make_parser("\"test asdf$foo $\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_escapes_dollar() {
        let correct = Word::DoubleQuoted(vec!(
            Word::Literal(String::from("test")),
            Word::Escaped(String::from("$")),
            Word::Literal(String::from("foo ")),
            Word::Param(Parameter::At),
        ));

        assert_eq!(Some(correct), make_parser("\"test\\$foo $@\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_escapes_backtick() {
        let correct = Word::DoubleQuoted(vec!(
            Word::Literal(String::from("test")),
            Word::Escaped(String::from("`")),
            Word::Literal(String::from(" ")),
            Word::Param(Parameter::Star),
        ));

        assert_eq!(Some(correct), make_parser("\"test\\` $*\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_escapes_double_quote() {
        let correct = Word::DoubleQuoted(vec!(
            Word::Literal(String::from("test")),
            Word::Escaped(String::from("\"")),
            Word::Literal(String::from(" ")),
            Word::Param(Parameter::Pound),
        ));

        assert_eq!(Some(correct), make_parser("\"test\\\" $#\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_escapes_newline() {
        let correct = Word::DoubleQuoted(vec!(
            Word::Literal(String::from("test")),
            Word::Escaped(String::from("\n")),
            Word::Literal(String::from(" ")),
            Word::Param(Parameter::Question),
            Word::Literal(String::from("\n")),
        ));

        assert_eq!(Some(correct), make_parser("\"test\\\n $?\n\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_escapes_slash() {
        let correct = Word::DoubleQuoted(vec!(
            Word::Literal(String::from("test")),
            Word::Escaped(String::from("\\")),
            Word::Literal(String::from(" ")),
            Word::Param(Parameter::Positional(0)),
        ));

        assert_eq!(Some(correct), make_parser("\"test\\\\ $0\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_remains_literal_in_general_case() {
        let correct = Word::DoubleQuoted(vec!(
            Word::Literal(String::from("t\\est ")),
            Word::Param(Parameter::Dollar),
        ));

        assert_eq!(Some(correct), make_parser("\"t\\est $$\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_slash_invalid_missing_close_quote() {
        make_parser("\"hello").word().unwrap_err();
        make_parser("\"hello\\\"").word().unwrap_err();
    }

    #[test]
    fn test_word_delegate_parameters() {
        let params = [
            "$@",
            "$*",
            "$#",
            "$?",
            "$-",
            "$$",
            "$!",
            "$3",
            "${@}",
            "${*}",
            "${#}",
            "${?}",
            "${-}",
            "${$}",
            "${!}",
            "${foo}",
            "${3}",
            "${1000}",
        ];

        for p in params.into_iter() {
            match make_parser(p).word() {
                Ok(Some(Word::Param(_))) => {}
                Ok(Some(w)) => panic!("Unexpectedly parsed \"{}\" as a non-parameter word:\n{:#?}", p, w),
                Ok(None) => panic!("Did not parse \"{}\" as a parameter", p),
                Err(e) => panic!("Did not parse \"{}\" as a parameter: {}", p, e),
            }
        }
    }

    #[test]
    fn test_word_literal_dollar_if_not_param() {
        let mut p = make_parser("$^asdf");
        let correct = Word::Concat(vec!(
            Word::Literal(String::from("$")),
            Word::Literal(String::from("^asdf")),
        ));

        assert_eq!(correct, p.word().unwrap().unwrap());
    }

    #[test]
    fn test_word_does_not_capture_comments() {
        assert_eq!(Ok(None), make_parser("#comment\n").word());
        assert_eq!(Ok(None), make_parser("  #comment\n").word());
        let mut p = make_parser("word   #comment\n");
        p.word().unwrap().unwrap();
        assert_eq!(Ok(None), p.word());
    }

    #[test]
    fn test_word_pound_in_middle_is_not_comment() {
        let correct = Word::Concat(vec!(
            Word::Literal(String::from("abc")),
            Word::Literal(String::from("#")),
            Word::Literal(String::from("def")),
        ));
        assert_eq!(Ok(Some(correct)), make_parser("abc#def\n").word());
    }

    #[test]
    fn test_word_tokens_which_become_literal_words() {
        let words = [
            "{",
            "}",
            "!",
            "blah=",
            "name",
            "1notname",
        ];

        for w in words.into_iter() {
            match make_parser(w).word() {
                Ok(Some(res)) => {
                    let correct = Word::Literal(String::from(*w));
                    if correct != res {
                        panic!("Unexpectedly parsed \"{}\": expected:\n{:#?}\ngot:\n{:#?}", w, correct, res);
                    }
                },
                Ok(None) => panic!("Did not parse \"{}\" as a word", w),
                Err(e) => panic!("Did not parse \"{}\" as a word: {}", w, e),
            }
        }
    }

    #[test]
    fn test_word_concatenation_works() {
        let correct = Word::Concat(vec!(
            Word::Literal(String::from("foo=")),
            Word::Literal(String::from("bar")),
            Word::DoubleQuoted(vec!(Word::Literal(String::from("double")))),
            Word::SingleQuoted(String::from("single")),
        ));

        assert_eq!(Ok(Some(correct)), make_parser("foo=bar\"double\"'single'").word());
    }

    #[test]
    fn test_word_special_words_recognized_as_such() {
        assert_eq!(Ok(Some(Word::Star)),     make_parser("*").word());
        assert_eq!(Ok(Some(Word::Question)), make_parser("?").word());
        assert_eq!(Ok(Some(Word::Tilde)),    make_parser("~").word());
    }

    #[test]
    fn test_word_backslash_makes_things_literal() {
        let lit = [
            "a",
            "&",
            ";",
            "(",
            "*",
            "?",
            "$",
        ];

        for l in lit.into_iter() {
            let src = format!("\\{}", l);
            match make_parser(&src).word() {
                Ok(Some(res)) => {
                    let correct = Word::Escaped(String::from(*l));
                    if correct != res {
                        panic!("Unexpectedly parsed \"{}\": expected:\n{:#?}\ngot:\n{:#?}", src, correct, res);
                    }
                },
                Ok(None) => panic!("Did not parse \"{}\" as a word", src),
                Err(e) => panic!("Did not parse \"{}\" as a word: {}", src, e),
            }
        }
    }

    #[test]
    fn test_word_escaped_newline_becomes_whitespace() {
        let mut p = make_parser("foo\\\nbar");
        assert_eq!(Ok(Some(Word::Literal(String::from("foo")))), p.word());
        assert_eq!(Ok(Some(Word::Literal(String::from("bar")))), p.word());
    }
}

