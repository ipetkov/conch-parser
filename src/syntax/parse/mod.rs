//! The definition of a parser (and related methods) for the shell language.

use std::error::Error;
use std::fmt;
use std::str::FromStr;
use syntax::ast;
use syntax::ast::builder::{self, Builder, SimpleWordKind};
use syntax::ast::builder::ComplexWordKind::{self, Concat, Single};
use syntax::ast::builder::WordKind::{self, DoubleQuoted, Simple, SingleQuoted};
use syntax::token::Token;
use syntax::token::Token::*;

mod iter;

/// A parser which will use a default AST builder implementation,
/// yielding results in terms of types defined in the `ast` module.
pub type DefaultParser<I> = Parser<I, builder::DefaultBuilder>;

/// A specialized `Result` type for parsing shell commands.
pub type Result<T> = ::std::result::Result<T, ParseError>;

/// Indicates a character/token position in the original source.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct SourcePos {
    /// The byte offset since the start of parsing.
    pub byte: usize,
    /// The line offset since the start of parsing, useful for error messages.
    pub line: usize,
    /// The column offset since the start of parsing, useful for error messages.
    pub col: usize,
}

impl SourcePos {
    /// Constructs a new, starting, source position
    pub fn new() -> SourcePos {
        SourcePos { byte: 0, line: 1, col: 1 }
    }

    /// Increments self using the length of the provided token.
    pub fn advance(&mut self, next: &Token) {
        let newlines = match *next {
            // Most of these should not have any newlines
            // embedded within them, but permitting external
            // tokenizers means we should sanity check anyway.
            Name(ref s)       |
            Literal(ref s)    |
            Whitespace(ref s) => s.chars().filter(|&c| c == '\n').count(),

            Newline => 1,
            _ => 0,
        };

        let tok_len = next.len();
        self.byte += tok_len;
        self.line += newlines;
        self.col = if newlines == 0 { self.col + tok_len } else { 1 };
    }
}

/// The error type which is returned from parsing shell commands.
#[derive(Debug)]
pub enum ParseError {
    /// Encountered a word that could not be interpreted as a valid file descriptor.
    /// Stores the start and end position of the invalid word.
    BadFd(SourcePos, SourcePos),
    /// Encountered a `Token::Literal` where expecting a `Token::Name`.
    BadIdent(String, SourcePos),
    /// Encountered a bad token inside of `${...}`.
    BadSubst(Token, SourcePos),
    /// Encountered EOF while looking for a match for the specified token.
    /// Stores position of opening token.
    Unmatched(Token, SourcePos),
    /// Did not find a reserved keyword within a command. The first String is the
    /// command being parsed, followed by the position of where it starts. Next
    /// is the missing keyword followed by the position of where the parse
    /// expected to have encountered it.
    IncompleteCmd(&'static str, SourcePos, &'static str, SourcePos),
    /// Encountered a token not appropriate for the current context.
    Unexpected(Token, SourcePos),
    /// Encountered the end of input while expecting additional tokens.
    UnexpectedEOF,
    /// A custom error returned by the AST builder.
    Custom(Box<Error + Send + Sync>),
}

impl ParseError {
    /// Create a new ParseError which wraps any custom error type.
    pub fn custom<T: Into<Box<Error + Send + Sync>>>(err: T) -> ParseError {
        ParseError::Custom(err.into())
    }
}

impl Error for ParseError {
    fn description(&self) -> &str {
        match *self {
            ParseError::BadFd(..)       => "bad file descriptor found",
            ParseError::BadIdent(..)    => "bad identifier found",
            ParseError::BadSubst(..)    => "bad substitution found",
            ParseError::Unmatched(..)   => "unmatched token",
            ParseError::IncompleteCmd(..)=> "incomplete command",
            ParseError::Unexpected(..)  => "unexpected token found",
            ParseError::UnexpectedEOF   => "unexpected end of input",
            ParseError::Custom(ref e)   => e.description(),
        }
    }

    fn cause(&self) -> Option<&Error> {
        match *self {
            ParseError::BadFd(..)        |
            ParseError::BadIdent(..)     |
            ParseError::BadSubst(..)     |
            ParseError::Unmatched(..)    |
            ParseError::IncompleteCmd(..)|
            ParseError::Unexpected(..)   |
            ParseError::UnexpectedEOF    => None,
            ParseError::Custom(ref e) => Some(&**e),
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ParseError::BadFd(ref start, ref end)  =>
                write!(fmt, "file descriptor found between lines {} - {} cannot possibly be a valid", start, end),
            ParseError::BadIdent(ref id, pos) => write!(fmt, "not a valid identifier {}: {}", pos, id),
            ParseError::BadSubst(ref t, pos)  => write!(fmt, "bad substitution {}: invalid token: {}", pos, t),
            ParseError::Unmatched(ref t, pos) => write!(fmt, "unmatched `{}` starting on line {}", t, pos),

            ParseError::IncompleteCmd(ref c, start, ref kw, kw_pos) => write!(fmt,
                "did not find `{}` keyword on line {}, in `{}` command which starts on line {}",
                kw, kw_pos, c, start),

            // When printing unexpected newlines, print \n instead to avoid confusingly formatted messages
            ParseError::Unexpected(Newline, pos) => write!(fmt, "found unexpected token on line {}: \\n", pos),
            ParseError::Unexpected(ref t, pos)   => write!(fmt, "found unexpected token on line {}: {}", pos, t),

            ParseError::UnexpectedEOF => fmt.write_str("unexpected end of input"),
            ParseError::Custom(ref e) => write!(fmt, "{}", e),
        }
    }
}

impl fmt::Display for SourcePos {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}:{}", self.line, self.col)
    }
}

impl ::std::convert::From<iter::UnmatchedError> for ParseError {
    fn from(err: iter::UnmatchedError) -> ParseError {
        ParseError::Unmatched(err.0, err.1)
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

impl<I: Iterator<Item = Token>, B: Builder> Iterator for Parser<I, B> {
    type Item = Result<B::Command>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.complete_command() {
            Ok(Some(c)) => Some(Ok(c)),
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

/// A parser for the shell language. It will parse shell commands from a
/// stream of shell `Token`s, and pass them to an AST builder.
///
/// The parser implements the `Iterator` trait so that it can behave like
/// a stream of parsed shell commands. Calling `Iterator::next()` on the parser
/// will yield a complete shell command, or an error should one arise.
///
/// # Building
///
/// To construct a parser you need a stream of `Token`s and a `Builder`
/// which will receive data from the parser and assemble an AST. This
/// library provides both a default `Token` lexer, as well as an AST `Builder`.
///
/// ```no_run
/// use shell_lang::syntax::ast::builder::{Builder, DefaultBuilder};
/// use shell_lang::syntax::lexer::Lexer;
/// use shell_lang::syntax::parse::Parser;
///
/// let source = "echo hello world";
/// let lexer = Lexer::new(source.chars());
/// let mut parser = Parser::with_builder(lexer, DefaultBuilder);
/// assert!(parser.complete_command().unwrap().is_some());
/// ```
///
/// If you want to use a parser with the default AST builder implementation
/// you can also use the `DefaultParser` type alias for a simpler setup.
///
/// ```no_run
/// use shell_lang::syntax::lexer::Lexer;
/// use shell_lang::syntax::parse::DefaultParser;
///
/// let source = "echo hello world";
/// let lexer = Lexer::new(source.chars());
/// let mut parser = DefaultParser::new(lexer);
/// assert!(parser.complete_command().unwrap().is_some());
/// ```
///
/// # Token lexing
///
/// Lexer implementations are free to yield tokens in whatever manner they wish,
/// however, there are a few considerations the lexer should take.
///
/// First, the lexer should consolidate consecutive tokens such as `Token::Name`,
/// `Token::Literal`, and `Token::Whitespace` as densely as possible, e.g.
/// `Literal(foobar)` is preferred over `[Literal(foo), Literal(bar)]`. Although
/// such splitting of tokens will not cause problems while parsing most shell
/// commands, certain situations require the parser to look-ahead some fixed
/// number of tokens so it can avoid backtracking. When the tokens are consolidated
/// the parser can look-ahead deterministically. If a lexer implementation chooses
/// not to use this strategy, the parser may unsuccessfully parse certain inputs
/// normally considered valid.
///
/// Second, the lexer can influence how token escaping is handled by the parser.
/// The backslash token, `\` is used to escape, or make literal, any token which
/// may or may not have a special meaning. Since the parser operates on tokens and
/// not characters, the escaping of multi-character tokens is affected by how the
/// lexer yields them. For example, the source `\<<` is normally considered by shells
/// as `[Literal(<), Less]`. If this behavior is desired, the lexer should yield
/// the tokens `[Backslash, Less, Less]` for that source. Otherwise if the lexer
/// yields the tokens `[Backslash, DLess]`, the parser will treat the source as if
/// it were `[Literal(<<)]`. The lexer's behavior need not be consistent between different
/// multi-char tokens, as long as it is aware of the implications.
#[derive(Debug)]
pub struct Parser<I: Iterator<Item = Token>, B: Builder> {
    iter: iter::TokenIter<I>,
    builder: B,
}

impl<I: Iterator<Item = Token>, B: Builder + Default> Parser<I, B> {
    /// Creates a new Parser from a Token iterator or collection.
    pub fn new<T>(iter: T) -> Parser<I, B> where T: IntoIterator<Item = Token, IntoIter = I> {
        Parser::with_builder(iter.into_iter(), Default::default())
    }
}

/// A macro that will consume and return a token that matches a specified pattern
/// from a parser's token iterator. If no matching token is found, None will be yielded.
macro_rules! eat_maybe {
    ($parser:expr, { $($tok:pat => $blk:block),+; _ => $default:block, }) => {
        eat_maybe!($parser, { $($tok => $blk),+; _ => $default })
    };

    ($parser:expr, { $($tok:pat => $blk:block),+,}) => {
        eat_maybe!($parser, { $($tok => $blk),+ })
    };

    ($parser:expr, { $($tok:pat => $blk:block),+ }) => {
        eat_maybe!($parser, { $($tok => $blk),+; _ => {} })
    };

    ($parser:expr, { $($tok:pat => $blk:block),+; _ => $default:block }) => {
        $(if let Some(&$tok) = $parser.iter.peek() {
            $parser.iter.next();
            $blk
        } else)+ {
            $default
        }
    };
}

/// A macro that will consume a specified token from the parser's iterator
/// an run a corresponding action block to do something with the token,
/// or it will construct and return an appropriate Unexpected(EOF) error.
macro_rules! eat {
    ($parser:expr, { $($tok:pat => $blk:block),+, }) => { eat!($parser, {$($tok => $blk),+}) };
    ($parser:expr, {$($tok:pat => $blk:block),+}) => {
        eat_maybe!($parser, {$($tok => $blk),+; _ => { return Err($parser.make_unexpected_err()) } })
    };
}

/// A macro that defines a function for parsing binary operations in arithmetic
/// expressions.  It accepts a name for the function, a name for the subsequent
/// expression (which has a higher precedence) to sub parse on, and a number of
/// tokens which can be recognized as an operator for the binary operation and
/// the appropriate AST constructor for said token/operator. All operators within
/// the definition are considered to have identical precedence and are left-to-right
/// associative.
macro_rules! arith_parse {
    ($fn_name:ident, $next_expr:ident, $($tok:pat => $constructor:path),+) => {
        #[inline]
        fn $fn_name(&mut self) -> Result<ast::Arithmetic> {
            let mut expr = try!(self.$next_expr());
            loop {
                self.skip_whitespace();
                eat_maybe!(self, {
                    $($tok => {
                        let next = try!(self.$next_expr());
                        expr = $constructor(Box::new(expr), Box::new(next));
                    }),+;
                    _ => { break },
                });
            }
            Ok(expr)
        }
    }
}

impl<I: Iterator<Item = Token>, B: Builder> Parser<I, B> {
    /// Construct an `Unexpected` error using the given token. If `None` specified, the next
    /// token in the iterator will be used (or `UnexpectedEOF` if none left).
    #[inline]
    fn make_unexpected_err(&mut self) -> ParseError {
        let pos = self.iter.pos();
        self.iter.next().map_or(ParseError::UnexpectedEOF, |t| ParseError::Unexpected(t, pos))
    }

    /// Creates a new Parser from a Token iterator and provided AST builder.
    pub fn with_builder(iter: I, builder: B) -> Parser<I, B> {
        Parser {
            iter: iter::TokenIter::new(iter),
            builder: builder,
        }
    }

    /// Creates a new Parser from a TokenIter and provided AST builder.
    /// Useful for when we have a collection of tokens which might not be contiguous
    /// but we don't want to lose the position information.
    fn with_token_iter_and_builder(iter: iter::TokenIter<I>, builder: B) -> Parser<I, B> {
        Parser {
            iter: iter,
            builder: builder,
        }
    }

    /// Returns the parser's current position in the source.
    pub fn pos(&self) -> SourcePos { self.iter.pos() }

    /// Parses a single complete command.
    ///
    /// For example, `foo && bar; baz` will yield two complete
    /// commands: `And(foo, bar)`, and `Simple(baz)`.
    pub fn complete_command(&mut self) -> Result<Option<B::Command>> {
        let pre_cmd_comments = self.linebreak();

        if self.iter.peek().is_none() {
            try!(self.builder.comments(pre_cmd_comments));
            return Ok(None);
        }

        let cmd = try!(self.and_or());

        let sep = eat_maybe!(self, {
            Semi => { builder::SeparatorKind::Semi },
            Amp  => { builder::SeparatorKind::Amp  };
            _ => {
                if let Some(n) = self.newline() {
                    builder::SeparatorKind::Newline(n)
                } else {
                    builder::SeparatorKind::Other
                }
            }
        });

        let post_cmd_comments = self.linebreak();
        Ok(Some(try!(self.builder.complete_command(pre_cmd_comments, cmd, sep, post_cmd_comments))))
    }

    /// Parses compound AND/OR commands.
    ///
    /// Commands are left associative. For example `foo || bar && baz`
    /// parses to `And(Or(foo, bar), baz)`.
    pub fn and_or(&mut self) -> Result<B::Command> {
        let mut cmd = try!(self.pipeline());

        loop {
            self.skip_whitespace();
            let kind = eat_maybe!(self, {
                OrIf  => { builder::AndOrKind::Or  },
                AndIf => { builder::AndOrKind::And };
                _ => { break },
            });

            let post_sep_comments = self.linebreak();
            let next = try!(self.pipeline());
            cmd = try!(self.builder.and_or(cmd, kind, post_sep_comments, next));
        }

        Ok(cmd)
    }

    /// Parses either a single command or a pipeline of commands.
    ///
    /// For example `[!] foo | bar`.
    pub fn pipeline(&mut self) -> Result<B::Command> {
        self.skip_whitespace();
        let bang = eat_maybe!(self, {
            Bang => { true };
            _ => { false },
        });

        let mut cmds = Vec::new();
        loop {
            // We've already passed an apropriate spot for !, so it
            // is an error if it appears before the start of a command.
            if let Some(&Bang) = self.iter.peek() {
                return Err(self.make_unexpected_err());
            }

            let cmd = try!(self.command());

            eat_maybe!(self, {
                Pipe => { cmds.push((self.linebreak(), cmd)) };
                _ => {
                    cmds.push((Vec::new(), cmd));
                    break;
                },
            });
        }

        Ok(try!(self.builder.pipeline(bang, cmds)))
    }

    /// Parses any command which itself is not a pipeline or an AND/OR command.
    pub fn command(&mut self) -> Result<B::Command> {
        if let Some(kw) = self.next_compound_command_type() {
            return self.compound_command_internal(Some(kw))
        }

        if self.peek_reserved_word(&["function"]).is_some() {
            return self.function_declaration();
        }

        let is_fn = {
            let mut peeked = self.iter.peek_many(3).into_iter();
            if let Some(&Name(_)) = peeked.next() {
                let second = peeked.next();

                if let Some(&Whitespace(_)) = second {
                    Some(&ParenOpen) == peeked.next()
                } else {
                    Some(&ParenOpen) == second
                }
            } else {
                false
            }
        };

        if is_fn {
            self.function_declaration()
        } else {
            self.simple_command()
        }
    }

    /// Tries to parse a simple command, e.g. `cmd arg1 arg2 >redirect`.
    ///
    /// A valid command is expected to have at least an executable name, or a single
    /// variable assignment or redirection. Otherwise an error will be returned.
    pub fn simple_command(&mut self) -> Result<B::Command> {
        let mut cmd: Option<B::Word> = None;
        let mut args = Vec::new();
        let mut vars = Vec::new();
        let mut io = Vec::new();

        loop {
            self.skip_whitespace();
            let is_name = {
                let mut peeked = self.iter.peek_many(2).into_iter();
                if let Some(&Name(_)) = peeked.next() {
                    Some(&Equals) == peeked.next()
                } else {
                    false
                }
            };

            if is_name {
                if let Some(Name(var)) = self.iter.next() {
                    self.iter.next(); // Consume the =

                    let value = if let Some(&Whitespace(_)) = self.iter.peek() {
                        None
                    } else {
                        try!(self.word())
                    };
                    vars.push((var, value));

                    // Make sure we continue checking for assignments,
                    // otherwise it they can be interpreted as literal words.
                    continue;
                } else {
                    unreachable!();
                }
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
        let cmd = match cmd {
            Some(cmd) => Some((cmd, args)),
            None => {
                debug_assert!(args.is_empty());
                if vars.is_empty() && io.is_empty() {
                    try!(Err(self.make_unexpected_err()));
                }
                None
            },
        };

        Ok(try!(self.builder.simple_command(vars, cmd, io)))
    }

    /// Parses a continuous list of redirections and will error if any words
    /// that are not valid file descriptors are found. Essentially used for
    /// parsing redirection lists after a compound command like `while` or `if`.
    pub fn redirect_list(&mut self) -> Result<Vec<B::Redirect>> {
        let mut list = Vec::new();
        loop {
            self.skip_whitespace();
            let start_pos = self.iter.pos();
            match try!(self.redirect()) {
                Some(Ok(io)) => list.push(io),
                Some(Err(_)) => return Err(ParseError::BadFd(start_pos, self.iter.pos())),
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
    pub fn redirect(&mut self) -> Result<Option<::std::result::Result<B::Redirect, B::Word>>> {
        fn could_be_numeric<C>(word: &WordKind<C>) -> bool {
            let simple_could_be_numeric = |word: &SimpleWordKind<C>| match *word {
                SimpleWordKind::Star        |
                SimpleWordKind::Question    |
                SimpleWordKind::SquareOpen  |
                SimpleWordKind::SquareClose |
                SimpleWordKind::Tilde       |
                SimpleWordKind::Colon       => false,

                // Literals and can be statically checked if they have non-numeric characters
                SimpleWordKind::Escaped(ref s) |
                SimpleWordKind::Literal(ref s) => s.chars().all(|c| c.is_digit(10)),

                // These could end up evaluating to a numeric,
                // but we'll have to see at runtime.
                SimpleWordKind::Param(_) |
                SimpleWordKind::Subst(_) |
                SimpleWordKind::CommandSubst(_) => true,
            };

            match *word {
                Simple(ref s) => simple_could_be_numeric(s),
                SingleQuoted(ref s) => s.chars().all(|c| c.is_digit(10)),
                DoubleQuoted(ref fragments) => fragments.iter().all(simple_could_be_numeric),
            }
        }

        fn as_num<C>(word: &ComplexWordKind<C>) -> Option<u16> {
            match *word {
                Single(Simple(SimpleWordKind::Literal(ref s))) => u16::from_str_radix(s, 10).ok(),
                Single(_) => None,
                Concat(ref fragments) => {
                    let mut buf = String::new();
                    for w in fragments {
                        if let Simple(SimpleWordKind::Literal(ref s)) = *w {
                            buf.push_str(s);
                        } else {
                            return None;
                        }
                    }

                    u16::from_str_radix(&buf, 10).ok()
                }
            }
        }

        let (src_fd, src_fd_as_word) = match try!(self.word_preserve_trailing_whitespace_raw()) {
            None => (None, None),
            Some(w) => match as_num(&w) {
                Some(num) => (Some(num), Some(w)),
                None => return Ok(Some(Err(try!(self.builder.word(w))))),
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

            Some(&DLess)     |
            Some(&DLessDash) => return Ok(Some(Ok(try!(self.redirect_heredoc(src_fd))))),

            _ => match src_fd_as_word {
                Some(w) => return Ok(Some(Err(try!(self.builder.word(w))))),
                None => return Ok(None),
            },
        };

        self.skip_whitespace();

        macro_rules! get_path {
            ($parser:expr) => {
                match try!($parser.word_preserve_trailing_whitespace_raw()) {
                    Some(p) => try!($parser.builder.word(p)),
                    None => return Err(self.make_unexpected_err()),
                }
            }
        }

        macro_rules! get_dup_path {
            ($parser:expr) => {{
                let path = if $parser.peek_reserved_token(&[Dash]).is_some() {
                    let dash = try!($parser.reserved_token(&[Dash])).to_string();
                    Single(Simple(SimpleWordKind::Literal(dash)))
                } else {
                    let path_start_pos = $parser.iter.pos();
                    let path = if let Some(p) = try!($parser.word_preserve_trailing_whitespace_raw()) {
                        p
                    } else {
                        return Err($parser.make_unexpected_err())
                    };
                    let is_numeric = match path {
                        Single(ref p) => could_be_numeric(&p),
                        Concat(ref v) => v.iter().all(could_be_numeric),
                    };
                    if is_numeric {
                        path
                    } else {
                        return Err(ParseError::BadFd(path_start_pos, self.iter.pos()));
                    }
                };
                try!($parser.builder.word(path))
            }}
        }

        let redirect = match redir_tok {
            Less      => builder::RedirectKind::Read(src_fd, get_path!(self)),
            Great     => builder::RedirectKind::Write(src_fd, get_path!(self)),
            DGreat    => builder::RedirectKind::Append(src_fd, get_path!(self)),
            Clobber   => builder::RedirectKind::Clobber(src_fd, get_path!(self)),
            LessGreat => builder::RedirectKind::ReadWrite(src_fd, get_path!(self)),

            LessAnd   => builder::RedirectKind::DupRead(src_fd, get_dup_path!(self)),
            GreatAnd  => builder::RedirectKind::DupWrite(src_fd, get_dup_path!(self)),

            _ => unreachable!(),
        };

        Ok(Some(Ok(try!(self.builder.redirect(redirect)))))
    }

    /// Parses a heredoc redirection and the heredoc's body.
    ///
    /// This method will look ahead after the next unquoted/unescaped newline
    /// to capture the heredoc's body, and will stop consuming tokens until
    /// the approrpiate delimeter is found on a line by itself. If the
    /// delimeter is unquoted, the heredoc's body will be expanded for
    /// parameters and other special words. Otherwise, there heredoc's body
    /// will be treated as a literal.
    ///
    /// The heredoc delimeter need not be a valid word (e.g. parameter subsitution
    /// rules within ${ } need not apply), although it is expected to be balanced
    /// like a regular word. In other words, all single/double quotes, backticks,
    /// `${ }`, `$( )`, and `( )` must be balanced.
    ///
    /// Note: if the delimeter is quoted, this method will look for an UNQUOTED
    /// version in the body. For example `<<"EOF"` will cause the parser to look
    /// until `\nEOF` is found. This it is possible to create a heredoc that can
    /// only be delimited by the end of the stream, e.g. if a newline is embedded
    /// within the delimeter. Any backticks that appear in the delimeter are
    /// expected to appear at the end of the delimeter of the heredoc body, as
    /// well as any embedded backslashes (unless the backslashes are followed by
    /// a \, $, or `).
    ///
    /// Note: this method expects that the caller provide a potential file
    /// descriptor for redirection.
    pub fn redirect_heredoc(&mut self, src_fd: Option<u16>) -> Result<B::Redirect> {
        let strip_tabs = eat!(self, {
            DLess => { false },
            DLessDash => { true },
        });

        self.skip_whitespace();

        // Unfortunately we're going to have to capture the delimeter word "manually"
        // here and double some code. The problem is that we might need to unquote the
        // word--something that the parser isn't normally aware as a concept. We can
        // crawl a parsed WordKind tree, but we would still have to convert the inner
        // trees as either a token collection or into a string, each of which is more
        // trouble than its worth (especially since WordKind can hold a parsed and
        // and assembled Builder::Command object, which may not even be possible to
        // be represented as a string).
        //
        // Also some shells like bash and zsh seem to check for balanced tokens like
        // ', ", or ` within the heredoc delimiter (though this may just be from them
        // parsing out a word as usual), so to maintain reasonable expectations, we'll
        // do the same here.
        let mut delim_tokens = Vec::new();
        loop {
            // Normally parens are never part of words, but many
            // shells permit them to be part of a heredoc delimeter.
            if let Some(t) = self.iter.peek() {
                if t.is_word_delimiter() && t != &ParenOpen { break; }
            } else {
                break;
            }

            for t in self.iter.balanced() { delim_tokens.push(try!(t)); }
        }

        let mut iter = iter::TokenIter::new(delim_tokens.into_iter());
        let mut quoted = false;
        let mut delim = String::new();
        loop {
            let start_pos = iter.pos();
            match iter.next() {
                Some(Backslash) => {
                    quoted = true;
                    iter.next().map(|t| delim.push_str(&t.to_string()));
                },

                Some(SingleQuote) => {
                    quoted = true;
                    for t in iter.single_quoted(start_pos) {
                        delim.push_str(&try!(t).to_string());
                    }
                },

                Some(DoubleQuote) => {
                    quoted = true;
                    let mut iter = iter.double_quoted(start_pos);
                    while let Some(next) = iter.next() {
                        match try!(next) {
                            Backslash => {
                                match iter.next() {
                                    Some(Ok(tok@Dollar))      |
                                    Some(Ok(tok@Backtick))    |
                                    Some(Ok(tok@DoubleQuote)) |
                                    Some(Ok(tok@Backslash))   |
                                    Some(Ok(tok@Newline))     => delim.push_str(&tok.to_string()),

                                    Some(t) => {
                                        let t = try!(t);
                                        delim.push_str(&Backslash.to_string());
                                        delim.push_str(&t.to_string());
                                    },

                                    None => delim.push_str(&Backslash.to_string()),
                                }
                            },

                            t => delim.push_str(&t.to_string()),
                        }
                    }
                },

                // Having backticks in a heredoc delimeter is something the major shells all
                // disagree on. Half of them (bash included) treat the precense of backticks
                // as indicating that the delimeter is quoted (and the body isn't expanded).
                // Although the POSIX standard does not indicate backticks are a form of quoting
                // its not unreasonable for them to be seen as such a way. Moreover, the presense
                // of backticks in a heredoc delimeter isn't something that is seen often, so there
                // probably won't be many problems in using this non-portable style, so we will
                // treat their presense as an indication to NOT expand the body.
                //
                // Backslashes inside the double quotes should retain their literal meaning unless
                // followed by \, $, or `, according to the POSIX standard. bash is the only major
                // shell which does not follow this rule. Since the majority of the shells seeem to
                // follow these escaping rules (one way or another), and since the standard
                // indicates this course of action, we will adopt it as well. Again, most shell
                // script maintainers probably avoid using escaping in heredoc delimeters to avoid
                // confusing, and non-portable style so picking any approach shouldn't cause too
                // many issues that cannot be fixed in a future version or with some compatability
                // flag.
                //
                // TL;DR: balanced backticks are allowed in delimeter, they cause the body to NOT
                // be expanded, and backslashes are only removed if followed by \, $, or `.
                Some(Backtick) => {
                    quoted = true;
                    delim.push_str(&Backtick.to_string());
                    for t in iter.backticked_remove_backslashes(start_pos) {
                        delim.push_str(&try!(t).to_string());
                    }
                    delim.push_str(&Backtick.to_string());
                },

                Some(t) => delim.push_str(&t.to_string()),
                None => break,
            }
        }

        if delim.is_empty() {
            return Err(self.make_unexpected_err());
        }

        delim.shrink_to_fit();
        let (delim, quoted) = (delim, quoted);
        let delim_len = delim.len();
        let delim_r = delim.clone() + "\r";
        let delim_r_len = delim_r.len();

        // Here we will fast-forward to the next newline and capture the heredoc's
        // body that comes after it. Then we'll store these tokens in a safe place
        // and continue parsing them later. Although it may seem inefficient to do
        // this instead of parsing input until all pending heredocs are resolved,
        // we would have to do even more bookkeeping to store pending and resolved
        // heredocs, especially if we want to keep the builder unaware of our
        // shenanigans (since it *could* be keeping some internal state of what
        // we feed it).
        let saved_pos = self.iter.pos();
        let mut saved_tokens = Vec::new();
        while self.iter.peek().is_some() {
            // Make sure we save all tokens until the next UNQUOTED newilne
            if let Some(&Newline) = self.iter.peek() {
                saved_tokens.push(self.iter.next().unwrap());
                break;
            }

            for t in self.iter.balanced() { saved_tokens.push(try!(t)); }
        }

        let heredoc_start_pos = self.iter.pos();
        let mut heredoc = Vec::new();
        'heredoc: loop {
            let mut line_start_pos = self.iter.pos();
            let mut line: Vec<Token> = Vec::new();
            'line: loop {
                if strip_tabs {
                    if let Some(&Whitespace(_)) = self.iter.peek() {
                        if let Some(Whitespace(w)) = self.iter.next() {
                            let mut w_iter = w.chars().peekable();
                            let mut tabs: String = String::with_capacity(w.len());

                            while let Some(&'\t') = w_iter.peek() {
                                tabs.push(w_iter.next().unwrap());
                            }

                            line_start_pos.advance(&Whitespace(tabs));

                            let s: String = w_iter.collect();
                            if !s.is_empty() {
                                line.push(Whitespace(s));
                            }
                        } else {
                            unreachable!()
                        }
                    }
                }

                let next = self.iter.next();
                match next {
                    // If we haven't grabbed any input we must have hit EOF
                    // which should delimit the heredoc body
                    None if line.is_empty() => break 'heredoc,

                    // Otherwise, if we have a partial line captured, check
                    // whether it happens to be the delimeter, and append it
                    // to the body if it isn't
                    None | Some(Newline) => {
                        // Do a quick length check on the line. Odds are that heredoc lines
                        // will be much longer than the delimeter itself, and it could get
                        // slow to stringify each and every line (and alloc it in memory)
                        // when token length checks are available without converting to strings.
                        let mut line_len = 0;
                        for t in &line {
                            line_len += t.len();
                            if line_len > delim_r_len {
                                break;
                            }
                        }

                        // NB A delimeter like "\eof" becomes [Name(e), Name(of)], which
                        // won't compare to [Name(eof)], forcing us to do a string comparison
                        // NB We must also do a check using \r\n line endings. Although we could
                        // lex \r\n as a Newline token, doing so would complicate keeping track
                        // of positions in the source, as we could have one or two byte Newlines,
                        // or two different tokens to deal with.
                        if line_len == delim_len || line_len == delim_r_len {
                            let line_str = line.iter().map(|t| t.to_string()).collect::<Vec<String>>().concat();

                            if line_str == delim || line_str == delim_r {
                                break 'heredoc;
                            }
                        }

                        if next == Some(Newline) { line.push(Newline); }
                        break 'line;
                    },

                    Some(t) => line.push(t),
                }
            }

            heredoc.push((line, line_start_pos));
        }

        self.iter.backup_buffered_tokens(saved_tokens, saved_pos);

        let body = if quoted {
            let body = heredoc.into_iter()
                              .flat_map(|(t,_)| t)
                              .map(|t| t.to_string())
                              .collect::<Vec<String>>()
                              .concat();
            Single(Simple(SimpleWordKind::Literal(body)))
        } else {
            let mut tok_iter = iter::TokenIter::with_position(::std::iter::empty(), heredoc_start_pos);
            while let Some((line, pos)) = heredoc.pop() {
                tok_iter.backup_buffered_tokens(line, pos);
            }

            // Dodge an "ICE": If we don't erase the type of the builder, the type of the parser
            // below will will be of type Parser<_, &mut B>, whose methods that create a sub-parser
            // create a ones whose type will be Parser<_, &mut &mut B>, ad infinitum, causing rustc
            // to overflow its stack. By erasing the builder's type the sub-parser's type is always
            // fixed and rustc will remain happy :)
            let b: &mut Builder<Command=B::Command, Word=B::Word, Redirect=B::Redirect>
                = &mut self.builder;
            let mut parser = Parser::with_token_iter_and_builder(tok_iter, b);
            let mut body = try!(parser.word_interpolated_raw(None, heredoc_start_pos));

            if body.len() > 1 {
                Concat(body.into_iter().map(Simple).collect())
            } else {
                let body = body.pop().unwrap_or(SimpleWordKind::Literal(String::new()));
                Single(Simple(body))
            }
        };

        let word = try!(self.builder.word(body));
        Ok(try!(self.builder.redirect(builder::RedirectKind::Heredoc(src_fd, word))))
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
    /// (e.g. malformed parameter).
    pub fn word(&mut self) -> Result<Option<B::Word>> {
        let ret = try!(self.word_preserve_trailing_whitespace());
        self.skip_whitespace();
        Ok(ret)
    }

    /// Identical to `Parser::word()` but preserves trailing whitespace after the word.
    pub fn word_preserve_trailing_whitespace(&mut self) -> Result<Option<B::Word>> {
        let w = match try!(self.word_preserve_trailing_whitespace_raw()) {
            Some(w) => Some(try!(self.builder.word(w))),
            None => None,
        };
        Ok(w)
    }

    /// Identical to `Parser::word_preserve_trailing_whitespace()` but does
    /// not pass the result to the AST builder.
    fn word_preserve_trailing_whitespace_raw(&mut self)
        -> Result<Option<ComplexWordKind<B::Command>>>
    {
        self.skip_whitespace();

        // Make sure we don't consume comments,
        // e.g. if a # is at the start of a word.
        if let Some(&Pound) = self.iter.peek() {
            return Ok(None);
        }

        let mut words = Vec::new();
        loop {
            match self.iter.peek() {
                Some(&CurlyOpen)          |
                Some(&CurlyClose)         |
                Some(&SquareOpen)         |
                Some(&SquareClose)        |
                Some(&SingleQuote)        |
                Some(&DoubleQuote)        |
                Some(&Pound)              |
                Some(&Star)               |
                Some(&Question)           |
                Some(&Tilde)              |
                Some(&Bang)               |
                Some(&Backslash)          |
                Some(&Percent)            |
                Some(&Dash)               |
                Some(&Equals)             |
                Some(&Plus)               |
                Some(&Colon)              |
                Some(&At)                 |
                Some(&Caret)              |
                Some(&Slash)              |
                Some(&Comma)              |
                Some(&Name(_))            |
                Some(&Literal(_))         => {},

                Some(&Backtick) => {
                    words.push(Simple(try!(self.backticked_raw())));
                    continue;
                },

                Some(&Dollar)             |
                Some(&ParamPositional(_)) => {
                    words.push(Simple(try!(self.parameter_raw())));
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

                None => break,
            }

            let start_pos = self.iter.pos();
            let w = match self.iter.next().unwrap() {
                // Unless we are explicitly parsing a brace group, `{` and `}` should
                // be treated as literals.
                //
                // Also, comments are only recognized where a Newline is valid, thus '#'
                // becomes a literal if it occurs in the middle of a word.
                tok@Bang       |
                tok@Pound      |
                tok@Percent    |
                tok@Dash       |
                tok@Equals     |
                tok@Plus       |
                tok@At         |
                tok@Caret      |
                tok@Slash      |
                tok@Comma      |
                tok@CurlyOpen  |
                tok@CurlyClose => Simple(SimpleWordKind::Literal(tok.to_string())),

                Name(s)    |
                Literal(s) => Simple(SimpleWordKind::Literal(s)),

                Star        => Simple(SimpleWordKind::Star),
                Question    => Simple(SimpleWordKind::Question),
                Tilde       => Simple(SimpleWordKind::Tilde),
                SquareOpen  => Simple(SimpleWordKind::SquareOpen),
                SquareClose => Simple(SimpleWordKind::SquareClose),
                Colon       => Simple(SimpleWordKind::Colon),

                Backslash => match self.iter.next() {
                    Some(Newline) => break, // escaped newlines become whitespace and a delimiter
                    Some(t) => Simple(SimpleWordKind::Escaped(t.to_string())),
                    None => break, // Can't escape EOF, just ignore the slash
                },

                SingleQuote => {
                    let mut buf = String::new();
                    for t in self.iter.single_quoted(start_pos) {
                        buf.push_str(&try!(t).to_string());
                    }

                    SingleQuoted(buf)
                },

                DoubleQuote => DoubleQuoted(
                    try!(self.word_interpolated_raw(Some((DoubleQuote, DoubleQuote)), start_pos))
                ),

                // Parameters and backticks should have been
                // handled while peeking above.
                Backtick           |
                Dollar             |
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
            Some(Single(words.pop().unwrap()))
        } else {
            Some(Concat(words))
        };

        Ok(ret)
    }

    /// Parses tokens in a way similar to how double quoted strings may be interpreted.
    ///
    /// Parameters/substitutions are parsed as normal, backslashes keep their literal
    /// meaning unless they preceed $, `, ", \, \n, or the specified delimeter, while
    /// all other tokens are consumed as literals.
    ///
    /// Tokens will continue to be consumed until a specified delimeter is reached
    /// (which is also consumed). If EOF is reached before a delimeter can be found,
    /// an error will result. If a `None` is provided as a delimeter tokens will be
    /// consumed until EOF is reached and no error will result.
    ///
    /// `delim` argument structure is Option<(open token, close token)>. The close
    /// token indicates when to stop parsing the word, while the open token will be
    /// used to construct a `ParseError::Unmatched` error.
    fn word_interpolated_raw(&mut self, delim: Option<(Token, Token)>, start_pos: SourcePos)
        -> Result<Vec<SimpleWordKind<B::Command>>>
    {
        let (delim_open, delim_close) = match delim {
            Some((o,c)) => (Some(o), Some(c)),
            None => (None, None),
        };

        let mut words = Vec::new();
        let mut buf = String::new();
        loop {
            if self.iter.peek() == delim_close.as_ref() {
                self.iter.next();
                break;
            }

            macro_rules! store {
                ($word:expr) => {{
                    if !buf.is_empty() {
                        words.push(SimpleWordKind::Literal(buf));
                        buf = String::new();
                    }
                    words.push($word);
                }}
            }

            // Make sure we don't consume any $ (or any specific parameter token)
            // we find since the `parameter` method expects to consume them.
            match self.iter.peek() {
                Some(&Dollar)             |
                Some(&ParamPositional(_)) => {
                    store!(try!(self.parameter_raw()));
                    continue;
                },

                Some(&Backtick) => {
                    store!(try!(self.backticked_raw()));
                    continue;
                },

                _ => {},
            }

            match self.iter.next() {
                // Backslashes only escape a few tokens when double-quoted-type words
                Some(Backslash) => {
                    let special = {
                        let peeked = self.iter.peek();
                        [Dollar, Backtick, DoubleQuote, Backslash, Newline].iter().any(|t| Some(t) == peeked)
                    };

                    if special || self.iter.peek() == delim_close.as_ref() {
                        store!(SimpleWordKind::Escaped(self.iter.next().unwrap().to_string()))
                    } else {
                        buf.push_str(&Backslash.to_string());
                    }
                },

                Some(Dollar) => unreachable!(), // Sanity
                Some(Backtick) => unreachable!(), // Sanity

                Some(t) => buf.push_str(&t.to_string()),
                None => match delim_open {
                    Some(delim) => return Err(ParseError::Unmatched(delim, start_pos)),
                    None => break,
                },
            }
        }

        if !buf.is_empty() {
            words.push(SimpleWordKind::Literal(buf));
        }

        Ok(words)
    }

    /// Parses a command subsitution in the form \`cmd\`.
    ///
    /// Any backslashes that are immediately followed by \, $, or ` are removed
    /// before the contents inside the original backticks are recursively parsed
    /// as a command.
    pub fn backticked_command_substitution(&mut self) -> Result<B::Word> {
        let word = try!(self.backticked_raw());
        Ok(try!(self.builder.word(Single(Simple(word)))))
    }

    /// Identical to `Parser::backticked_command_substitution`, except but does not pass the
    /// result to the AST builder.
    fn backticked_raw(&mut self) -> Result<SimpleWordKind<B::Command>> {
        let backtick_pos = self.iter.pos();
        eat!(self, { Backtick => {} });

        let tok_iter = try!(self.iter.token_iter_from_backticked_with_removed_backslashes(backtick_pos));

        // Dodge an "ICE": If we don't erase the type of the builder, the type of the parser
        // below will will be of type Parser<_, &mut B>, whose methods that create a sub-parser
        // create a ones whose type will be Parser<_, &mut &mut B>, ad infinitum, causing rustc
        // to overflow its stack. By erasing the builder's type the sub-parser's type is always
        // fixed and rustc will remain happy :)
        let b: &mut Builder<Command=B::Command, Word=B::Word, Redirect=B::Redirect>
            = &mut self.builder;
        let mut parser = Parser::with_token_iter_and_builder(tok_iter, b);

        let mut cmds = Vec::new();
        while let Some(c) = try!(parser.complete_command()) {
            cmds.push(c);
        }

        Ok(SimpleWordKind::CommandSubst(cmds))
    }

    /// Parses a parameters such as `$$`, `$1`, `$foo`, etc, or
    /// parameter substitutions such as `$(cmd)`, `${param-word}`, etc.
    ///
    /// Since it is possible that a leading `$` is not followed by a valid
    /// parameter, the `$` should be treated as a literal. Thus this method
    /// returns an `Word`, which will capture both cases where a literal or
    /// parameter is parsed.
    pub fn parameter(&mut self) -> Result<B::Word> {
        let param = try!(self.parameter_raw());
        Ok(try!(self.builder.word(Single(Simple(param)))))
    }

    /// Identical to `Parser::parameter()` but does not pass the result to the AST builder.
    fn parameter_raw(&mut self) -> Result<SimpleWordKind<B::Command>> {
        use syntax::ast::Parameter;
        use syntax::ast::builder::ParameterSubstitutionKind::*;

        let start_pos = self.iter.pos();
        match self.iter.next() {
            Some(ParamPositional(p)) => return Ok(SimpleWordKind::Param(Parameter::Positional(p as u32))),

            Some(Dollar) => {
                match self.iter.peek() {
                    Some(&Star)      |
                    Some(&Pound)     |
                    Some(&Question)  |
                    Some(&Dollar)    |
                    Some(&Bang)      |
                    Some(&Dash)      |
                    Some(&At)        |
                    Some(&Name(_))   |
                    Some(&ParenOpen) |
                    Some(&CurlyOpen) => {},
                    _ => return Ok(SimpleWordKind::Literal(Dollar.to_string())),
                }
            },

            Some(t) => return Err(ParseError::Unexpected(t, start_pos)),
            None => return Err(ParseError::UnexpectedEOF),
        }

        let start_pos = self.iter.pos();
        let param_word = |parser: &mut Self| -> Result<Option<Box<ComplexWordKind<B::Command>>>> {
            let mut words = try!(parser.word_interpolated_raw(Some((CurlyOpen, CurlyClose)), start_pos));
            let ret = if words.is_empty() {
                None
            } else if words.len() == 1 {
                Some(Single(Simple(words.pop().unwrap())))
            } else {
                Some(Concat(words.into_iter().map(Simple).collect()))
            };

            Ok(ret.map(Box::new))
        };

        let param = match self.iter.peek() {
            Some(&ParenOpen) => {
                let is_arith = {
                    let mut peeked = self.iter.peek_many(2).into_iter();
                    peeked.next();
                    Some(&ParenOpen) == peeked.next()
                };

                let subst = if is_arith {
                    eat!(self, { ParenOpen => {} });
                    eat!(self, { ParenOpen => {} });

                    // If we hit a paren right off the bat either the body is empty
                    // or there is a stray paren which will result in an error either
                    // when we look for the closing parens or sometime after.
                    self.skip_whitespace();
                    let subst = if let Some(&ParenClose) = self.iter.peek() {
                        None
                    } else {
                        Some(try!(self.arithmetic_substitution()))
                    };

                    // Some shells allow the closing parens to have whitespace in between
                    self.skip_whitespace();
                    eat!(self, { ParenClose => {} });
                    self.skip_whitespace();
                    eat!(self, { ParenClose => {} });

                    Arith(subst)
                } else {
                    Command(try!(self.subshell_internal(true)))
                };

                return Ok(SimpleWordKind::Subst(subst));
            },

            Some(&CurlyOpen) => {
                self.iter.next();
                let param = if let Some(&Pound) = self.iter.peek() {
                    self.iter.next();
                    match self.iter.peek() {
                        Some(&Percent) => {
                            self.iter.next();
                            if let Some(&Percent) = self.iter.peek() {
                                self.iter.next();
                                Err(RemoveLargestSuffix(Parameter::Pound, try!(param_word(self))))
                            } else {
                                Err(RemoveSmallestSuffix(Parameter::Pound, try!(param_word(self))))
                            }
                        },

                        Some(&Pound) => {
                            self.iter.next();
                            if let Some(&Pound) = self.iter.peek() {
                                self.iter.next();
                                Err(RemoveLargestPrefix(Parameter::Pound, try!(param_word(self))))
                            } else {
                                match try!(param_word(self)) {
                                    w@Some(_) => Err(RemoveSmallestPrefix(Parameter::Pound, w)),
                                    None => Err(Len(Parameter::Pound)),
                                }
                            }
                        },

                        Some(&Colon)      |
                        Some(&Dash)       |
                        Some(&Equals)     |
                        Some(&Question)   |
                        Some(&Plus)       |
                        Some(&CurlyClose) => Ok(Parameter::Pound),

                        _ => {
                            let param = try!(self.parameter_inner());
                            eat!(self, { CurlyClose => { Err(Len(param)) } })
                        },
                    }
                } else {
                    let param = try!(self.parameter_inner());
                    if let Some(&Percent) = self.iter.peek() {
                        self.iter.next();
                        if let Some(&Percent) = self.iter.peek() {
                            self.iter.next();
                            Err(RemoveLargestSuffix(param, try!(param_word(self))))
                        } else {
                            Err(RemoveSmallestSuffix(param, try!(param_word(self))))
                        }
                    } else if let Some(&Pound) = self.iter.peek() {
                        self.iter.next();
                        if let Some(&Pound) = self.iter.peek() {
                            self.iter.next();
                            Err(RemoveLargestPrefix(param, try!(param_word(self))))
                        } else {
                            Err(RemoveSmallestPrefix(param, try!(param_word(self))))
                        }
                    } else {
                        Ok(param)
                    }
                };

                // Handle any other substitutions unless we already found a remove prefix/suffix one
                let param = match param {
                    Err(p) => Err(p),
                    Ok(p) => if let Some(&CurlyClose) = self.iter.peek() { Ok(p) } else {
                        let has_colon = if let Some(&Colon) = self.iter.peek() {
                            self.iter.next();
                            true
                        } else {
                            false
                        };

                        let op_pos = self.iter.pos();
                        let op = match self.iter.next() {
                            Some(tok@Dash)     |
                            Some(tok@Equals)   |
                            Some(tok@Question) |
                            Some(tok@Plus)     => tok,
                            Some(t) => return Err(ParseError::BadSubst(t, op_pos)),
                            None => return Err(ParseError::UnexpectedEOF),
                        };

                        let word = try!(param_word(self));
                        let maybe_len = p == Parameter::Pound && !has_colon && word.is_none();

                        // We must carefully check if we get ${#-} or ${#?}, in which case
                        // we have parsed a Len substitution and not something else
                        if maybe_len && op == Dash {
                            Err(Len(Parameter::Dash))
                        } else if maybe_len && op == Question {
                            Err(Len(Parameter::Question))
                        } else {
                            match op {
                                Dash     => Err(Default(has_colon, p, word)),
                                Equals   => Err(Assign(has_colon, p, word)),
                                Question => Err(Error(has_colon, p, word)),
                                Plus     => Err(Alternative(has_colon, p, word)),
                                _ => unreachable!(),
                            }
                        }
                    },
                };

                match param {
                    // Substitutions have already consumed the closing CurlyClose token
                    Err(subst) => return Ok(SimpleWordKind::Subst(subst)),
                    // Regular parameters, however, have not
                    Ok(p) => eat!(self, { CurlyClose => { p } }),
                }
            },

            _ => try!(self.parameter_inner()),
        };

        Ok(SimpleWordKind::Param(param))
    }

    /// Parses a valid parameter that can appear inside a set of curly braces.
    fn parameter_inner(&mut self) -> Result<ast::Parameter> {
        use syntax::ast::Parameter;

        let start_pos = self.iter.pos();
        let param = match self.iter.next() {
            Some(Star)     => Parameter::Star,
            Some(Pound)    => Parameter::Pound,
            Some(Question) => Parameter::Question,
            Some(Dollar)   => Parameter::Dollar,
            Some(Bang)     => Parameter::Bang,
            Some(Dash)     => Parameter::Dash,
            Some(At)       => Parameter::At,

            Some(Name(n)) => Parameter::Var(n),
            Some(Literal(s)) => match u32::from_str(&s) {
                Ok(n)  => Parameter::Positional(n),
                Err(_) => return Err(ParseError::BadSubst(Literal(s), start_pos)),
            },

            Some(t) => return Err(ParseError::BadSubst(t, start_pos)),
            None => return Err(ParseError::UnexpectedEOF),
        };

        Ok(param)
    }

    /// Parses any number of sequential commands between the `do` and `done`
    /// reserved words. Each of the reserved words must be a literal token, and cannot be
    /// quoted or concatenated.
    pub fn do_group(&mut self) -> Result<Vec<B::Command>> {
        let start_pos = self.iter.pos();
        try!(self.reserved_word(&["do"]).map_err(|_| self.make_unexpected_err()));
        let result = try!(self.command_list(&["done"], &[]));
        try!(self.reserved_word(&["done"])
             .or(Err(ParseError::IncompleteCmd("do", start_pos, "done", self.iter.pos()))));
        Ok(result)
    }

    /// Parses any number of sequential commands between balanced `{` and `}`
    /// reserved words. Each of the reserved words must be a literal token, and cannot be quoted.
    pub fn brace_group(&mut self) -> Result<Vec<B::Command>> {
        // CurlyClose must be encountered as a stand alone word,
        // even though it is represented as its own token
        let start_pos = self.iter.pos();
        try!(self.reserved_token(&[CurlyOpen]));
        let cmds = try!(self.command_list(&[], &[CurlyClose]));
        try!(self.reserved_token(&[CurlyClose]).or(Err(ParseError::Unmatched(CurlyOpen, start_pos))));
        Ok(cmds)
    }

    /// Parses any number of sequential commands between balanced `(` and `)`.
    ///
    /// It is considered an error if no commands are present inside the subshell.
    pub fn subshell(&mut self) -> Result<Vec<B::Command>> {
        self.subshell_internal(false)
    }

    /// Like `Parser::subshell` but allows the caller to specify
    /// if an empty body constitutes an error or not.
    fn subshell_internal(&mut self, empty_body_ok: bool) -> Result<Vec<B::Command>> {
        let start_pos = self.iter.pos();
        eat!(self, { ParenOpen => {} });

        // Paren's are always special tokens, hence they aren't
        // reserved words, and thus the `command_list` method doesn't apply.
        let mut cmds = Vec::new();
        loop {
            let comments = self.linebreak();
            if !comments.is_empty() {
                try!(self.builder.comments(comments));
            }

            if let Some(&ParenClose) = self.iter.peek() { break; }
            match try!(self.complete_command()) {
                Some(c) => cmds.push(c),
                None => break,
            }
        }

        match self.iter.peek() {
            Some(&ParenClose) if empty_body_ok || !cmds.is_empty() => {
                self.iter.next();
                Ok(cmds)
            },
            Some(_) => Err(self.make_unexpected_err()),
            None => Err(ParseError::Unmatched(ParenOpen, start_pos)),
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
    pub fn compound_command(&mut self) -> Result<B::Command> {
        self.compound_command_internal(None)
    }

    /// Slightly optimized version of `Parse::compound_command` that will not
    /// check an upcoming reserved word if the caller already knows the answer.
    fn compound_command_internal(&mut self, kw: Option<CompoundCmdKeyword>) -> Result<B::Command> {
        let cmd = match kw.or_else(|| self.next_compound_command_type()) {
            Some(CompoundCmdKeyword::If) => {
                let fragments = try!(self.if_command());
                let io = try!(self.redirect_list());
                try!(self.builder.if_command(fragments, io))
            },

            Some(CompoundCmdKeyword::While) |
            Some(CompoundCmdKeyword::Until) => {
                let (until, guard_body_pair) = try!(self.loop_command());
                let io = try!(self.redirect_list());
                try!(self.builder.loop_command(until, guard_body_pair, io))
            },

            Some(CompoundCmdKeyword::For) => {
                let for_fragments = try!(self.for_command());
                let io = try!(self.redirect_list());
                try!(self.builder.for_command(for_fragments, io))
            },

            Some(CompoundCmdKeyword::Case) => {
                let fragments = try!(self.case_command());
                let io = try!(self.redirect_list());
                try!(self.builder.case_command(fragments, io))
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

            None => return Err(self.make_unexpected_err()),
        };

        Ok(cmd)
    }

    /// Parses loop commands like `while` and `until` but does not parse any
    /// redirections that may follow.
    ///
    /// Since they are compound commands (and can have redirections applied to
    /// the entire loop) this method returns the relevant parts of the loop command,
    /// without constructing an AST node, it so that the caller can do so with redirections.
    pub fn loop_command(&mut self) -> Result<(builder::LoopKind, ast::GuardBodyPair<B::Command>)> {
        let start_pos = self.iter.pos();
        let kind = match try!(self.reserved_word(&["while", "until"])
                              .map_err(|_| self.make_unexpected_err())) {
            "while" => builder::LoopKind::While,
            "until" => builder::LoopKind::Until,
            _ => unreachable!(),
        };
        let guard = try!(self.command_list(&["do"], &[]));
        match self.peek_reserved_word(&["do"]) {
            Some(_) => Ok((kind, ast::GuardBodyPair {
                guard: guard,
                body: try!(self.do_group())
            })),
            None => Err(ParseError::IncompleteCmd("while", start_pos, "do", self.iter.pos())),
        }
    }

    /// Parses a single `if` command but does not parse any redirections that may follow.
    ///
    /// Since `if` is a compound command (and can have redirections applied to it) this
    /// method returns the relevant parts of the `if` command, without constructing an
    /// AST node, it so that the caller can do so with redirections.
    pub fn if_command(&mut self) -> Result<builder::IfFragments<B::Command>> {
        let start_pos = self.iter.pos();
        try!(self.reserved_word(&["if"]).map_err(|_| self.make_unexpected_err()));

        macro_rules! missing_fi {
            () => { |_| ParseError::IncompleteCmd("if", start_pos, "fi", self.iter.pos()) }
        }

        macro_rules! missing_then {
            () => { |_| ParseError::IncompleteCmd("if", start_pos, "then", self.iter.pos()) }
        }

        let mut conditionals = Vec::new();
        loop {
            let guard = try!(self.command_list(&["then"], &[]));
            try!(self.reserved_word(&["then"]).map_err(missing_then!()));

            let body = try!(self.command_list(&["elif", "else", "fi"], &[]));
            conditionals.push(ast::GuardBodyPair {
                guard: guard,
                body: body,
            });

            let els = match try!(self.reserved_word(&["elif", "else", "fi"]).map_err(missing_fi!())) {
                "elif" => continue,
                "else" => {
                    let els = try!(self.command_list(&["fi"], &[]));
                    try!(self.reserved_word(&["fi"]).map_err(missing_fi!()));
                    Some(els)
                },
                "fi" => None,
                _ => unreachable!(),
            };

            return Ok(builder::IfFragments { conditionals: conditionals, else_part: els })
        }
    }

    /// Parses a single `for` command but does not parse any redirections that may follow.
    ///
    /// Since `for` is a compound command (and can have redirections applied to it) this
    /// method returns the relevant parts of the `for` command, without constructing an
    /// AST node, it so that the caller can do so with redirections.
    pub fn for_command(&mut self) -> Result<builder::ForFragments<B::Word, B::Command>> {
        let start_pos = self.iter.pos();
        try!(self.reserved_word(&["for"]).map_err(|_| self.make_unexpected_err()));

        self.skip_whitespace();

        match self.iter.peek() {
            Some(&Name(_))    |
            Some(&Literal(_)) => {},
            _ => return Err(self.make_unexpected_err()),
        }

        let var_pos = self.iter.pos();
        let var = match self.iter.next() {
            Some(Name(v)) => v,
            Some(Literal(s)) => return Err(ParseError::BadIdent(s, var_pos)),
            _ => unreachable!(),
        };

        // Make sure that there isn't some extraneous token concatenated
        // ot the Name token which is the variable
        eat!(self, { Whitespace(_) => {} });

        let post_var_comments = self.linebreak();
        let (words, post_words_comments) = if self.peek_reserved_word(&["in"]).is_some() {
            self.reserved_word(&["in"]).unwrap();

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
            let post_words_comments = self.linebreak();
            if !found_semi && post_words_comments.is_empty() {
                return Err(self.make_unexpected_err());
            }

            (Some(words), Some(post_words_comments))
        } else if self.peek_reserved_word(&["do"]).is_none() {
            // If we didn't find an `in` keyword, and we havent hit the body
            // (a `do` keyword), then we can reasonably say the script has
            // words without an `in` keyword.
            return Err(ParseError::IncompleteCmd("for", start_pos, "in", self.iter.pos()));
        } else {
            (None, None)
        };

        if self.peek_reserved_word(&["do"]).is_none() {
            return Err(ParseError::IncompleteCmd("for", start_pos , "do", self.iter.pos()));
        }

        let body = try!(self.do_group());
        Ok(builder::ForFragments {
            var: var,
            post_var_comments: post_var_comments,
            words: words,
            post_words_comments: post_words_comments,
            body: body,
        })
    }

    /// Parses a single `case` command but does not parse any redirections that may follow.
    ///
    /// Since `case` is a compound command (and can have redirections applied to it) this
    /// method returns the relevant parts of the `case` command, without constructing an
    /// AST node, it so that the caller can do so with redirections.
    pub fn case_command(&mut self) -> Result<builder::CaseFragments<B::Word, B::Command>> {
        let start_pos = self.iter.pos();

        macro_rules! missing_in {
            () => { |_| ParseError::IncompleteCmd("case", start_pos, "in", self.iter.pos()); }
        }

        macro_rules! missing_esac {
            () => { |_| ParseError::IncompleteCmd("case", start_pos, "esac", self.iter.pos()); }
        }

        try!(self.reserved_word(&["case"]).map_err(|_| self.make_unexpected_err()));

        let word = match try!(self.word()) {
            Some(w) => w,
            None => return Err(self.make_unexpected_err()),
        };

        let post_word_comments = self.linebreak();
        try!(self.reserved_word(&["in"]).map_err(missing_in!()));

        let mut pre_esac_comments = None;
        let mut arms = Vec::new();
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

            // Make sure we check for missing `esac` here, otherwise if we have EOF
            // trying to parse a word will result in an `UnexpectedEOF` error
            if self.iter.peek().is_none() {
                return Err(()).map_err(missing_esac!());
            }

            let mut patterns = Vec::new();
            loop {
                match try!(self.word()) {
                    Some(p) => patterns.push(p),
                    None => return Err(self.make_unexpected_err()),
                }

                match self.iter.peek() {
                    Some(&Pipe) => {
                        self.iter.next();
                        continue;
                    },

                    Some(&ParenClose) if !patterns.is_empty() => {
                        self.iter.next();
                        break;
                    },

                    // Make sure we check for missing `esac` here, otherwise if we have EOF
                    // trying to parse a word will result in an `UnexpectedEOF` error
                    None => return Err(()).map_err(missing_esac!()),
                    _ => return Err(self.make_unexpected_err()),
                }
            }

            // NB: we must capture linebreaks here since `peek_reserved_word`
            // will not consume them, and it could mistake a reserved word for a command.
            let post_pattern_comments = self.linebreak();

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

            let pat_fragments = builder::CasePatternFragments {
                pre_pattern_comments: pre_pat_comments,
                pattern_alternatives: patterns,
                post_pattern_comments: post_pattern_comments,
            };

            arms.push((pat_fragments, cmds));

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
                comments.extend(remaining_comments);
                comments
            },
            None => remaining_comments,
        };

        try!(self.reserved_word(&["esac"]).map_err(missing_esac!()));

        Ok(builder::CaseFragments {
            word: word,
            post_word_comments: post_word_comments,
            arms: arms,
            post_arms_comments: pre_esac_comments,
        })
    }

    /// Parses a single function declaration.
    ///
    /// A function declaration must either begin with the `function` reserved word, or
    /// the name of the function must be followed by `()`. Whitespace is allowed between
    /// the name and `(`, and whitespace is allowed between `()`.
    fn function_declaration(&mut self) -> Result<B::Command> {
        let found_fn = match self.peek_reserved_word(&["function"]) {
            Some(_) => { self.iter.next(); true },
            None => false,
        };

        self.skip_whitespace();

        match self.iter.peek() {
            Some(&Name(_))    |
            Some(&Literal(_)) => {},
            _ => return Err(self.make_unexpected_err()),
        }

        let ident_pos = self.iter.pos();
        let name = match self.iter.next() {
            Some(Name(n)) => n,
            Some(Literal(s)) => return Err(ParseError::BadIdent(s, ident_pos)),
            _ => unreachable!(),
        };

        // If there is no whitespace after the function name, the only valid
        // possibility is for `()` to appear.
        let body = if Some(&ParenOpen) == self.iter.peek() {
            eat!(self, { ParenOpen => {} });
            self.skip_whitespace();
            eat!(self, { ParenClose => {} });
            None
        } else if found_fn && Some(&Newline) == self.iter.peek() {
            // Do nothing, function declaration satisfied
            None
        } else {
            eat!(self, { Whitespace(_) => {} });
            self.skip_whitespace();

            // If we didn't find the function keyword, we MUST find `()` at this time
            if !found_fn {
                eat!(self, { ParenOpen => {} });
                self.skip_whitespace();
                eat!(self, { ParenClose => {} });
                None
            } else if Some(&Newline) == self.iter.peek() {
                // Do nothing, function declaration satisfied
                None
            } else if Some(&ParenOpen) == self.iter.peek() {
                // Otherwise it is possible for there to be a subshell as the body
                let subshell = try!(self.subshell_internal(true));
                if subshell.is_empty() {
                    // Case like `function foo () ...`
                    None
                } else {
                    // Case like `function foo (subshell)`
                    Some(try!(self.builder.subshell(subshell, Vec::new())))
                }
            } else {
                None
            }
        };

        let body = match body {
            Some(subshell) => subshell,
            None => match try!(self.complete_command()) {
                Some(c) => c,
                None => return Err(self.make_unexpected_err()),
            },
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

            let found_backslash_newline = {
                let mut peeked = self.iter.peek_many(2).into_iter();
                Some(&Backslash) == peeked.next() && Some(&Newline) == peeked.next()
            };

            if found_backslash_newline {
                self.iter.next();
                self.iter.next();
            } else {
                break;
            }
        }
    }

    /// Parses zero or more `Token::Newline`s, skipping whitespace but capturing comments.
    #[inline]
    pub fn linebreak(&mut self) -> Vec<builder::Newline> {
        let mut lines = Vec::new();
        while let Some(n) = self.newline() {
            lines.push(n);
        }
        lines
    }

    /// Tries to parse a `Token::Newline` (or a comment) after skipping whitespace.
    pub fn newline(&mut self) -> Option<builder::Newline> {
        self.skip_whitespace();

        match self.iter.peek() {
            Some(&Pound) => {
                let comment = self.iter.by_ref()
                    .take_while(|t| t != &Newline)
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .concat();

                Some(builder::Newline(Some(comment)))
            },

            Some(&Newline) => {
                self.iter.next();
                Some(builder::Newline(None))
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
        if tokens.is_empty() {
            return None;
        }

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
                let mut peeked = self.iter.peek_many(2).into_iter();
                let tok = match peeked.next() {
                    Some(tok) => tok,
                    None => return None,
                };

                let is_delim = match peeked.next() {
                    Some(delim) => delim.is_word_delimiter(),
                    None => true, // EOF is also a valid delimeter
                };

                if is_delim {
                    match tokens.iter().find(|&t| t == tok) {
                        ret@Some(_) => return ret,
                        None => {},
                    }
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
        if words.is_empty() {
            return None;
        }

        self.skip_whitespace();
        let mut peeked = self.iter.peek_many(2).into_iter();
        let tok = match peeked.next() {
            Some(kw) => kw,
            None => return None,
        };

        // EOF is a valid delimeter
        if let Some(delim) = peeked.next() {
            if !delim.is_word_delimiter() {
                return None;
            }
        }

        match *tok {
            Name(ref kw) |
            Literal(ref kw) => words.iter().find(|&w| w == kw).map(|kw| *kw),
            _ => None,
        }
    }

    /// Checks that one of the specified tokens appears as a reserved word
    /// and consumes it, returning the token it matched in case the caller
    /// cares which specific reserved word was found.
    pub fn reserved_token(&mut self, tokens: &[Token]) -> Result<Token> {
        match self.peek_reserved_token(tokens) {
            Some(_) => Ok(self.iter.next().unwrap()),
            None => {
                // If the desired token is next, but we failed to find a reserved
                // token (because the token after it isn't a valid delimeter)
                // then the following token is the unexpected culprit, so we should
                // skip the upcoming one before forming the error.
                let skip_one = {
                    let peeked = self.iter.peek();
                    tokens.iter().any(|t| Some(t) == peeked)
                };

                if skip_one { self.iter.next(); }
                Err(self.make_unexpected_err())
            },
        }
    }

    /// Checks that one of the specified strings appears as a reserved word
    /// and consumes it, returning the string it matched in case the caller
    /// cares which specific reserved word was found.
    pub fn reserved_word<'a>(&mut self, words: &'a [&str]) -> ::std::result::Result<&'a str, ()> {
        match self.peek_reserved_word(words) {
            Some(s) => { self.iter.next(); Ok(s) },
            None => Err(()),
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
    pub fn command_list(&mut self, words: &[&str], tokens: &[Token]) -> Result<Vec<B::Command>> {
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
            Err(self.make_unexpected_err())
        } else {
            Ok(cmds)
        }
    }

    /// Parses the body of any arbitrary arithmetic expression, e.g. `x + $y << 5`.
    /// The caller is responsible for parsing the external `$(( ))` tokens.
    pub fn arithmetic_substitution(&mut self) -> Result<ast::Arithmetic> {
        let mut exprs = Vec::new();
        loop {
            self.skip_whitespace();
            exprs.push(try!(self.arith_assig()));

            eat_maybe!(self, {
                Comma => {};
                _ => { break },
            });
        }

        if exprs.len() == 1 {
            Ok(exprs.pop().unwrap())
        } else {
            Ok(ast::Arithmetic::Sequence(exprs))
        }
    }

    /// Parses expressions such as `var = expr` or `var op= expr`, where `op` is
    /// any of the following operators: *, /, %, +, -, <<, >>, &, |, ^.
    fn arith_assig(&mut self) -> Result<ast::Arithmetic> {
        use syntax::ast::Arithmetic::*;

        self.skip_whitespace();

        let assig = {
            let mut peeked = self.iter.peek_many(5).into_iter().peekable();
            if Some(&&Dollar) == peeked.peek() { peeked.next(); }

            if let Some(&Name(_)) = peeked.next() {
                if let Some(&&Whitespace(_)) = peeked.peek() { peeked.next(); }
                match peeked.next() {
                    Some(&Star)    |
                    Some(&Slash)   |
                    Some(&Percent) |
                    Some(&Plus)    |
                    Some(&Dash)    |
                    Some(&DLess)   |
                    Some(&DGreat)  |
                    Some(&Amp)     |
                    Some(&Pipe)    |
                    Some(&Caret)   => Some(&Equals) == peeked.next(),

                    // Make sure we only recognize $(( x = ...)) but NOT $(( x == ...))
                    Some(&Equals)  => Some(&Equals) != peeked.next(),
                    _ => false,
                }
            } else {
                false
            }
        };

        if !assig {
            return self.arith_ternary();
        }

        let var = try!(self.arith_var());
        self.skip_whitespace();
        let op = match self.iter.next() {
            Some(op@Star)    |
            Some(op@Slash)   |
            Some(op@Percent) |
            Some(op@Plus)    |
            Some(op@Dash)    |
            Some(op@DLess)   |
            Some(op@DGreat)  |
            Some(op@Amp)     |
            Some(op@Pipe)    |
            Some(op@Caret)   => { eat!(self, { Equals => {} }); op },
            Some(op@Equals)  => op,
            _ => unreachable!(),
        };

        let value = Box::new(try!(self.arith_assig()));
        let expr = match op {
            Star    => Box::new(Mult(Box::new(Var(var.clone())), value)),
            Slash   => Box::new(Div(Box::new(Var(var.clone())), value)),
            Percent => Box::new(Modulo(Box::new(Var(var.clone())), value)),
            Plus    => Box::new(Add(Box::new(Var(var.clone())), value)),
            Dash    => Box::new(Sub(Box::new(Var(var.clone())), value)),
            DLess   => Box::new(ShiftLeft(Box::new(Var(var.clone())), value)),
            DGreat  => Box::new(ShiftRight(Box::new(Var(var.clone())), value)),
            Amp     => Box::new(BitwiseAnd(Box::new(Var(var.clone())), value)),
            Pipe    => Box::new(BitwiseOr(Box::new(Var(var.clone())), value)),
            Caret   => Box::new(BitwiseXor(Box::new(Var(var.clone())), value)),
            Equals  => value,
            _ => unreachable!(),
        };
        Ok(Assign(var, expr))
    }

    /// Parses expressions such as `expr ? expr : expr`.
    fn arith_ternary(&mut self) -> Result<ast::Arithmetic> {
        let guard = try!(self.arith_logical_or());
        self.skip_whitespace();
        eat_maybe!(self, {
            Question => {
                let body = try!(self.arith_ternary());
                self.skip_whitespace();
                eat!(self, { Colon => {} });
                let els = try!(self.arith_ternary());
                Ok(ast::Arithmetic::Ternary(Box::new(guard), Box::new(body), Box::new(els)))
            };
            _ => { Ok(guard) },
        })
    }

    /// Parses expressions such as `expr || expr`.
    arith_parse!(arith_logical_or,  arith_logical_and, OrIf  => ast::Arithmetic::LogicalOr);
    /// Parses expressions such as `expr && expr`.
    arith_parse!(arith_logical_and, arith_bitwise_or,  AndIf => ast::Arithmetic::LogicalAnd);
    /// Parses expressions such as `expr | expr`.
    arith_parse!(arith_bitwise_or,  arith_bitwise_xor, Pipe  => ast::Arithmetic::BitwiseOr);
    /// Parses expressions such as `expr ^ expr`.
    arith_parse!(arith_bitwise_xor, arith_bitwise_and, Caret => ast::Arithmetic::BitwiseXor);
    /// Parses expressions such as `expr & expr`.
    arith_parse!(arith_bitwise_and, arith_eq,          Amp   => ast::Arithmetic::BitwiseAnd);

    /// Parses expressions such as `expr == expr` or `expr != expr`.
    #[inline]
    fn arith_eq(&mut self) -> Result<ast::Arithmetic> {
        let mut expr = try!(self.arith_ineq());
        loop {
            self.skip_whitespace();
            let eq_type = eat_maybe!(self, {
                Equals => { true },
                Bang => { false };
                _ => { break }
            });

            eat!(self, { Equals => {} });
            let next = try!(self.arith_ineq());
            expr = if eq_type {
                ast::Arithmetic::Eq(Box::new(expr), Box::new(next))
            } else {
                ast::Arithmetic::NotEq(Box::new(expr), Box::new(next))
            };
        }
        Ok(expr)
    }

    /// Parses expressions such as `expr < expr`,`expr <= expr`,`expr > expr`,`expr >= expr`.
    #[inline]
    fn arith_ineq(&mut self) -> Result<ast::Arithmetic> {
        let mut expr = try!(self.arith_shift());
        loop {
            self.skip_whitespace();
            eat_maybe!(self, {
                Less => {
                    let eq = eat_maybe!(self, { Equals => { true }; _ => { false } });
                    let next = try!(self.arith_shift());

                    expr = if eq {
                        ast::Arithmetic::LessEq(Box::new(expr), Box::new(next))
                    } else {
                        ast::Arithmetic::Less(Box::new(expr), Box::new(next))
                    };
                },
                Great => {
                    let eq = eat_maybe!(self, { Equals => { true }; _ => { false } });
                    let next = try!(self.arith_shift());

                    expr = if eq {
                        ast::Arithmetic::GreatEq(Box::new(expr), Box::new(next))
                    } else {
                        ast::Arithmetic::Great(Box::new(expr), Box::new(next))
                    };
                };
                _ => { break },
            });
        }
        Ok(expr)
    }

    /// Parses expressions such as `expr << expr` or `expr >> expr`.
    arith_parse!(arith_shift, arith_add,
                 DLess  => ast::Arithmetic::ShiftLeft,
                 DGreat => ast::Arithmetic::ShiftRight
    );

    /// Parses expressions such as `expr + expr` or `expr - expr`.
    arith_parse!(arith_add, arith_mult,
                 Plus => ast::Arithmetic::Add,
                 Dash => ast::Arithmetic::Sub
    );

    /// Parses expressions such as `expr * expr`, `expr / expr`, or `expr % expr`.
    arith_parse!(arith_mult, arith_pow,
                 Star    => ast::Arithmetic::Mult,
                 Slash   => ast::Arithmetic::Div,
                 Percent => ast::Arithmetic::Modulo
    );

    /// Parses expressions such as `expr ** expr`.
    fn arith_pow(&mut self) -> Result<ast::Arithmetic> {
        let expr = try!(self.arith_unary_misc());
        self.skip_whitespace();

        // We must be extra careful here because ** has a higher precedence
        // than *, meaning power operations will be parsed before multiplication.
        // Thus we should be absolutely certain we should parse a ** operator
        // and avoid confusing it with a multiplication operation that is yet
        // to be parsed.
        if self.iter.peek_many(2) == [&Star, &Star] {
            eat!(self, { Star => {} });
            eat!(self, { Star => {} });
            Ok(ast::Arithmetic::Pow(Box::new(expr), Box::new(try!(self.arith_pow()))))
        } else {
            Ok(expr)
        }
    }

    /// Parses expressions such as `!expr`, `~expr`, `+expr`, `-expr`, `++var` and `--var`.
    fn arith_unary_misc(&mut self) -> Result<ast::Arithmetic> {
        self.skip_whitespace();
        let expr = eat_maybe!(self, {
            Bang  => { ast::Arithmetic::LogicalNot(Box::new(try!(self.arith_unary_misc()))) },
            Tilde => { ast::Arithmetic::BitwiseNot(Box::new(try!(self.arith_unary_misc()))) },
            Plus  => {
                eat_maybe!(self, {
                    // Although we can optimize this out, we'll let the AST builder handle
                    // optimizations, in case it is interested in such redundant situations.
                    Dash => {
                        let next = try!(self.arith_unary_misc());
                        ast::Arithmetic::UnaryPlus(Box::new(ast::Arithmetic::UnaryMinus(Box::new(next))))
                    },
                    Plus => { ast::Arithmetic::PreIncr(try!(self.arith_var())) };
                    _ => { ast::Arithmetic::UnaryPlus(Box::new(try!(self.arith_unary_misc()))) }
                })
            },

            Dash  => {
                eat_maybe!(self, {
                    // Although we can optimize this out, we'll let the AST builder handle
                    // optimizations, in case it is interested in such redundant situations.
                    Plus => {
                        let next = try!(self.arith_unary_misc());
                        ast::Arithmetic::UnaryMinus(Box::new(ast::Arithmetic::UnaryPlus(Box::new(next))))
                    },
                    Dash => { ast::Arithmetic::PreDecr(try!(self.arith_var())) };
                    _ => { ast::Arithmetic::UnaryMinus(Box::new(try!(self.arith_unary_misc()))) }
                })
            };

            _ => { try!(self.arith_post_incr()) }
        });
        Ok(expr)
    }

    /// Parses expressions such as `(expr)`, numeric literals, `var`, `var++`, or `var--`.
    /// Numeric literals must appear as a single `Literal` token. `Name` tokens will be
    /// treated as variables.
    #[inline]
    fn arith_post_incr(&mut self) -> Result<ast::Arithmetic> {
        self.skip_whitespace();
        eat_maybe!(self, {
            ParenOpen => {
                let expr = try!(self.arithmetic_substitution());
                self.skip_whitespace();
                eat!(self, { ParenClose => {} });
                return Ok(expr);
            }
        });

        let num = if let Some(&Literal(ref s)) = self.iter.peek() {
            if s.starts_with("0x") || s.starts_with("0X") {
                // from_str_radix does not like it when 0x is present
                // in the string to parse, thus we should strip it off.
                // Also, if the string is empty from_str_radix will return
                // an error; shells like bash and zsh treat `0x` as `0x0`
                // so we will do the same.
                let num = &s[2..];
                if num.is_empty() {
                    Some(0)
                } else {
                    isize::from_str_radix(&s[2..], 16).ok()
                }
            } else if s.starts_with("0") {
                isize::from_str_radix(s, 8).ok()
            } else {
                isize::from_str_radix(s, 10).ok()
            }
        } else {
            None
        };

        let expr = match num {
            Some(num) => {
                // Make sure we consume the Token::Literal which holds the number
                self.iter.next();
                ast::Arithmetic::Literal(num)
            },
            None => {
                let var = try!(self.arith_var());

                // We must be extra careful here because post-increment has a higher precedence
                // than addition/subtraction meaning post-increment operations will be parsed
                // before addition. Thus we should be absolutely certain we should parse a
                // post-increment operator and avoid confusing it with an addition operation
                // that is yet to be parsed.
                let post_incr = {
                    self.skip_whitespace();
                    let peeked = self.iter.peek_many(2);
                    peeked == [&Plus, &Plus] || peeked == [&Dash, &Dash]
                };

                if post_incr {
                    eat!(self, {
                        Plus => { eat!(self, { Plus => { ast::Arithmetic::PostIncr(var) } }) },
                        Dash => { eat!(self, { Dash => { ast::Arithmetic::PostDecr(var) } }) },
                    })
                } else {
                    ast::Arithmetic::Var(var)
                }
            }
        };
        Ok(expr)
    }

    /// Parses a variable name in the form `name` or `$name`.
    #[inline]
    fn arith_var(&mut self) -> Result<String> {
        self.skip_whitespace();
        eat_maybe!(self, { Dollar => {} });

        if let Some(&Name(_)) = self.iter.peek() {
            if let Some(Name(n)) = self.iter.next() { Ok(n) } else { unreachable!() }
        } else {
            return Err(self.make_unexpected_err())
        }
    }
}

#[cfg(test)]
pub mod test {
    use std::rc::Rc;
    use syntax::lexer::Lexer;

    use syntax::ast::*;
    use syntax::ast::builder::Newline;
    use syntax::ast::Command::*;
    use syntax::ast::ComplexWord::*;
    use syntax::ast::CompoundCommand::*;
    use syntax::ast::SimpleWord::*;
    use syntax::parse::*;
    use syntax::parse::ParseError::*;
    use syntax::token::Token;

    // Extension errors may not implement Eq/PartialEq, but
    // equality checking is invaluable for testing, so we'll compromise and implement
    // some equality checking for testing.
    impl ::std::cmp::Eq for ParseError {}
    impl ::std::cmp::PartialEq for ParseError {
        fn eq(&self, other: &ParseError) -> bool {
            match (self, other) {
                (&UnexpectedEOF, &UnexpectedEOF) => true,

                (&BadFd(ref a1, ref b1),      &BadFd(ref a2, ref b2))      => a1 == a2 && b1 == b2,
                (&BadIdent(ref a1, ref b1),   &BadIdent(ref a2, ref b2))   => a1 == a2 && b1 == b2,
                (&BadSubst(ref a1, ref b1),   &BadSubst(ref a2, ref b2))   => a1 == a2 && b1 == b2,
                (&Unmatched(ref a1, ref b1),  &Unmatched(ref a2, ref b2))  => a1 == a2 && b1 == b2,
                (&Unexpected(ref a1, ref b1), &Unexpected(ref a2, ref b2)) => a1 == a2 && b1 == b2,

                (&IncompleteCmd(ref a1, ref b1, ref c1, ref d1),
                 &IncompleteCmd(ref a2, ref b2, ref c2, ref d2)) =>
                    a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2,

                (&Custom(_), &Custom(_)) =>
                    panic!("Cannot compare two custom errors without downcasting"),

                _ => false,
            }
        }
    }

    pub fn lit<W, C>(s: &str) -> Word<W, C> {
        Word::Simple(Box::new(Literal(String::from(s))))
    }

    pub fn escaped<W, C>(s: &str) -> Word<W, C> {
        Word::Simple(Box::new(Escaped(String::from(s))))
    }

    pub fn subst<W, C>(s: ParameterSubstitution<W, C>) -> Word<W, C> {
        Word::Simple(Box::new(Subst(Box::new(s))))
    }

    pub fn single_quoted(s: &str) -> TopLevelWord {
        TopLevelWord(Single(Word::SingleQuoted(String::from(s))))
    }

    pub fn double_quoted(s: &str) -> TopLevelWord {
        TopLevelWord(Single(Word::DoubleQuoted(vec!(Literal(String::from(s))))))
    }

    pub fn word(s: &str) -> TopLevelWord {
        TopLevelWord(Single(lit(s)))
    }

    pub fn word_escaped(s: &str) -> TopLevelWord {
        TopLevelWord(Single(escaped(s)))
    }

    pub fn word_subst(s: ParameterSubstitution<TopLevelWord, Command<TopLevelWord>>)
        -> TopLevelWord
    {
        TopLevelWord(Single(subst(s)))
    }

    pub fn word_param(p: Parameter) -> TopLevelWord {
        TopLevelWord(Single(Word::Simple(Box::new(Param(p)))))
    }

    pub fn make_parser(src: &str) -> DefaultParser<Lexer<::std::str::Chars>> {
        DefaultParser::new(Lexer::new(src.chars()))
    }

    fn make_parser_from_tokens(src: Vec<Token>) -> DefaultParser<::std::vec::IntoIter<Token>> {
        DefaultParser::new(src.into_iter())
    }

    fn cmd_args_unboxed(cmd: &str, args: &[&str]) -> Command<TopLevelWord> {
        let cmd = word(cmd);
        let args = args.iter().map(|&a| word(a)).collect();

        Simple(Box::new(SimpleCommand {
            cmd: Some((cmd, args)),
            vars: vec!(),
            io: vec!(),
        }))
    }

    fn cmd_unboxed(cmd: &str) -> Command<TopLevelWord> {
        cmd_args_unboxed(cmd, &[])
    }

    fn cmd(cmd: &str) -> Box<Command<TopLevelWord>> {
        Box::new(cmd_unboxed(cmd))
    }

    fn src(byte: usize, line: usize, col: usize) -> SourcePos {
        SourcePos {
            byte: byte,
            line: line,
            col: col,
        }
    }

    struct SimpleCommandFragments {
        cmd: Option<(TopLevelWord, Vec<TopLevelWord>)>,
        vars: Vec<(String, Option<TopLevelWord>)>,
        io: Vec<Redirect<TopLevelWord>>,
    }

    fn sample_simple_command() -> SimpleCommandFragments {
        SimpleCommandFragments {
            cmd: Some((word("foo"), vec!(
                word("bar"),
                word("baz"),
            ))),
            vars: vec!(
                (String::from("var"), Some(word("val"))),
                (String::from("ENV"), Some(word("true"))),
                (String::from("BLANK"), None),
            ),
            io: vec!(
                Redirect::Clobber(Some(2), word("clob")),
                Redirect::ReadWrite(Some(3), word("rw")),
                Redirect::Read(None, word("in")),
            ),
        }
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
        // Fail to parse "&& baz" which is an error
        assert_eq!(Err(Unexpected(Token::AndIf, src(12, 3, 1))), p.complete_command());
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
        assert_eq!(Err(Unexpected(Token::Bang, src(14, 1, 15))), p.pipeline());
    }

    #[test]
    fn test_comment_cannot_start_mid_whitespace_delimited_word() {
        let mut p = make_parser("hello#world");
        let w = p.word().unwrap().expect("no valid word was discovered");
        assert_eq!(w, word("hello#world"));
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
            Parameter::At,
            Parameter::Star,
            Parameter::Pound,
            Parameter::Question,
            Parameter::Dash,
            Parameter::Dollar,
            Parameter::Bang,
            Parameter::Positional(3),
        );

        let mut p = make_parser("$@$*$#$?$-$$$!$3$");
        for param in words {
            assert_eq!(p.parameter().unwrap(), word_param(param));
        }

        assert_eq!(word("$"), p.parameter().unwrap());
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_short_in_curlies() {
        let words = vec!(
            Parameter::At,
            Parameter::Star,
            Parameter::Pound,
            Parameter::Question,
            Parameter::Dash,
            Parameter::Dollar,
            Parameter::Bang,
            Parameter::Var(String::from("foo")),
            Parameter::Positional(3),
            Parameter::Positional(1000),
        );

        let mut p = make_parser("${@}${*}${#}${?}${-}${$}${!}${foo}${3}${1000}");
        for param in words {
            assert_eq!(p.parameter().unwrap(), word_param(param));
        }

        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_command_substitution() {
        let correct = word_subst(ParameterSubstitution::Command(vec!(
            cmd_args_unboxed("echo", &["hello"]),
            cmd_args_unboxed("echo", &["world"]),
        )));

        assert_eq!(correct, make_parser("$(echo hello; echo world)").parameter().unwrap());
    }

    #[test]
    fn test_parameter_command_substitution_valid_empty_substitution() {
        let correct = word_subst(ParameterSubstitution::Command(vec!()));
        assert_eq!(correct, make_parser("$()").parameter().unwrap());
        assert_eq!(correct, make_parser("$(     )").parameter().unwrap());
        assert_eq!(correct, make_parser("$(\n\n)").parameter().unwrap());
    }

    #[test]
    fn test_parameter_literal_dollar_if_no_param() {
        let mut p = make_parser("$%asdf");
        assert_eq!(word("$"), p.parameter().unwrap());
        assert_eq!(p.word().unwrap().unwrap(), word("%asdf"));
    }

    #[test]
    fn test_parameter_substitution() {
        let words = vec!(
            ParameterSubstitution::Len(Parameter::At),
            ParameterSubstitution::Len(Parameter::Star),
            ParameterSubstitution::Len(Parameter::Pound),
            ParameterSubstitution::Len(Parameter::Question),
            ParameterSubstitution::Len(Parameter::Dash),
            ParameterSubstitution::Len(Parameter::Dollar),
            ParameterSubstitution::Len(Parameter::Bang),
            ParameterSubstitution::Len(Parameter::Var(String::from("foo"))),
            ParameterSubstitution::Len(Parameter::Positional(3)),
            ParameterSubstitution::Len(Parameter::Positional(1000)),
            ParameterSubstitution::Command(vec!(cmd_args_unboxed("echo", &["foo"]))),
        );

        let mut p = make_parser("${#@}${#*}${##}${#?}${#-}${#$}${#!}${#foo}${#3}${#1000}$(echo foo)");
        for param in words {
            let correct = word_subst(param);
            assert_eq!(correct, p.parameter().unwrap());
        }

        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_smallest_suffix() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = word("foo");

        let substs = vec!(
            RemoveSmallestSuffix(At, Some(word.clone())),
            RemoveSmallestSuffix(Star, Some(word.clone())),
            RemoveSmallestSuffix(Pound, Some(word.clone())),
            RemoveSmallestSuffix(Question, Some(word.clone())),
            RemoveSmallestSuffix(Dash, Some(word.clone())),
            RemoveSmallestSuffix(Dollar, Some(word.clone())),
            RemoveSmallestSuffix(Bang, Some(word.clone())),
            RemoveSmallestSuffix(Positional(0), Some(word.clone())),
            RemoveSmallestSuffix(Positional(10), Some(word.clone())),
            RemoveSmallestSuffix(Positional(100), Some(word.clone())),
            RemoveSmallestSuffix(Var(String::from("foo_bar123")), Some(word.clone())),

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
            assert_eq!(word_subst(s), p.parameter().unwrap());
        }

        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_largest_suffix() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = word("foo");

        let substs = vec!(
            RemoveLargestSuffix(At, Some(word.clone())),
            RemoveLargestSuffix(Star, Some(word.clone())),
            RemoveLargestSuffix(Pound, Some(word.clone())),
            RemoveLargestSuffix(Question, Some(word.clone())),
            RemoveLargestSuffix(Dash, Some(word.clone())),
            RemoveLargestSuffix(Dollar, Some(word.clone())),
            RemoveLargestSuffix(Bang, Some(word.clone())),
            RemoveLargestSuffix(Positional(0), Some(word.clone())),
            RemoveLargestSuffix(Positional(10), Some(word.clone())),
            RemoveLargestSuffix(Positional(100), Some(word.clone())),
            RemoveLargestSuffix(Var(String::from("foo_bar123")), Some(word.clone())),

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
            assert_eq!(word_subst(s), p.parameter().unwrap());
        }

        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_smallest_prefix() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = word("foo");

        let substs = vec!(
            RemoveSmallestPrefix(At, Some(word.clone())),
            RemoveSmallestPrefix(Star, Some(word.clone())),
            RemoveSmallestPrefix(Pound, Some(word.clone())),
            RemoveSmallestPrefix(Question, Some(word.clone())),
            RemoveSmallestPrefix(Dash, Some(word.clone())),
            RemoveSmallestPrefix(Dollar, Some(word.clone())),
            RemoveSmallestPrefix(Bang, Some(word.clone())),
            RemoveSmallestPrefix(Positional(0), Some(word.clone())),
            RemoveSmallestPrefix(Positional(10), Some(word.clone())),
            RemoveSmallestPrefix(Positional(100), Some(word.clone())),
            RemoveSmallestPrefix(Var(String::from("foo_bar123")), Some(word.clone())),

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
            assert_eq!(word_subst(s), p.parameter().unwrap());
        }

        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_largest_prefix() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = word("foo");

        let substs = vec!(
            RemoveLargestPrefix(At, Some(word.clone())),
            RemoveLargestPrefix(Star, Some(word.clone())),
            RemoveLargestPrefix(Pound, Some(word.clone())),
            RemoveLargestPrefix(Question, Some(word.clone())),
            RemoveLargestPrefix(Dash, Some(word.clone())),
            RemoveLargestPrefix(Dollar, Some(word.clone())),
            RemoveLargestPrefix(Bang, Some(word.clone())),
            RemoveLargestPrefix(Positional(0), Some(word.clone())),
            RemoveLargestPrefix(Positional(10), Some(word.clone())),
            RemoveLargestPrefix(Positional(100), Some(word.clone())),
            RemoveLargestPrefix(Var(String::from("foo_bar123")), Some(word.clone())),

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
            assert_eq!(word_subst(s), p.parameter().unwrap());
        }

        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_default() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = word("foo");

        let substs = vec!(
            Default(true, At, Some(word.clone())),
            Default(true, Star, Some(word.clone())),
            Default(true, Pound, Some(word.clone())),
            Default(true, Question, Some(word.clone())),
            Default(true, Dash, Some(word.clone())),
            Default(true, Dollar, Some(word.clone())),
            Default(true, Bang, Some(word.clone())),
            Default(true, Positional(0), Some(word.clone())),
            Default(true, Positional(10), Some(word.clone())),
            Default(true, Positional(100), Some(word.clone())),
            Default(true, Var(String::from("foo_bar123")), Some(word.clone())),

            Default(true, At, None),
            Default(true, Star, None),
            Default(true, Pound, None),
            Default(true, Question, None),
            Default(true, Dash, None),
            Default(true, Dollar, None),
            Default(true, Bang, None),
            Default(true, Positional(0), None),
            Default(true, Positional(10), None),
            Default(true, Positional(100), None),
            Default(true, Var(String::from("foo_bar123")), None),
        );

        let src = "${@:-foo}${*:-foo}${#:-foo}${?:-foo}${-:-foo}${$:-foo}${!:-foo}${0:-foo}${10:-foo}${100:-foo}${foo_bar123:-foo}${@:-}${*:-}${#:-}${?:-}${-:-}${$:-}${!:-}${0:-}${10:-}${100:-}${foo_bar123:-}";
        let mut p = make_parser(src);
        for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted

        let substs = vec!(
            Default(false, At, Some(word.clone())),
            Default(false, Star, Some(word.clone())),
            Default(false, Pound, Some(word.clone())),
            Default(false, Question, Some(word.clone())),
            Default(false, Dash, Some(word.clone())),
            Default(false, Dollar, Some(word.clone())),
            Default(false, Bang, Some(word.clone())),
            Default(false, Positional(0), Some(word.clone())),
            Default(false, Positional(10), Some(word.clone())),
            Default(false, Positional(100), Some(word.clone())),
            Default(false, Var(String::from("foo_bar123")), Some(word.clone())),

            Default(false, At, None),
            Default(false, Star, None),
            //Default(false, Pound, None), // ${#-} should be a length check of the `-` parameter
            Default(false, Question, None),
            Default(false, Dash, None),
            Default(false, Dollar, None),
            Default(false, Bang, None),
            Default(false, Positional(0), None),
            Default(false, Positional(10), None),
            Default(false, Positional(100), None),
            Default(false, Var(String::from("foo_bar123")), None),
        );

        let src = "${@-foo}${*-foo}${#-foo}${?-foo}${--foo}${$-foo}${!-foo}${0-foo}${10-foo}${100-foo}${foo_bar123-foo}${@-}${*-}${?-}${--}${$-}${!-}${0-}${10-}${100-}${foo_bar123-}";
        let mut p = make_parser(src);
        for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_error() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = word("foo");

        let substs = vec!(
            Error(true, At, Some(word.clone())),
            Error(true, Star, Some(word.clone())),
            Error(true, Pound, Some(word.clone())),
            Error(true, Question, Some(word.clone())),
            Error(true, Dash, Some(word.clone())),
            Error(true, Dollar, Some(word.clone())),
            Error(true, Bang, Some(word.clone())),
            Error(true, Positional(0), Some(word.clone())),
            Error(true, Positional(10), Some(word.clone())),
            Error(true, Positional(100), Some(word.clone())),
            Error(true, Var(String::from("foo_bar123")), Some(word.clone())),

            Error(true, At, None),
            Error(true, Star, None),
            Error(true, Pound, None),
            Error(true, Question, None),
            Error(true, Dash, None),
            Error(true, Dollar, None),
            Error(true, Bang, None),
            Error(true, Positional(0), None),
            Error(true, Positional(10), None),
            Error(true, Positional(100), None),
            Error(true, Var(String::from("foo_bar123")), None),
        );

        let src = "${@:?foo}${*:?foo}${#:?foo}${?:?foo}${-:?foo}${$:?foo}${!:?foo}${0:?foo}${10:?foo}${100:?foo}${foo_bar123:?foo}${@:?}${*:?}${#:?}${?:?}${-:?}${$:?}${!:?}${0:?}${10:?}${100:?}${foo_bar123:?}";
        let mut p = make_parser(src);
        for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted

        let substs = vec!(
            Error(false, At, Some(word.clone())),
            Error(false, Star, Some(word.clone())),
            Error(false, Pound, Some(word.clone())),
            Error(false, Question, Some(word.clone())),
            Error(false, Dash, Some(word.clone())),
            Error(false, Dollar, Some(word.clone())),
            Error(false, Bang, Some(word.clone())),
            Error(false, Positional(0), Some(word.clone())),
            Error(false, Positional(10), Some(word.clone())),
            Error(false, Positional(100), Some(word.clone())),
            Error(false, Var(String::from("foo_bar123")), Some(word.clone())),

            Error(false, At, None),
            Error(false, Star, None),
            //Error(false, Pound, None), // ${#?} should be a length check of the `?` parameter
            Error(false, Question, None),
            Error(false, Dash, None),
            Error(false, Dollar, None),
            Error(false, Bang, None),
            Error(false, Positional(0), None),
            Error(false, Positional(10), None),
            Error(false, Positional(100), None),
            Error(false, Var(String::from("foo_bar123")), None),
        );

        let src = "${@?foo}${*?foo}${#?foo}${??foo}${-?foo}${$?foo}${!?foo}${0?foo}${10?foo}${100?foo}${foo_bar123?foo}${@?}${*?}${??}${-?}${$?}${!?}${0?}${10?}${100?}${foo_bar123?}";
        let mut p = make_parser(src);
        for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_assign() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = word("foo");

        let substs = vec!(
            Assign(true, At, Some(word.clone())),
            Assign(true, Star, Some(word.clone())),
            Assign(true, Pound, Some(word.clone())),
            Assign(true, Question, Some(word.clone())),
            Assign(true, Dash, Some(word.clone())),
            Assign(true, Dollar, Some(word.clone())),
            Assign(true, Bang, Some(word.clone())),
            Assign(true, Positional(0), Some(word.clone())),
            Assign(true, Positional(10), Some(word.clone())),
            Assign(true, Positional(100), Some(word.clone())),
            Assign(true, Var(String::from("foo_bar123")), Some(word.clone())),

            Assign(true, At, None),
            Assign(true, Star, None),
            Assign(true, Pound, None),
            Assign(true, Question, None),
            Assign(true, Dash, None),
            Assign(true, Dollar, None),
            Assign(true, Bang, None),
            Assign(true, Positional(0), None),
            Assign(true, Positional(10), None),
            Assign(true, Positional(100), None),
            Assign(true, Var(String::from("foo_bar123")), None),
        );

        let src = "${@:=foo}${*:=foo}${#:=foo}${?:=foo}${-:=foo}${$:=foo}${!:=foo}${0:=foo}${10:=foo}${100:=foo}${foo_bar123:=foo}${@:=}${*:=}${#:=}${?:=}${-:=}${$:=}${!:=}${0:=}${10:=}${100:=}${foo_bar123:=}";
        let mut p = make_parser(src);
        for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted

        let substs = vec!(
            Assign(false, At, Some(word.clone())),
            Assign(false, Star, Some(word.clone())),
            Assign(false, Pound, Some(word.clone())),
            Assign(false, Question, Some(word.clone())),
            Assign(false, Dash, Some(word.clone())),
            Assign(false, Dollar, Some(word.clone())),
            Assign(false, Bang, Some(word.clone())),
            Assign(false, Positional(0), Some(word.clone())),
            Assign(false, Positional(10), Some(word.clone())),
            Assign(false, Positional(100), Some(word.clone())),
            Assign(false, Var(String::from("foo_bar123")), Some(word.clone())),

            Assign(false, At, None),
            Assign(false, Star, None),
            Assign(false, Pound, None),
            Assign(false, Question, None),
            Assign(false, Dash, None),
            Assign(false, Dollar, None),
            Assign(false, Bang, None),
            Assign(false, Positional(0), None),
            Assign(false, Positional(10), None),
            Assign(false, Positional(100), None),
            Assign(false, Var(String::from("foo_bar123")), None),
        );

        let src = "${@=foo}${*=foo}${#=foo}${?=foo}${-=foo}${$=foo}${!=foo}${0=foo}${10=foo}${100=foo}${foo_bar123=foo}${@=}${*=}${#=}${?=}${-=}${$=}${!=}${0=}${10=}${100=}${foo_bar123=}";
        let mut p = make_parser(src);
        for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_alternative() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let word = word("foo");

        let substs = vec!(
            Alternative(true, At, Some(word.clone())),
            Alternative(true, Star, Some(word.clone())),
            Alternative(true, Pound, Some(word.clone())),
            Alternative(true, Question, Some(word.clone())),
            Alternative(true, Dash, Some(word.clone())),
            Alternative(true, Dollar, Some(word.clone())),
            Alternative(true, Bang, Some(word.clone())),
            Alternative(true, Positional(0), Some(word.clone())),
            Alternative(true, Positional(10), Some(word.clone())),
            Alternative(true, Positional(100), Some(word.clone())),
            Alternative(true, Var(String::from("foo_bar123")), Some(word.clone())),

            Alternative(true, At, None),
            Alternative(true, Star, None),
            Alternative(true, Pound, None),
            Alternative(true, Question, None),
            Alternative(true, Dash, None),
            Alternative(true, Dollar, None),
            Alternative(true, Bang, None),
            Alternative(true, Positional(0), None),
            Alternative(true, Positional(10), None),
            Alternative(true, Positional(100), None),
            Alternative(true, Var(String::from("foo_bar123")), None),
        );

        let src = "${@:+foo}${*:+foo}${#:+foo}${?:+foo}${-:+foo}${$:+foo}${!:+foo}${0:+foo}${10:+foo}${100:+foo}${foo_bar123:+foo}${@:+}${*:+}${#:+}${?:+}${-:+}${$:+}${!:+}${0:+}${10:+}${100:+}${foo_bar123:+}";
        let mut p = make_parser(src);
        for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted

        let substs = vec!(
            Alternative(false, At, Some(word.clone())),
            Alternative(false, Star, Some(word.clone())),
            Alternative(false, Pound, Some(word.clone())),
            Alternative(false, Question, Some(word.clone())),
            Alternative(false, Dash, Some(word.clone())),
            Alternative(false, Dollar, Some(word.clone())),
            Alternative(false, Bang, Some(word.clone())),
            Alternative(false, Positional(0), Some(word.clone())),
            Alternative(false, Positional(10), Some(word.clone())),
            Alternative(false, Positional(100), Some(word.clone())),
            Alternative(false, Var(String::from("foo_bar123")), Some(word.clone())),

            Alternative(false, At, None),
            Alternative(false, Star, None),
            Alternative(false, Pound, None),
            Alternative(false, Question, None),
            Alternative(false, Dash, None),
            Alternative(false, Dollar, None),
            Alternative(false, Bang, None),
            Alternative(false, Positional(0), None),
            Alternative(false, Positional(10), None),
            Alternative(false, Positional(100), None),
            Alternative(false, Var(String::from("foo_bar123")), None),
        );

        let src = "${@+foo}${*+foo}${#+foo}${?+foo}${-+foo}${$+foo}${!+foo}${0+foo}${10+foo}${100+foo}${foo_bar123+foo}${@+}${*+}${#+}${?+}${-+}${$+}${!+}${0+}${10+}${100+}${foo_bar123+}";
        let mut p = make_parser(src);
        for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }

    #[test]
    fn test_parameter_substitution_words_can_have_spaces_and_escaped_curlies() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let var = Var(String::from("foo_bar123"));
        let word = TopLevelWord(Concat(vec!(
            lit("foo{"),
            escaped("}"),
            lit(" \t\r "),
            escaped("\n"),
            lit("bar \t\r "),
        )));

        let substs = vec!(
            RemoveSmallestSuffix(var.clone(), Some(word.clone())),
            RemoveLargestSuffix(var.clone(), Some(word.clone())),
            RemoveSmallestPrefix(var.clone(), Some(word.clone())),
            RemoveLargestPrefix(var.clone(), Some(word.clone())),
            Default(true, var.clone(), Some(word.clone())),
            Default(false, var.clone(), Some(word.clone())),
            Assign(true, var.clone(), Some(word.clone())),
            Assign(false, var.clone(), Some(word.clone())),
            Error(true, var.clone(), Some(word.clone())),
            Error(false, var.clone(), Some(word.clone())),
            Alternative(true, var.clone(), Some(word.clone())),
            Alternative(false, var.clone(), Some(word.clone())),
        );

        let src = vec!(
            "%",
            "%%",
            "#",
            "##",
            ":-",
            "-",
            ":=",
            "=",
            ":?",
            "?",
            ":+",
            "+",
        );

        for (i, s) in substs.into_iter().enumerate() {
            let src = format!("${{foo_bar123{}foo{{\\}} \t\r \\\nbar \t\r }}", src[i]);
            let mut p = make_parser(&src);
            assert_eq!(word_subst(s), p.parameter().unwrap());
            assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
        }
    }

    #[test]
    fn test_parameter_substitution_words_can_start_with_pound() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let var = Var(String::from("foo_bar123"));
        let word = TopLevelWord(Concat(vec!(
            lit("#foo{"),
            escaped("}"),
            lit(" \t\r "),
            escaped("\n"),
            lit("bar \t\r "),
        )));

        let substs = vec!(
            RemoveSmallestSuffix(var.clone(), Some(word.clone())),
            RemoveLargestSuffix(var.clone(), Some(word.clone())),
            //RemoveSmallestPrefix(var.clone(), Some(word.clone())),
            RemoveLargestPrefix(var.clone(), Some(word.clone())),
            Default(true, var.clone(), Some(word.clone())),
            Default(false, var.clone(), Some(word.clone())),
            Assign(true, var.clone(), Some(word.clone())),
            Assign(false, var.clone(), Some(word.clone())),
            Error(true, var.clone(), Some(word.clone())),
            Error(false, var.clone(), Some(word.clone())),
            Alternative(true, var.clone(), Some(word.clone())),
            Alternative(false, var.clone(), Some(word.clone())),
        );

        let src = vec!(
            "%",
            "%%",
            //"#", // Let's not confuse the pound in the word with a substitution
            "##",
            ":-",
            "-",
            ":=",
            "=",
            ":?",
            "?",
            ":+",
            "+",
        );

        for (i, s) in substs.into_iter().enumerate() {
            let src = format!("${{foo_bar123{}#foo{{\\}} \t\r \\\nbar \t\r }}", src[i]);
            let mut p = make_parser(&src);
            assert_eq!(word_subst(s), p.parameter().unwrap());
            assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
        }
    }

    #[test]
    fn test_parameter_substitution_words_can_be_parameters_or_substitutions_as_well() {
        use syntax::ast::Parameter::*;
        use syntax::ast::ParameterSubstitution::*;

        let var = Var(String::from("foo_bar123"));
        let word = TopLevelWord(Concat(vec!(
            Word::Simple(Box::new(Param(At))),
            subst(RemoveLargestPrefix(
                Var(String::from("foo")),
                Some(word("bar"))
            )),
        )));

        let substs = vec!(
            RemoveSmallestSuffix(var.clone(), Some(word.clone())),
            RemoveLargestSuffix(var.clone(), Some(word.clone())),
            RemoveSmallestPrefix(var.clone(), Some(word.clone())),
            RemoveLargestPrefix(var.clone(), Some(word.clone())),
            Default(true, var.clone(), Some(word.clone())),
            Default(false, var.clone(), Some(word.clone())),
            Assign(true, var.clone(), Some(word.clone())),
            Assign(false, var.clone(), Some(word.clone())),
            Error(true, var.clone(), Some(word.clone())),
            Error(false, var.clone(), Some(word.clone())),
            Alternative(true, var.clone(), Some(word.clone())),
            Alternative(false, var.clone(), Some(word.clone())),
        );

        let src = vec!(
            "%",
            "%%",
            "#",
            "##",
            ":-",
            "-",
            ":=",
            "=",
            ":?",
            "?",
            ":+",
            "+",
        );

        for (i, s) in substs.into_iter().enumerate() {
            let src = format!("${{foo_bar123{}$@${{foo##bar}}}}", src[i]);
            let mut p = make_parser(&src);
            assert_eq!(word_subst(s), p.parameter().unwrap());
            assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
        }
    }

    #[test]
    fn test_parameter_substitution_command_close_paren_need_not_be_followed_by_word_delimeter() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(), io: vec!(),
            cmd: Some((word("foo"), vec!(TopLevelWord(Single(Word::DoubleQuoted(vec!(
                Subst(Box::new(ParameterSubstitution::Command(vec!(cmd_unboxed("bar")))))
            ))))))),
        })));
        assert_eq!(correct, make_parser("foo \"$(bar)\"").complete_command().unwrap());
    }

    #[test]
    fn test_parameter_substitution_invalid() {
        let cases = vec!(
            ("$(( x",     UnexpectedEOF),
            ("${foo",     UnexpectedEOF),
            ("${ foo}",   BadSubst(Token::Whitespace(String::from(" ")), src(2,1,3))),
            ("${foo }",   BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
            ("${foo -}",  BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
            ("${foo =}",  BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
            ("${foo ?}",  BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
            ("${foo +}",  BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
            ("${foo :-}", BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
            ("${foo :=}", BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
            ("${foo :?}", BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
            ("${foo :+}", BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
            ("${foo: -}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
            ("${foo: =}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
            ("${foo: ?}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
            ("${foo: +}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
            ("${foo: %}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
            ("${foo: #}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
            ("${'foo'}",  BadSubst(Token::SingleQuote, src(2,1,3))),
            ("${\"foo\"}", BadSubst(Token::DoubleQuote, src(2,1,3))),
            ("${`foo`}",  BadSubst(Token::Backtick, src(2,1,3))),
        );

        for (s, correct) in cases.into_iter() {
            match make_parser(s).parameter() {
                Ok(w) => panic!("Unexpectedly parsed the source \"{}\" as\n{:?}", s, w),
                Err(ref err) => if err != &correct {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           s, correct, err);
                },
            }
        }
    }

    #[test]
    fn test_redirect_valid_close_without_whitespace() {
        let mut p = make_parser(">&-");
        assert_eq!(Some(Ok(Redirect::DupWrite(None, word("-")))), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_close_with_whitespace() {
        let mut p = make_parser("<&       -");
        assert_eq!(Some(Ok(Redirect::DupRead(None, word("-")))), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_start_with_dash_if_not_dup() {
        let path = word("-test");
        let cases = vec!(
            ("4<-test",  Redirect::Read(Some(4), path.clone())),
            ("4>-test",  Redirect::Write(Some(4), path.clone())),
            ("4<>-test", Redirect::ReadWrite(Some(4), path.clone())),
            ("4>>-test", Redirect::Append(Some(4), path.clone())),
            ("4>|-test", Redirect::Clobber(Some(4), path.clone())),
        );

        for (s, correct) in cases.into_iter() {
            match make_parser(s).redirect() {
                Ok(Some(Ok(ref r))) if *r == correct => {},
                Ok(r) => {
                    panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", s, r, correct)
                },
                Err(err) => panic!("Failed to parse the source \"{}\": {}", s, err),
            }
        }
    }

    #[test]
    fn test_redirect_valid_return_word_if_no_redirect() {
        let mut p = make_parser("hello");
        assert_eq!(Some(Err(word("hello"))), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_return_word_if_src_fd_is_definitely_non_numeric() {
        let mut p = make_parser("123$$'foo'>out");
        let correct = TopLevelWord(Concat(vec!(
            lit("123"),
            Word::Simple(Box::new(Param(Parameter::Dollar))),
            Word::SingleQuoted(String::from("foo")),
        )));
        assert_eq!(Some(Err(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_return_word_if_src_fd_has_escaped_numerics() {
        let mut p = make_parser("\\2>");
        let correct = word_escaped("2");
        assert_eq!(Some(Err(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_dst_fd_can_have_escaped_numerics() {
        let mut p = make_parser(">\\2");
        let correct = Redirect::Write(None, word_escaped("2"));
        assert_eq!(Some(Ok(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_invalid_dup_if_dst_fd_is_definitely_non_numeric() {
        assert_eq!(Err(BadFd(src(2, 1, 3), src(12, 1, 13))), make_parser(">&123$$'foo'").redirect());
    }

    #[test]
    fn test_redirect_valid_dup_return_redirect_if_dst_fd_is_possibly_numeric() {
        let mut p = make_parser(">&123$$$(echo 2)`echo bar`");
        let correct = Redirect::DupWrite(
            None,
            TopLevelWord(Concat(vec!(
                lit("123"),
                Word::Simple(Box::new(Param(Parameter::Dollar))),
                subst(ParameterSubstitution::Command(vec!(cmd_args_unboxed("echo", &["2"])))),
                subst(ParameterSubstitution::Command(vec!(cmd_args_unboxed("echo", &["bar"])))),
            ))),
        );
        assert_eq!(Some(Ok(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_invalid_close_without_whitespace() {
        assert_eq!(Err(BadFd(src(2, 1, 3), src(7, 1, 8))), make_parser(">&-asdf").redirect());
    }

    #[test]
    fn test_redirect_invalid_close_with_whitespace() {
        assert_eq!(Err(BadFd(src(9, 1, 10), src(14, 1, 15))), make_parser("<&       -asdf").redirect());
    }

    #[test]
    fn test_redirect_fd_immediately_preceeding_redirection() {
        let mut p = make_parser("foo 1>>out");
        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some((word("foo"), vec!())),
            vars: vec!(),
            io: vec!(Redirect::Append(Some(1), word("out"))),
        })));
    }

    #[test]
    fn test_redirect_fd_must_immediately_preceed_redirection() {
        let mut p = make_parser("foo 1 <>out");
        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some((word("foo"), vec!(word("1")))),
            vars: vec!(),
            io: vec!(Redirect::ReadWrite(None, word("out"))),
        })));
    }

    #[test]
    fn test_redirect_valid_dup_with_fd() {
        let mut p = make_parser("foo 1>&2");
        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some((word("foo"), vec!())),
            vars: vec!(),
            io: vec!(Redirect::DupWrite(Some(1), word("2"))),
        })));
    }

    #[test]
    fn test_redirect_valid_dup_without_fd() {
        let mut p = make_parser("foo 1 <&2");
        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some((word("foo"), vec!(word("1")))),
            vars: vec!(),
            io: vec!(Redirect::DupRead(None, word("2"))),
        })));
    }

    #[test]
    fn test_redirect_valid_dup_with_whitespace() {
        let mut p = make_parser("foo 1<& 2");
        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some((word("foo"), vec!())),
            vars: vec!(),
            io: vec!(Redirect::DupRead(Some(1), word("2"))),
        })));
    }

    #[test]
    fn test_redirect_valid_single_quoted_dup_fd() {
        let correct = Redirect::DupWrite(Some(1), single_quoted("2"));
        assert_eq!(Some(Ok(correct)), make_parser("1>&'2'").redirect().unwrap());
    }

    #[test]
    fn test_redirect_valid_double_quoted_dup_fd() {
        let correct = Redirect::DupWrite(None, double_quoted("2"));
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
            Token::Dash,
        ));

        let cmd = p.simple_command().unwrap();
        assert_eq!(cmd, Simple(Box::new(SimpleCommand {
            cmd: Some((word("foo"), vec!())),
            vars: vec!(),
            io: vec!(Redirect::DupRead(Some(1234), word("-"))),
        })));
    }

    #[test]
    fn test_redirect_dst_fd_need_not_be_single_token() {
        let mut p = make_parser_from_tokens(vec!(
            Token::GreatAnd,
            Token::Literal(String::from("12")),
            Token::Literal(String::from("34")),
        ));

        let correct = Redirect::DupWrite(None, word("1234"));
        assert_eq!(Some(Ok(correct)), p.redirect().unwrap());
    }

    #[test]
    fn test_redirect_accept_literal_and_name_tokens() {
        let mut p = make_parser_from_tokens(vec!(
            Token::GreatAnd,
            Token::Literal(String::from("12")),
        ));
        assert_eq!(Some(Ok(Redirect::DupWrite(None, word("12")))), p.redirect().unwrap());

        let mut p = make_parser_from_tokens(vec!(
            Token::GreatAnd,
            Token::Name(String::from("12")),
        ));
        assert_eq!(Some(Ok(Redirect::DupWrite(None, word("12")))), p.redirect().unwrap());
    }

    #[test]
    fn test_simple_command_valid_assignments_at_start_of_command() {
        let mut p = make_parser("var=val ENV=true BLANK= foo bar baz");
        let SimpleCommandFragments { cmd, vars, ..} = sample_simple_command();
        let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: vec!() }));
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_assignments_after_start_of_command_should_be_args() {
        let mut p = make_parser("var=val ENV=true BLANK= foo var2=val2 bar baz var3=val3");
        let SimpleCommandFragments { cmd, vars, ..} = sample_simple_command();
        let (cmd, mut args) = cmd.unwrap();
        args.insert(0, word("var2=val2"));
        args.push(word("var3=val3"));
        let correct = Simple(Box::new(SimpleCommand { cmd: Some((cmd, args)), vars: vars, io: vec!() }));
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_redirections_at_start_of_command() {
        let mut p = make_parser("2>|clob 3<>rw <in var=val ENV=true BLANK= foo bar baz");
        let SimpleCommandFragments { cmd, vars, io } = sample_simple_command();
        let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: io }));
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_redirections_at_end_of_command() {
        let mut p = make_parser("var=val ENV=true BLANK= foo bar baz 2>|clob 3<>rw <in");
        let SimpleCommandFragments { cmd, vars, io } = sample_simple_command();
        let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: io }));
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_redirections_throughout_the_command() {
        let mut p = make_parser("2>|clob var=val 3<>rw ENV=true BLANK= foo bar <in baz 4>&-");
        let SimpleCommandFragments { cmd, vars, mut io } = sample_simple_command();
        io.push(Redirect::DupWrite(Some(4), word("-")));
        let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: io }));
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\n")))
        })));

        assert_eq!(correct, make_parser("cat <<eof\nhello\neof\n").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_eof_after_delimiter_allowed() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\n")))
        })));

        assert_eq!(correct, make_parser("cat <<eof\nhello\neof").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_with_empty_body() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word(""))),
        })));

        assert_eq!(correct, make_parser("cat <<eof\neof").complete_command().unwrap());
        assert_eq!(correct, make_parser("cat <<eof\n").complete_command().unwrap());
        assert_eq!(correct, make_parser("cat <<eof").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_eof_acceptable_as_delimeter() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\n")))
        })));

        assert_eq!(correct, make_parser("cat <<eof\nhello\neof").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_does_not_lose_tokens_up_to_next_newline() {
        let mut p = make_parser("cat <<eof1; cat 3<<eof2\nhello\neof1\nworld\neof2");
        let cat = Some((word("cat"), vec!()));
        let first = Simple(Box::new(SimpleCommand {
            cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(None, word("hello\n")))
        }));
        let second = Simple(Box::new(SimpleCommand {
            cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(Some(3), word("world\n")))
        }));

        assert_eq!(Some(first), p.complete_command().unwrap());
        assert_eq!(Some(second), p.complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_space_before_delimeter_allowed() {
        let mut p = make_parser("cat <<   eof1; cat 3<<- eof2\nhello\neof1\nworld\neof2");
        let cat = Some((word("cat"), vec!()));
        let first = Simple(Box::new(SimpleCommand {
            cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(None, word("hello\n")))
        }));
        let second = Simple(Box::new(SimpleCommand {
            cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(Some(3), word("world\n")))
        }));

        assert_eq!(Some(first), p.complete_command().unwrap());
        assert_eq!(Some(second), p.complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_unquoted_delimeter_should_expand_body() {
        let cat = Some((word("cat"), vec!()));
        let expanded = Some(Simple(Box::new(SimpleCommand {
            cmd: cat.clone(), vars: vec!(), io: vec!(
                Redirect::Heredoc(None, TopLevelWord(Concat(vec!(
                    Word::Simple(Box::new(Param(Parameter::Dollar))),
                    lit(" "),
                    subst(ParameterSubstitution::Len(Parameter::Bang)),
                    lit(" "),
                    subst(ParameterSubstitution::Command(vec!(cmd_unboxed("foo")))),
                    lit("\n"),
                )))
            ))
        })));
        let literal = Some(Simple(Box::new(SimpleCommand {
            cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(None, word("$$ ${#!} `foo`\n")))
        })));

        assert_eq!(expanded, make_parser("cat <<eof\n$$ ${#!} `foo`\neof").complete_command().unwrap());
        assert_eq!(literal, make_parser("cat <<'eof'\n$$ ${#!} `foo`\neof").complete_command().unwrap());
        assert_eq!(literal, make_parser("cat <<`eof`\n$$ ${#!} `foo`\n`eof`").complete_command().unwrap());
        assert_eq!(literal, make_parser("cat <<\"eof\"\n$$ ${#!} `foo`\neof").complete_command().unwrap());
        assert_eq!(literal, make_parser("cat <<e\\of\n$$ ${#!} `foo`\neof").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_leading_tab_removal_works() {
        let mut p = make_parser("cat <<-eof1; cat 3<<-eof2\n\t\thello\n\teof1\n\t\t \t\nworld\n\t\teof2");
        let cat = Some((word("cat"), vec!()));
        let first = Simple(Box::new(SimpleCommand {
            cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(None, word("hello\n")))
        }));
        let second = Simple(Box::new(SimpleCommand {
            cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(Some(3), word(" \t\nworld\n")))
        }));

        assert_eq!(Some(first), p.complete_command().unwrap());
        assert_eq!(Some(second), p.complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_leading_tab_removal_works_if_dash_immediately_after_dless() {
        let mut p = make_parser("cat 3<< -eof\n\t\t \t\nworld\n\t\teof\n\t\t-eof\n-eof");
        let correct = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(Some(3), word("\t\t \t\nworld\n\t\teof\n\t\t-eof\n")))
        }));

        assert_eq!(Some(correct), p.complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_unquoted_backslashes_in_delimeter_disappear() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\n")))
        })));

        assert_eq!(correct, make_parser("cat <<e\\ f\\f\nhello\ne ff").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_balanced_single_quotes_in_delimeter() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\n")))
        })));

        assert_eq!(correct, make_parser("cat <<e'o'f\nhello\neof").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_balanced_double_quotes_in_delimeter() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\n")))
        })));

        assert_eq!(correct, make_parser("cat <<e\"\\o${foo}\"f\nhello\ne\\o${foo}f").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_balanced_backticks_in_delimeter() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\n")))
        })));

        assert_eq!(correct, make_parser("cat <<e`\\o\\$\\`\\\\${f}`\nhello\ne`\\o$`\\${f}`").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_balanced_parens_in_delimeter() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\n")))
        })));

        assert_eq!(correct, make_parser("cat <<eof(  )\nhello\neof(  )").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_cmd_subst_in_delimeter() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\n")))
        })));

        assert_eq!(correct, make_parser("cat <<eof$(  )\nhello\neof$(  )").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_param_subst_in_delimeter() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\n")))
        })));
        assert_eq!(correct, make_parser("cat <<eof${  }\nhello\neof${  }").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_skip_past_newlines_in_single_quotes() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!(
                single_quoted("\n"), word("arg")
            ))),
            io: vec!(Redirect::Heredoc(None, word("here\n")))
        })));
        assert_eq!(correct, make_parser("cat <<EOF '\n' arg\nhere\nEOF").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_skip_past_newlines_in_double_quotes() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!(
                double_quoted("\n"),
                word("arg")
            ))),
            io: vec!(Redirect::Heredoc(None, word("here\n")))
        })));
        assert_eq!(correct, make_parser("cat <<EOF \"\n\" arg\nhere\nEOF").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_skip_past_newlines_in_backticks() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!(
                word_subst(ParameterSubstitution::Command(vec!(cmd_unboxed("echo")))),
                word("arg")
            ))),
            io: vec!(Redirect::Heredoc(None, word("here\n")))
        })));
        assert_eq!(correct, make_parser("cat <<EOF `echo \n` arg\nhere\nEOF").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_skip_past_newlines_in_parens() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("here\n")))
        })));
        assert_eq!(correct, make_parser("cat <<EOF; (foo\n); arg\nhere\nEOF").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_skip_past_newlines_in_cmd_subst() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!(
                word_subst(ParameterSubstitution::Command(vec!(cmd_unboxed("foo")))),
                word("arg"),
            ))),
            io: vec!(Redirect::Heredoc(None, word("here\n")))
        })));
        assert_eq!(correct, make_parser("cat <<EOF $(foo\n) arg\nhere\nEOF").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_skip_past_newlines_in_param_subst() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!(
                word_subst(ParameterSubstitution::Assign(
                        false,
                        Parameter::Var(String::from("foo")),
                        Some(word("\n"))
                )),
                word("arg")
            ))),
            io: vec!(Redirect::Heredoc(None, word("here\n")))
        })));
        assert_eq!(correct, make_parser("cat <<EOF ${foo=\n} arg\nhere\nEOF").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_skip_past_escaped_newlines() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!(word("arg")))),
            io: vec!(Redirect::Heredoc(None, word("here\n")))
        })));
        assert_eq!(correct, make_parser("cat <<EOF \\\n arg\nhere\nEOF").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_double_quoted_delim_keeps_backslashe_except_after_specials() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("here\n")))
        })));
        assert_eq!(correct, make_parser("cat <<\"\\EOF\\$\\`\\\"\\\\\"\nhere\n\\EOF$`\"\\\n")
                   .complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_unquoting_only_removes_outer_quotes_and_backslashes() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("here\n")))
        })));
        assert_eq!(correct, make_parser("cat <<EOF${ 'asdf'}(\"hello'\"){\\o}\nhere\nEOF${ asdf}(hello'){o}")
                   .complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_delimeter_can_be_followed_by_carriage_return_newline() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!(word("arg")))),
            io: vec!(Redirect::Heredoc(None, word("here\n")))
        })));
        assert_eq!(correct, make_parser("cat <<EOF arg\nhere\nEOF\r\n").complete_command().unwrap());

        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!(word("arg")))),
            io: vec!(Redirect::Heredoc(None, word("here\r\n")))
        })));
        assert_eq!(correct, make_parser("cat <<EOF arg\nhere\r\nEOF\r\n").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_valid_delimiter_can_start_with() {
        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("\thello\n\t\tworld\n")))
        })));
        assert_eq!(correct, make_parser("cat << -EOF\n\thello\n\t\tworld\n-EOF").complete_command().unwrap());

        let correct = Some(Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("cat"), vec!())),
            io: vec!(Redirect::Heredoc(None, word("hello\nworld\n")))
        })));
        assert_eq!(correct, make_parser("cat <<--EOF\n\thello\n\t\tworld\n-EOF").complete_command().unwrap());
    }

    #[test]
    fn test_heredoc_invalid_missing_delimeter() {
        assert_eq!(Err(Unexpected(Token::Semi, src(7, 1, 8))), make_parser("cat << ;").complete_command());
    }

    #[test]
    fn test_heredoc_invalid_unbalanced_quoting() {
        assert_eq!(Err(Unmatched(Token::SingleQuote, src(6,  1,  7))), make_parser("cat <<'eof" ).complete_command());
        assert_eq!(Err(Unmatched(Token::Backtick,    src(6,  1,  7))), make_parser("cat <<`eof" ).complete_command());
        assert_eq!(Err(Unmatched(Token::DoubleQuote, src(6,  1,  7))), make_parser("cat <<\"eof").complete_command());
        assert_eq!(Err(Unmatched(Token::ParenOpen,   src(9,  1, 10))), make_parser("cat <<eof(" ).complete_command());
        assert_eq!(Err(Unmatched(Token::ParenOpen,   src(10, 1, 11))), make_parser("cat <<eof$(").complete_command());
        assert_eq!(Err(Unmatched(Token::CurlyOpen,   src(10, 1, 11))), make_parser("cat <<eof${").complete_command());
    }

    #[test]
    fn test_heredoc_invalid_shows_right_position_of_error() {
        let mut p = make_parser("cat <<EOF\nhello\n${invalid subst\nEOF");
        assert_eq!(
            Err(BadSubst(Token::Whitespace(String::from(" ")), src(25,3,10))),
            p.complete_command()
        );
    }

    #[test]
    fn test_heredoc_invalid_shows_right_position_of_error_when_tabs_stripped() {
        let mut p = make_parser("cat <<-EOF\n\t\thello\n\t\t${invalid subst\n\t\t\tEOF");
        assert_eq!(
            Err(BadSubst(Token::Whitespace(String::from(" ")), src(30,3,12))),
            p.complete_command()
        );
    }

    #[test]
    fn test_heredoc_keeps_track_of_correct_position_after_redirect() {
        let mut p = make_parser("cat <<EOF arg ()\nhello\nEOF");
        // Grab the heredoc command
        p.complete_command().unwrap();
        // Fail on the ()
        assert_eq!(Err(Unexpected(Token::ParenClose, src(15,1,16))), p.complete_command());
    }

    #[test]
    fn test_redirect_list_valid() {
        let mut p = make_parser("1>>out <& 2 2>&-");
        let io = p.redirect_list().unwrap();
        assert_eq!(io, vec!(
            Redirect::Append(Some(1), word("out")),
            Redirect::DupRead(None, word("2")),
            Redirect::DupWrite(Some(2), word("-")),
        ));
    }

    #[test]
    fn test_redirect_list_rejects_non_fd_words() {
        assert_eq!(Err(BadFd(src(16, 1, 17), src(19, 1, 20))), make_parser("1>>out <in 2>&- abc").redirect_list());
        assert_eq!(Err(BadFd(src(7,  1, 8),  src(10,  1, 11))), make_parser("1>>out abc<in 2>&-").redirect_list());
        assert_eq!(Err(BadFd(src(7,  1, 8),  src(10,  1, 11))), make_parser("1>>out abc <in 2>&-").redirect_list());
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
        assert_eq!(Err(IncompleteCmd("do", src(0,1,1), "done", src(20,2,14))), p.do_group());
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
        assert_eq!(Err(Unexpected(Token::Name(String::from("foo")), src(0,1,1))), p.do_group());
        let mut p = make_parser("do foo\nbar; baz");
        assert_eq!(Err(IncompleteCmd("do", src(0,1,1), "done", src(15,2,9))), p.do_group());
    }

    #[test]
    fn test_do_group_invalid_quoted() {
        let cmds = [
            ("'do' foo\nbar; baz; done",   Unexpected(Token::SingleQuote, src(0, 1, 1))),
            ("do foo\nbar; baz; 'done'",   IncompleteCmd("do", src(0,1,1), "done", src(23,2,17))),
            ("\"do\" foo\nbar; baz; done", Unexpected(Token::DoubleQuote, src(0, 1, 1))),
            ("do foo\nbar; baz; \"done\"", IncompleteCmd("do", src(0,1,1), "done", src(23,2,17))),
        ];

        for &(c, ref e) in cmds.into_iter() {
            match make_parser(c).do_group() {
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
                Err(ref err) => if err != e {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           c, e, err);
                },
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
        assert_eq!(Err(Unexpected(Token::Literal(String::from("d")), src(0,1,1))), p.do_group());
        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("do")),
            Token::Newline,
            Token::Literal(String::from("foo")),
            Token::Newline,
            Token::Literal(String::from("do")),
            Token::Literal(String::from("ne")),
        ));
        assert_eq!(Err(IncompleteCmd("do", src(0,1,1), "done", src(11,3,5))), p.do_group());
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
        assert_eq!(Err(IncompleteCmd("do", src(0,1,1), "done", src(7,2,5))), p.do_group());
    }

    #[test]
    fn test_brace_group_valid() {
        let mut p = make_parser("{ foo\nbar; baz; }");
        let correct = vec!(cmd_unboxed("foo"), cmd_unboxed("bar"), cmd_unboxed("baz"));
        assert_eq!(correct, p.brace_group().unwrap());
    }

    #[test]
    fn test_brace_group_invalid_missing_separator() {
        assert_eq!(Err(Unmatched(Token::CurlyOpen, src(0,1,1))), make_parser("{ foo\nbar; baz }").brace_group());
    }

    #[test]
    fn test_brace_group_invalid_start_must_be_whitespace_delimited() {
        let mut p = make_parser("{foo\nbar; baz; }");
        assert_eq!(Err(Unexpected(Token::Name(String::from("foo")), src(1,1,2))), p.brace_group());
    }

    #[test]
    fn test_brace_group_valid_end_must_be_whitespace_and_separator_delimited() {
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
        assert_eq!(Err(Unmatched(Token::CurlyOpen, src(0,1,1))), p.brace_group());
        let mut p = make_parser("foo\nbar; baz; }");
        assert_eq!(Err(Unexpected(Token::Name(String::from("foo")), src(0,1,1))), p.brace_group());
    }

    #[test]
    fn test_brace_group_invalid_quoted() {
        let cmds = [
            ("'{' foo\nbar; baz; }",   Unexpected(Token::SingleQuote, src(0,1,1))),
            ("{ foo\nbar; baz; '}'",   Unmatched(Token::CurlyOpen, src(0,1,1))),
            ("\"{\" foo\nbar; baz; }", Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("{ foo\nbar; baz; \"}\"", Unmatched(Token::CurlyOpen, src(0,1,1))),
        ];

        for &(c, ref e) in cmds.into_iter() {
            match make_parser(c).brace_group() {
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
                Err(ref err) => if err != e {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           c, e, err);
                }
            }
        }
    }

    #[test]
    fn test_brace_group_invalid_missing_body() {
        assert_eq!(Err(Unmatched(Token::CurlyOpen, src(0, 1, 1))), make_parser("{\n}").brace_group());
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
        assert_eq!(Err(Unmatched(Token::ParenOpen, src(0,1,1))), make_parser("( foo\nbar; baz").subshell());
        assert_eq!(Err(Unexpected(Token::Name(String::from("foo")), src(0,1,1))),
            make_parser("foo\nbar; baz; )").subshell());
    }

    #[test]
    fn test_subshell_invalid_quoted() {
        let cmds = [
            ("'(' foo\nbar; baz; )",   Unexpected(Token::SingleQuote, src(0,1,1))),
            ("( foo\nbar; baz; ')'",   Unmatched(Token::ParenOpen, src(0,1,1))),
            ("\"(\" foo\nbar; baz; )", Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("( foo\nbar; baz; \")\"", Unmatched(Token::ParenOpen, src(0,1,1))),
        ];

        for &(c, ref e) in cmds.into_iter() {
            match make_parser(c).subshell() {
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
                Err(ref err) => if err != e {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           c, e, err);
                },
            }
        }
    }

    #[test]
    fn test_subshell_invalid_missing_body() {
        assert_eq!(Err(Unexpected(Token::ParenClose, src(2,2,1))), make_parser("(\n)").subshell());
        assert_eq!(Err(Unexpected(Token::ParenClose, src(1,1,2))), make_parser("()").subshell());
    }

    #[test]
    fn test_loop_command_while_valid() {
        let mut p = make_parser("while guard1; guard2; do foo\nbar; baz; done");
        let (until, GuardBodyPair { guard, body }) = p.loop_command().unwrap();

        let correct_guard = vec!(cmd_unboxed("guard1"), cmd_unboxed("guard2"));
        let correct_body = vec!(cmd_unboxed("foo"), cmd_unboxed("bar"), cmd_unboxed("baz"));

        assert_eq!(until, builder::LoopKind::While);
        assert_eq!(correct_guard, guard);
        assert_eq!(correct_body, body);
    }

    #[test]
    fn test_loop_command_until_valid() {
        let mut p = make_parser("until guard1\n guard2\n do foo\nbar; baz; done");
        let (until, GuardBodyPair { guard, body }) = p.loop_command().unwrap();

        let correct_guard = vec!(cmd_unboxed("guard1"), cmd_unboxed("guard2"));
        let correct_body = vec!(cmd_unboxed("foo"), cmd_unboxed("bar"), cmd_unboxed("baz"));

        assert_eq!(until, builder::LoopKind::Until);
        assert_eq!(correct_guard, guard);
        assert_eq!(correct_body, body);
    }

    #[test]
    fn test_loop_command_invalid_missing_separator() {
        let mut p = make_parser("while guard do foo\nbar; baz; done");
        assert_eq!(Err(IncompleteCmd("while", src(0,1,1), "do", src(33,2,15))), p.loop_command());
        let mut p = make_parser("while guard; do foo\nbar; baz done");
        assert_eq!(Err(IncompleteCmd("do", src(13,1,14), "done", src(33,2,14))), p.loop_command());
    }

    #[test]
    fn test_loop_command_invalid_missing_keyword() {
        let mut p = make_parser("guard; do foo\nbar; baz; done");
        assert_eq!(Err(Unexpected(Token::Name(String::from("guard")), src(0,1,1))), p.loop_command());
    }

    #[test]
    fn test_loop_command_invalid_missing_guard() {
        // With command separator between loop and do keywords
        let mut p = make_parser("while; do foo\nbar; baz; done");
        assert_eq!(Err(Unexpected(Token::Semi, src(5, 1, 6))), p.loop_command());
        let mut p = make_parser("until; do foo\nbar; baz; done");
        assert_eq!(Err(Unexpected(Token::Semi, src(5, 1, 6))), p.loop_command());

        // Without command separator between loop and do keywords
        let mut p = make_parser("while do foo\nbar; baz; done");
        assert_eq!(Err(Unexpected(Token::Name(String::from("do")), src(6, 1, 7))), p.loop_command());
        let mut p = make_parser("until do foo\nbar; baz; done");
        assert_eq!(Err(Unexpected(Token::Name(String::from("do")), src(6, 1, 7))), p.loop_command());
    }

    #[test]
    fn test_loop_command_invalid_quoted() {
        let cmds = [
            ("'while' guard do foo\nbar; baz; done",   Unexpected(Token::SingleQuote, src(0,1,1))),
            ("'until' guard do foo\nbar; baz; done",   Unexpected(Token::SingleQuote, src(0,1,1))),
            ("\"while\" guard do foo\nbar; baz; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("\"until\" guard do foo\nbar; baz; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ];

        for &(c, ref e) in cmds.into_iter() {
            match make_parser(c).loop_command() {
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
                Err(ref err) => if err != e {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           c, e, err);
                },
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
        assert_eq!(Err(Unexpected(Token::Literal(String::from("whi")), src(0,1,1))), p.loop_command());
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
        assert_eq!(Err(Unexpected(Token::Literal(String::from("un")), src(0,1,1))), p.loop_command());
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
        let guard1 = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("guard1"), vec!())),
            io: vec!(Redirect::Read(None, word("in"))),
        }));

        let guard2 = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("guard2"), vec!())),
            io: vec!(Redirect::Write(None, word("out"))),
        }));

        let guard3 = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("guard3"), vec!())),
            io: vec!(),
        }));

        let body1 = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("body1"), vec!())),
            io: vec!(Redirect::Clobber(None, word("clob"))),
        }));

        let body2 = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("body2"), vec!())),
            io: vec!(Redirect::Append(Some(2), word("app"))),
        }));

        let els = cmd_unboxed("else");

        let correct = builder::IfFragments {
            conditionals: vec!(
                GuardBodyPair { guard: vec!(guard1, guard2), body: vec!(body1) },
                GuardBodyPair { guard: vec!(guard3), body: vec!(body2) },
            ),
            else_part: Some(vec!(els)),
        };
        let mut p = make_parser("if guard1 <in; >out guard2; then body1 >|clob\n elif guard3; then body2 2>>app; else else; fi");
        assert_eq!(correct, p.if_command().unwrap());
    }

    #[test]
    fn test_if_command_valid_without_else() {
        let guard1 = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("guard1"), vec!())),
            io: vec!(Redirect::Read(None, word("in"))),
        }));

        let guard2 = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("guard2"), vec!())),
            io: vec!(Redirect::Write(None, word("out"))),
        }));

        let guard3 = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("guard3"), vec!())),
            io: vec!(),
        }));

        let body1 = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("body1"), vec!())),
            io: vec!(Redirect::Clobber(None, word("clob"))),
        }));

        let body2 = Simple(Box::new(SimpleCommand {
            vars: vec!(),
            cmd: Some((word("body2"), vec!())),
            io: vec!(Redirect::Append(Some(2), word("app"))),
        }));

        let correct = builder::IfFragments {
            conditionals: vec!(
                GuardBodyPair { guard: vec!(guard1, guard2), body: vec!(body1) },
                GuardBodyPair { guard: vec!(guard3), body: vec!(body2) },
            ),
            else_part: None,
        };
        let mut p = make_parser("if guard1 <in; >out guard2; then body1 >|clob\n elif guard3; then body2 2>>app; fi");
        assert_eq!(correct, p.if_command().unwrap());
    }

    #[test]
    fn test_if_command_invalid_missing_separator() {
        let mut p = make_parser("if guard; then body1; elif guard2; then body2; else else fi");
        assert_eq!(Err(IncompleteCmd("if", src(0,1,1), "fi", src(59,1,60))), p.if_command());
    }

    #[test]
    fn test_if_command_invalid_missing_keyword() {
        let mut p = make_parser("guard1; then body1; elif guard2; then body2; else else; fi");
        assert_eq!(Err(Unexpected(Token::Name(String::from("guard1")), src(0,1,1))), p.if_command());
        let mut p = make_parser("if guard1; then body1; elif guard2; then body2; else else;");
        assert_eq!(Err(IncompleteCmd("if", src(0,1,1), "fi", src(58,1,59))), p.if_command());
    }

    #[test]
    fn test_if_command_invalid_missing_guard() {
        let mut p = make_parser("if; then body1; elif guard2; then body2; else else; fi");
        assert_eq!(Err(Unexpected(Token::Semi, src(2,1,3))), p.if_command());
    }

    #[test]
    fn test_if_command_invalid_missing_body() {
        let mut p = make_parser("if guard; then; elif guard2; then body2; else else; fi");
        assert_eq!(Err(Unexpected(Token::Semi, src(14, 1, 15))), p.if_command());
        let mut p = make_parser("if guard1; then body1; elif; then body2; else else; fi");
        assert_eq!(Err(Unexpected(Token::Semi, src(27, 1, 28))), p.if_command());
        let mut p = make_parser("if guard1; then body1; elif guard2; then body2; else; fi");
        assert_eq!(Err(Unexpected(Token::Semi, src(52, 1, 53))), p.if_command());
    }

    #[test]
    fn test_if_command_invalid_quoted() {
        let cmds = [
            ("'if' guard1; then body1; elif guard2; then body2; else else; fi", Unexpected(Token::SingleQuote, src(0,1,1))),
            ("if guard1; then body1; elif guard2; then body2; else else; 'fi'", IncompleteCmd("if", src(0,1,1), "fi", src(63,1,64))),
            ("\"if\" guard1; then body1; elif guard2; then body2; else else; fi", Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("if guard1; then body1; elif guard2; then body2; else else; \"fi\"", IncompleteCmd("if", src(0,1,1), "fi", src(63,1,64))),
        ];

        for &(s, ref e) in cmds.into_iter() {
            match make_parser(s).if_command() {
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", s, result),
                Err(ref err) => if err != e {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           s, e, err);
                },
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
        assert_eq!(Err(Unexpected(Token::Literal(String::from("i")), src(0,1,1))), p.if_command());

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
        assert_eq!(Err(IncompleteCmd("if", src(0,1,1), "fi", src(61,11,3))), p.if_command());
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
        assert_eq!(p.word().unwrap().unwrap(), word("echo"));
        assert_eq!(p.word().unwrap().unwrap(), word("{}"));
        assert_eq!(p.word().unwrap().unwrap(), word("}"));
        assert_eq!(p.word().unwrap().unwrap(), word("{"));

        let correct = Some(cmd_args_unboxed("echo", &["{}", "}", "{"]));
        assert_eq!(correct, make_parser(source).complete_command().unwrap());
    }

    #[test]
    fn test_for_command_valid_with_words() {
        let mut p = make_parser("for var #comment1\nin one two three\n#comment2\n\ndo echo $var; done");
        let fragments = p.for_command().unwrap();
        assert_eq!(fragments.var, "var");
        assert_eq!(fragments.post_var_comments, vec!(Newline(Some(String::from("#comment1")))));
        assert_eq!(fragments.words.unwrap(), vec!(
            word("one"),
            word("two"),
            word("three"),
        ));
        assert_eq!(fragments.post_words_comments, Some(vec!(
            Newline(None),
            Newline(Some(String::from("#comment2"))),
            Newline(None),
        )));

        let correct_body = vec!(Simple(Box::new(SimpleCommand {
            vars: vec!(), io: vec!(),
            cmd: Some((word("echo"), vec!(word_param(Parameter::Var(String::from("var"))))))
        })));

        assert_eq!(correct_body, fragments.body);
    }

    #[test]
    fn test_for_command_valid_without_words() {
        let mut p = make_parser("for var #comment\ndo echo $var; done");
        let fragments = p.for_command().unwrap();
        assert_eq!(fragments.var, "var");
        assert_eq!(fragments.post_var_comments, vec!(Newline(Some(String::from("#comment")))));
        assert_eq!(fragments.words, None);
        assert_eq!(fragments.post_words_comments, None);

        let correct_body = vec!(Simple(Box::new(SimpleCommand {
            vars: vec!(), io: vec!(),
            cmd: Some((word("echo"), vec!(word_param(Parameter::Var(String::from("var"))))))
        })));

        assert_eq!(correct_body, fragments.body);
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
        assert_eq!(Err(IncompleteCmd("for", src(0,1,1), "do", src(25,1,26))), p.for_command());
    }

    #[test]
    fn test_for_command_invalid_missing_separator() {
        let mut p = make_parser("for var in one two three do echo $var; done");
        assert_eq!(Err(IncompleteCmd("for", src(0,1,1), "do", src(39,1,40))), p.for_command());
    }

    #[test]
    fn test_for_command_invalid_amp_not_valid_separator() {
        let mut p = make_parser("for var in one two three& do echo $var; done");
        assert_eq!(Err(Unexpected(Token::Amp, src(24, 1, 25))), p.for_command());
    }

    #[test]
    fn test_for_command_invalid_missing_keyword() {
        let mut p = make_parser("var in one two three\ndo echo $var; done");
        assert_eq!(Err(Unexpected(Token::Name(String::from("var")), src(0,1,1))), p.for_command());
    }

    #[test]
    fn test_for_command_invalid_missing_var() {
        let mut p = make_parser("for in one two three\ndo echo $var; done");
        assert_eq!(Err(IncompleteCmd("for", src(0,1,1), "in", src(7,1,8))), p.for_command());
    }

    #[test]
    fn test_for_command_invalid_missing_body() {
        let mut p = make_parser("for var in one two three\n");
        assert_eq!(Err(IncompleteCmd("for", src(0,1,1), "do", src(25,2,1))), p.for_command());
    }

    #[test]
    fn test_for_command_invalid_quoted() {
        let cmds = [
            ("'for' var in one two three\ndo echo $var; done", Unexpected(Token::SingleQuote, src(0,1,1))),
            ("for var 'in' one two three\ndo echo $var; done", IncompleteCmd("for", src(0,1,1), "in", src(8,1,9))),
            ("\"for\" var in one two three\ndo echo $var; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("for var \"in\" one two three\ndo echo $var; done", IncompleteCmd("for", src(0,1,1), "in", src(8,1,9))),
        ];

        for &(c, ref e) in cmds.into_iter() {
            match make_parser(c).for_command() {
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
                Err(ref err) => if err != e {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           c, e, err);
                },
            }
        }
    }

    #[test]
    fn test_for_command_invalid_var_must_be_name() {
        let mut p = make_parser("for 123var in one two three\ndo echo $var; done");
        assert_eq!(Err(BadIdent(String::from("123var"), src(4, 1, 5))), p.for_command());
        let mut p = make_parser("for 'var' in one two three\ndo echo $var; done");
        assert_eq!(Err(Unexpected(Token::SingleQuote, src(4, 1, 5))), p.for_command());
        let mut p = make_parser("for \"var\" in one two three\ndo echo $var; done");
        assert_eq!(Err(Unexpected(Token::DoubleQuote, src(4, 1, 5))), p.for_command());
        let mut p = make_parser("for var*% in one two three\ndo echo $var; done");
        assert_eq!(Err(Unexpected(Token::Star, src(7, 1, 8))), p.for_command());
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
        assert_eq!(Err(Unexpected(Token::Literal(String::from("fo")), src(0, 1, 1))), p.for_command());

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
        assert_eq!(Err(IncompleteCmd("for", src(0,1,1), "in", src(8,1,9))), p.for_command());
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
        let correct = Function(
            String::from("foo"),
            Rc::new(Compound(
                Box::new(Brace(vec!(Simple(Box::new(SimpleCommand {
                    cmd: Some((word("echo"), vec!(word("body")))),
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
        let correct = Function(
            String::from("foo"),
            Rc::new(Simple(Box::new(SimpleCommand {
                cmd: Some((word("echo"), vec!(word("body")))),
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
    fn test_function_declaration_parens_can_be_subshell_if_function_keyword_present() {
        let correct = Function(
            String::from("foo"),
            Rc::new(Compound(
                Box::new(Subshell(vec!(Simple(Box::new(SimpleCommand {
                    cmd: Some((word("echo"), vec!(word("subshell")))),
                    vars: vec!(),
                    io: vec!(),
                }))))),
                vec!()
            ))
        );

        assert_eq!(correct, make_parser("function foo (echo subshell)").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo() (echo subshell)").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo () (echo subshell)").function_declaration().unwrap());
        assert_eq!(correct, make_parser("function foo\n(echo subshell)").function_declaration().unwrap());
    }

    #[test]
    fn test_function_declaration_invalid_newline_in_declaration() {
        let mut p = make_parser("function\nname() { echo body; }");
        assert_eq!(Err(Unexpected(Token::Newline, src(8,1,9))), p.function_declaration());
        // If the function keyword is present the () are optional, and at this particular point
        // they become an empty subshell (which is invalid)
        let mut p = make_parser("function name\n() { echo body; }");
        assert_eq!(Err(Unexpected(Token::ParenClose, src(15,2,2))), p.function_declaration());
    }

    #[test]
    fn test_function_declaration_invalid_missing_space_after_fn_keyword_and_no_parens() {
        let mut p = make_parser("functionname { echo body; }");
        assert_eq!(Err(Unexpected(Token::CurlyOpen, src(13,1,14))), p.function_declaration());
    }

    #[test]
    fn test_function_declaration_invalid_missing_fn_keyword_and_parens() {
        let mut p = make_parser("name { echo body; }");
        assert_eq!(Err(Unexpected(Token::CurlyOpen, src(5,1,6))), p.function_declaration());
    }

    #[test]
    fn test_function_declaration_invalid_missing_space_after_name_no_parens() {
        let mut p = make_parser("function name{ echo body; }");
        assert_eq!(Err(Unexpected(Token::CurlyOpen, src(13,1,14))), p.function_declaration());
        let mut p = make_parser("function name( echo body; )");
        assert_eq!(Err(Unexpected(Token::Name(String::from("echo")), src(15,1,16))), p.function_declaration());
    }

    #[test]
    fn test_function_declaration_invalid_missing_name() {
        let mut p = make_parser("function { echo body; }");
        assert_eq!(Err(Unexpected(Token::CurlyOpen, src(9,1,10))), p.function_declaration());
        let mut p = make_parser("function () { echo body; }");
        assert_eq!(Err(Unexpected(Token::ParenOpen, src(9,1,10))), p.function_declaration());
        let mut p = make_parser("() { echo body; }");
        assert_eq!(Err(Unexpected(Token::ParenOpen, src(0,1,1))), p.function_declaration());
    }

    #[test]
    fn test_function_declaration_invalid_missing_body() {
        let mut p = make_parser("function name");
        assert_eq!(Err(UnexpectedEOF), p.function_declaration());
        let mut p = make_parser("function name()");
        assert_eq!(Err(UnexpectedEOF), p.function_declaration());
        let mut p = make_parser("name()");
        assert_eq!(Err(UnexpectedEOF), p.function_declaration());
    }

    #[test]
    fn test_function_declaration_invalid_quoted() {
        let cmds = [
            ("'function' name { echo body; }", Unexpected(Token::SingleQuote, src(0,1,1))),
            ("function 'name'() { echo body; }", Unexpected(Token::SingleQuote, src(9,1,10))),
            ("name'()' { echo body; }", Unexpected(Token::SingleQuote, src(4,1,5))),
            ("\"function\" name { echo body; }", Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("function \"name\"() { echo body; }", Unexpected(Token::DoubleQuote, src(9,1,10))),
            ("name\"()\" { echo body; }", Unexpected(Token::DoubleQuote, src(4,1,5))),
        ];

        for &(c, ref e) in cmds.into_iter() {
            match make_parser(c).function_declaration() {
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
                Err(ref err) => if err != e {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           c, e, err);
                },
            }
        }
    }

    #[test]
    fn test_function_declaration_invalid_fn_must_be_name() {
        let mut p = make_parser("function 123fn { echo body; }");
        assert_eq!(Err(BadIdent(String::from("123fn"), src(9, 1, 10))), p.function_declaration());
        let mut p = make_parser("function 123fn() { echo body; }");
        assert_eq!(Err(BadIdent(String::from("123fn"), src(9, 1, 10))), p.function_declaration());
        let mut p = make_parser("123fn() { echo body; }");
        assert_eq!(Err(BadIdent(String::from("123fn"), src(0, 1, 1))), p.function_declaration());
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
        assert_eq!(Err(BadIdent(String::from("fn_name"), src(9, 1, 10))), p.function_declaration());

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
        assert_eq!(Err(BadIdent(String::from("func"), src(0, 1, 1))), p.function_declaration());
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
        let correct = builder::CaseFragments {
            word: word("foo"),
            post_word_comments: vec!(),
            arms: vec!(
                (
                    builder::CasePatternFragments {
                        pre_pattern_comments: vec!(),
                        pattern_alternatives: vec!(word("hello"), word("goodbye")),
                        post_pattern_comments: vec!(),
                    },
                    vec!(cmd_args_unboxed("echo", &["greeting"])),
                ),
                (
                    builder::CasePatternFragments {
                        pre_pattern_comments: vec!(),
                        pattern_alternatives: vec!(word("world")),
                        post_pattern_comments: vec!(),
                    },
                    vec!(cmd_args_unboxed("echo", &["noun"])),
                ),
            ),
            post_arms_comments: vec!(),
        };

        let cases = vec!(
            // `(` before pattern is optional
            "case foo in  hello | goodbye) echo greeting;;  world) echo noun;; esac",
            "case foo in (hello | goodbye) echo greeting;;  world) echo noun;; esac",
            "case foo in (hello | goodbye) echo greeting;; (world) echo noun;; esac",

            // Final `;;` is optional as long as last command is complete
            "case foo in hello | goodbye) echo greeting;; world) echo noun\nesac",
            "case foo in hello | goodbye) echo greeting;; world) echo noun; esac",
        );

        for src in cases {
            assert_eq!(correct, make_parser(src).case_command().unwrap());
        }
    }

    #[test]
    fn test_case_command_valid_with_comments() {
        let correct = builder::CaseFragments {
            word: word("foo"),
            post_word_comments: vec!(
                Newline(Some(String::from("#post_word_a"))),
                Newline(None),
                Newline(Some(String::from("#post_word_b"))),
            ),
            arms: vec!(
                (
                    builder::CasePatternFragments {
                        pre_pattern_comments: vec!(
                            Newline(Some(String::from("#pre_pat_1a"))),
                            Newline(None),
                            Newline(Some(String::from("#pre_pat_1b"))),
                        ),
                        pattern_alternatives: vec!(word("hello"), word("goodbye")),
                        post_pattern_comments: vec!(
                            Newline(Some(String::from("#post_pat_1a"))),
                            Newline(None),
                            Newline(Some(String::from("#post_pat_1b"))),
                        ),
                    },
                    vec!(cmd_args_unboxed("echo", &["greeting"])),
                ),
                (
                    builder::CasePatternFragments {
                        pre_pattern_comments: vec!(
                            Newline(Some(String::from("#pre_pat_2a"))),
                            Newline(None),
                            Newline(Some(String::from("#pre_pat_2b"))),
                        ),
                        pattern_alternatives: vec!(word("world")),
                        post_pattern_comments: vec!(
                            Newline(Some(String::from("#post_pat_2a"))),
                            Newline(None),
                            Newline(Some(String::from("#post_pat_2b"))),
                        ),
                    },
                    vec!(cmd_args_unboxed("echo", &["noun"])),
                ),
            ),
            post_arms_comments: vec!(
                Newline(Some(String::from("#post_branch_a"))),
                Newline(None),
                Newline(Some(String::from("#post_branch_b"))),
            ),
        };

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
        let correct = builder::CaseFragments {
            word: word("foo"),
            post_word_comments: vec!(
                Newline(Some(String::from("#post_word_a"))),
                Newline(None),
                Newline(Some(String::from("#post_word_b"))),
            ),
            arms: vec!(),
            post_arms_comments: vec!(
                Newline(Some(String::from("#post_branch_a"))),
                Newline(None),
                Newline(Some(String::from("#post_branch_b"))),
            ),
        };

        // Various newlines and comments allowed within the command
        let cmd =
            "case foo #post_word_a

            #post_word_b
            in #post_branch_a

            #post_branch_b
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
        assert_eq!(Err(Unexpected(Token::Name(String::from("foo")), src(0, 1, 1))), p.case_command());
        let mut p = make_parser("case foo foo) echo foo;; bar) echo bar;; esac");
        assert_eq!(Err(IncompleteCmd("case", src(0,1,1), "in", src(9,1,10))), p.case_command());
        let mut p = make_parser("case foo in foo) echo foo;; bar) echo bar;;");
        assert_eq!(Err(IncompleteCmd("case", src(0,1,1), "esac", src(43,1,44))), p.case_command());
    }

    #[test]
    fn test_case_command_invalid_missing_word() {
        let mut p = make_parser("case in foo) echo foo;; bar) echo bar;; esac");
        assert_eq!(Err(IncompleteCmd("case", src(0,1,1), "in", src(8,1,9))), p.case_command());
    }

    #[test]
    fn test_case_command_invalid_quoted() {
        let cmds = [
            ("'case' foo in foo) echo foo;; bar) echo bar;; esac", Unexpected(Token::SingleQuote, src(0,1,1))),
            ("case foo 'in' foo) echo foo;; bar) echo bar;; esac", IncompleteCmd("case", src(0,1,1), "in", src(9,1,10))),
            ("case foo in foo) echo foo;; bar')' echo bar;; esac", Unexpected(Token::Name(String::from("echo")), src(35,1,36))),
            ("case foo in foo) echo foo;; bar) echo bar;; 'esac'", IncompleteCmd("case", src(0,1,1), "esac", src(50,1,51))),
            ("\"case\" foo in foo) echo foo;; bar) echo bar;; esac", Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("case foo \"in\" foo) echo foo;; bar) echo bar;; esac", IncompleteCmd("case", src(0,1,1), "in", src(9,1,10))),
            ("case foo in foo) echo foo;; bar\")\" echo bar;; esac", Unexpected(Token::Name(String::from("echo")), src(35,1,36))),
            ("case foo in foo) echo foo;; bar) echo bar;; \"esac\"", IncompleteCmd("case", src(0,1,1), "esac", src(50,1,51))),
        ];

        for &(c, ref e) in cmds.into_iter() {
            match make_parser(c).case_command() {
                Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
                Err(ref err) => if err != e {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           c, e, err);
                },
            }
        }
    }

    #[test]
    fn test_case_command_invalid_newline_after_case() {
        let mut p = make_parser("case\nfoo in foo) echo foo;; bar) echo bar;; esac");
        assert_eq!(Err(Unexpected(Token::Newline, src(4, 1, 5))), p.case_command());
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
        assert_eq!(Err(Unexpected(Token::Literal(String::from("ca")), src(0,1,1))), p.case_command());

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
        assert_eq!(Err(IncompleteCmd("case", src(0,1,1), "in", src(12,1,13))), p.case_command());

        let mut p = make_parser_from_tokens(vec!(
            Token::Literal(String::from("case")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("foo")),
            Token::Literal(String::from("bar")),
            Token::Whitespace(String::from(" ")),

            Token::Literal(String::from("in")),
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

            Token::Literal(String::from("es")), Token::Literal(String::from("ac")),
        ));
        assert_eq!(Err(IncompleteCmd("case", src(0,1,1), "esac", src(36,4,7))), p.case_command());
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

        for cmd in &commands {
            match make_parser(cmd).compound_command() {
                Ok(ref result) if result == &correct => {},
                Ok(result) => panic!("Parsed \"{}\" as an unexpected command type:\n{:#?}", cmd, result),
                Err(err) => panic!("Failed to parse \"{}\": {}", cmd, err),
            }
        }
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_while() {
        let correct = Compound(
            Box::new(While(GuardBodyPair {
                guard: vec!(cmd_unboxed("guard")),
                body: vec!(cmd_unboxed("foo")),
            })),
            vec!()
        );
        assert_eq!(correct, make_parser("while guard; do foo; done").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_until() {
        let correct = Compound(
            Box::new(Until(GuardBodyPair {
                guard: vec!(cmd_unboxed("guard")),
                body: vec!(cmd_unboxed("foo")),
            })),
            vec!()
        );
        assert_eq!(correct, make_parser("until guard; do foo; done").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_for() {
        let correct = Compound(Box::new(For(String::from("var"), Some(vec!()), vec!(cmd_unboxed("foo")))), vec!());
        assert_eq!(correct, make_parser("for var in; do foo; done").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_if() {
        let correct = Compound(
            Box::new(If(
                vec!(GuardBodyPair {
                    guard: vec!(cmd_unboxed("guard")),
                    body: vec!(cmd_unboxed("body")),
                }),
                None)
            ),
            vec!()
        );
        assert_eq!(correct, make_parser("if guard; then body; fi").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_delegates_valid_commands_case() {
        let correct = Compound(Box::new(Case(word("foo"), vec!())), vec!());
        assert_eq!(correct, make_parser("case foo in esac").compound_command().unwrap());
    }

    #[test]
    fn test_compound_command_errors_on_quoted_commands() {
        let cases = [
            // { is a reserved word, thus concatenating it essentially "quotes" it
            // `compound_command` doesn't know or care enough to specify that "foo" is
            // the problematic token instead of {, however, callers who are smart enough
            // to expect a brace command would be aware themselves that no such valid
            // command actually exists. TL;DR: it's okay for `compound_command` to blame {
            ("{foo; }",                      Unexpected(Token::CurlyOpen,   src(0,1,1))),
            ("'{' foo; }",                   Unexpected(Token::SingleQuote, src(0,1,1))),
            ("'(' foo; )",                   Unexpected(Token::SingleQuote, src(0,1,1))),
            ("'while' guard do foo; done",   Unexpected(Token::SingleQuote, src(0,1,1))),
            ("'until' guard do foo; done",   Unexpected(Token::SingleQuote, src(0,1,1))),
            ("'if' guard; then body; fi",    Unexpected(Token::SingleQuote, src(0,1,1))),
            ("'for' var in; do foo; done",   Unexpected(Token::SingleQuote, src(0,1,1))),
            ("'case' foo in esac",           Unexpected(Token::SingleQuote, src(0,1,1))),
            ("\"{\" foo; }",                 Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("\"(\" foo; )",                 Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("\"while\" guard do foo; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("\"until\" guard do foo; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("\"if\" guard; then body; fi",  Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("\"for\" var in; do foo; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
            ("\"case\" foo in esac",         Unexpected(Token::DoubleQuote, src(0,1,1))),
        ];

        for &(src, ref e) in &cases {
            match make_parser(src).compound_command() {
                Ok(result) =>
                    panic!("Parse::compound_command unexpectedly succeeded parsing \"{}\" with result:\n{:#?}",
                           src, result),
                Err(ref err) => if err != e {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           src, e, err);
                },
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

        for cmd in &cases {
            match make_parser(cmd).compound_command() {
                Ok(Compound(_, io)) => assert_eq!(io, vec!(
                    Redirect::Append(Some(1), word("out")),
                    Redirect::DupRead(None, word("2")),
                    Redirect::DupWrite(Some(2), word("-")),
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

        for cmd in &commands {
            match make_parser(cmd).command() {
                Ok(ref result) if result == &correct => {},
                Ok(result) => panic!("Parsed \"{}\" as an unexpected command type:\n{:#?}", cmd, result),
                Err(err) => panic!("Failed to parse \"{}\": {}", cmd, err),
            }
        }
    }

    #[test]
    fn test_command_delegates_valid_commands_while() {
        let correct = Compound(
            Box::new(While(GuardBodyPair {
                guard: vec!(cmd_unboxed("guard")),
                body: vec!(cmd_unboxed("foo")),
            })),
            vec!()
        );
        assert_eq!(correct, make_parser("while guard; do foo; done").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_commands_until() {
        let correct = Compound(
            Box::new(Until(GuardBodyPair {
                guard: vec!(cmd_unboxed("guard")),
                body: vec!(cmd_unboxed("foo")),
            })),
            vec!()
        );
        assert_eq!(correct, make_parser("until guard; do foo; done").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_commands_for() {
        let correct = Compound(Box::new(For(String::from("var"), Some(vec!()), vec!(cmd_unboxed("foo")))), vec!());
        assert_eq!(correct, make_parser("for var in; do foo; done").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_commands_if() {
        let correct = Compound(
            Box::new(If(
                vec!(GuardBodyPair {
                    guard: vec!(cmd_unboxed("guard")),
                    body: vec!(cmd_unboxed("body")),
                }),
                None)
            ),
            vec!()
        );
        assert_eq!(correct, make_parser("if guard; then body; fi").command().unwrap());
    }

    #[test]
    fn test_command_delegates_valid_commands_case() {
        let correct = Compound(Box::new(Case(word("foo"), vec!())), vec!());
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

        let correct = Function(String::from("foo"), Rc::new(Compound(Box::new(Brace(vec!(cmd_args_unboxed("echo", &["body"])))), vec!())));

        for cmd in &commands {
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

        for cmd in &cases {
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
        let correct = single_quoted("abc&&||\n\n#comment\nabc");
        assert_eq!(Some(correct), make_parser("'abc&&||\n\n#comment\nabc'").word().unwrap());
    }

    #[test]
    fn test_word_single_quote_valid_slash_remains_literal() {
        let correct = single_quoted("\\\n");
        assert_eq!(Some(correct), make_parser("'\\\n'").word().unwrap());
    }

    #[test]
    fn test_word_single_quote_valid_does_not_quote_single_quotes() {
        let correct = single_quoted("hello \\");
        assert_eq!(Some(correct), make_parser("'hello \\'").word().unwrap());
    }

    #[test]
    fn test_word_single_quote_invalid_missing_close_quote() {
        assert_eq!(Err(Unmatched(Token::SingleQuote, src(0, 1, 1))), make_parser("'hello").word());
    }

    #[test]
    fn test_word_double_quote_valid() {
        let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(Literal(String::from("abc&&||\n\n#comment\nabc"))))));
        assert_eq!(Some(correct), make_parser("\"abc&&||\n\n#comment\nabc\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_recognizes_parameters() {
        let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
            Literal(String::from("test asdf")),
            Param(Parameter::Var(String::from("foo"))),
            Literal(String::from(" $")),
        ))));

        assert_eq!(Some(correct), make_parser("\"test asdf$foo $\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_recognizes_backticks() {
        let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
            Literal(String::from("test asdf ")),
            Subst(Box::new(ParameterSubstitution::Command(vec!(cmd_unboxed("foo"))))),
        ))));

        assert_eq!(Some(correct), make_parser("\"test asdf `foo`\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_escapes_dollar() {
        let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
            Literal(String::from("test")),
            Escaped(String::from("$")),
            Literal(String::from("foo ")),
            Param(Parameter::At),
        ))));

        assert_eq!(Some(correct), make_parser("\"test\\$foo $@\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_escapes_backtick() {
        let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
            Literal(String::from("test")),
            Escaped(String::from("`")),
            Literal(String::from(" ")),
            Param(Parameter::Star),
        ))));

        assert_eq!(Some(correct), make_parser("\"test\\` $*\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_escapes_double_quote() {
        let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
            Literal(String::from("test")),
            Escaped(String::from("\"")),
            Literal(String::from(" ")),
            Param(Parameter::Pound),
        ))));

        assert_eq!(Some(correct), make_parser("\"test\\\" $#\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_escapes_newline() {
        let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
            Literal(String::from("test")),
            Escaped(String::from("\n")),
            Literal(String::from(" ")),
            Param(Parameter::Question),
            Literal(String::from("\n")),
        ))));

        assert_eq!(Some(correct), make_parser("\"test\\\n $?\n\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_escapes_slash() {
        let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
            Literal(String::from("test")),
            Escaped(String::from("\\")),
            Literal(String::from(" ")),
            Param(Parameter::Positional(0)),
        ))));

        assert_eq!(Some(correct), make_parser("\"test\\\\ $0\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_valid_slash_remains_literal_in_general_case() {
        let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
            Literal(String::from("t\\est ")),
            Param(Parameter::Dollar),
        ))));

        assert_eq!(Some(correct), make_parser("\"t\\est $$\"").word().unwrap());
    }

    #[test]
    fn test_word_double_quote_slash_invalid_missing_close_quote() {
        assert_eq!(Err(Unmatched(Token::DoubleQuote, src(0, 1, 1))), make_parser("\"hello").word());
        assert_eq!(Err(Unmatched(Token::DoubleQuote, src(0, 1, 1))), make_parser("\"hello\\\"").word());
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
                Ok(Some(TopLevelWord(Single(Word::Simple(w))))) => if let Param(_) = *w {} else {
                    panic!("Unexpectedly parsed \"{}\" as a non-parameter word:\n{:#?}", p, w);
                },
                Ok(Some(w)) => panic!("Unexpectedly parsed \"{}\" as a non-parameter word:\n{:#?}", p, w),
                Ok(None) => panic!("Did not parse \"{}\" as a parameter", p),
                Err(e) => panic!("Did not parse \"{}\" as a parameter: {}", p, e),
            }
        }
    }

    #[test]
    fn test_word_literal_dollar_if_not_param() {
        let correct = word("$%asdf");
        assert_eq!(correct, make_parser("$%asdf").word().unwrap().unwrap());
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
        let correct = word("abc#def");
        assert_eq!(Ok(Some(correct)), make_parser("abc#def\n").word());
    }

    #[test]
    fn test_word_tokens_which_become_literal_words() {
        let words = [
            "{",
            "}",
            "!",
            "name",
            "1notname",
        ];

        for w in words.into_iter() {
            match make_parser(w).word() {
                Ok(Some(res)) => {
                    let correct = word(*w);
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
        let correct = TopLevelWord(Concat(vec!(
            lit("foo=bar"),
            Word::DoubleQuoted(vec!(Literal(String::from("double")))),
            Word::SingleQuoted(String::from("single")),
        )));

        assert_eq!(Ok(Some(correct)), make_parser("foo=bar\"double\"'single'").word());
    }

    #[test]
    fn test_word_special_words_recognized_as_such() {
        assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(Box::new(Star)))))),        make_parser("*").word());
        assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(Box::new(Question)))))),    make_parser("?").word());
        assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(Box::new(Tilde)))))),       make_parser("~").word());
        assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(Box::new(SquareOpen)))))),  make_parser("[").word());
        assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(Box::new(SquareClose)))))), make_parser("]").word());
        assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(Box::new(Colon)))))),       make_parser(":").word());
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
                    let correct = word_escaped(l);
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
        assert_eq!(Ok(Some(word("foo"))), p.word());
        assert_eq!(Ok(Some(word("bar"))), p.word());
    }

    #[test]
    fn test_backticked_valid() {
        let correct = word_subst(ParameterSubstitution::Command(vec!(cmd_unboxed("foo"))));
        assert_eq!(correct, make_parser("`foo`").backticked_command_substitution().unwrap());
    }

    #[test]
    fn test_backticked_valid_backslashes_removed_if_before_dollar_backslash_and_backtick() {
        let correct = word_subst(ParameterSubstitution::Command(vec!(Simple(Box::new(SimpleCommand {
            vars: vec!(), io: vec!(),
            cmd: Some((word("foo"), vec!(
                TopLevelWord(Concat(vec!(
                    Word::Simple(Box::new(Param(Parameter::Dollar))),
                    escaped("`"),
                    escaped("o"),
                )))
            ))),
        })))));
        assert_eq!(correct, make_parser("`foo \\$\\$\\\\\\`\\o`").backticked_command_substitution().unwrap());
    }

    #[test]
    fn test_backticked_nested_backticks() {
        let correct = word_subst(ParameterSubstitution::Command(vec!(
            Simple(Box::new(SimpleCommand {
                vars: vec!(), io: vec!(),
                cmd: Some((word("foo"), vec!(
                    word_subst(
                        ParameterSubstitution::Command(vec!(Simple(Box::new(SimpleCommand {
                            vars: vec!(), io: vec!(),
                            cmd: Some((word("bar"), vec!(TopLevelWord(Concat(vec!(escaped("$"), escaped("$")))))))
                        }))))
                    )
                ))),
            }))
        )));
        assert_eq!(correct, make_parser(r#"`foo \`bar \\\\$\\\\$\``"#).backticked_command_substitution().unwrap());
    }

    #[test]
    fn test_backticked_nested_backticks_x2() {
        let correct = word_subst(ParameterSubstitution::Command(vec!(
            Simple(Box::new(SimpleCommand {
                vars: vec!(), io: vec!(),
                cmd: Some((word("foo"), vec!(word_subst(
                    ParameterSubstitution::Command(vec!(Simple(Box::new(SimpleCommand {
                        vars: vec!(), io: vec!(),
                        cmd: Some((word("bar"), vec!(word_subst(
                            ParameterSubstitution::Command(vec!(Simple(Box::new(SimpleCommand {
                                vars: vec!(), io: vec!(),
                                cmd: Some((word("baz"), vec!(TopLevelWord(Concat(vec!(escaped("$"), escaped("$")))))))
                            }))))
                        ))))
                    }))))
                ))))
            }))
        )));
        assert_eq!(correct, make_parser(r#"`foo \`bar \\\`baz \\\\\\\\$\\\\\\\\$ \\\`\``"#).backticked_command_substitution().unwrap());
    }

    #[test]
    fn test_backticked_nested_backticks_x3() {
        let correct = word_subst(ParameterSubstitution::Command(vec!(
            Simple(Box::new(SimpleCommand {
                vars: vec!(), io: vec!(),
                cmd: Some((word("foo"), vec!(word_subst(
                    ParameterSubstitution::Command(vec!(Simple(Box::new(SimpleCommand {
                        vars: vec!(), io: vec!(),
                        cmd: Some((word("bar"), vec!(word_subst(
                            ParameterSubstitution::Command(vec!(Simple(Box::new(SimpleCommand {
                                vars: vec!(), io: vec!(),
                                cmd: Some((word("baz"), vec!(word_subst(
                                    ParameterSubstitution::Command(vec!(Simple(Box::new(SimpleCommand {
                                        vars: vec!(), io: vec!(),
                                        cmd: Some((word("qux"), vec!(TopLevelWord(Concat(vec!(escaped("$"), escaped("$")))))))
                                    }))))
                                )))),
                            }))))
                        ))))
                    }))))
                ))))
            }))
        )));
        assert_eq!(correct, make_parser(
            r#"`foo \`bar \\\`baz \\\\\\\`qux \\\\\\\\\\\\\\\\$\\\\\\\\\\\\\\\\$ \\\\\\\` \\\`\``"#
        ).backticked_command_substitution().unwrap());
    }

    #[test]
    fn test_backticked_invalid_missing_closing_backtick() {
        let src = [
            // Missing outermost backtick
            (r#"`foo"#, src(0,1,1)),
            (r#"`foo \`bar \\\\$\\\\$\`"#, src(0,1,1)),
            (r#"`foo \`bar \\\`baz \\\\\\\\$\\\\\\\\$ \\\`\`"#, src(0,1,1)),
            (r#"`foo \`bar \\\`baz \\\\\\\`qux \\\\\\\\\\\\\\\\$ \\\\\\\\\\\\\\\\$ \\\\\\\` \\\`\`"#, src(0,1,1)),

            // Missing second to last backtick
            (r#"`foo \`bar \\\\$\\\\$`"#, src(6,1,7)),
            (r#"`foo \`bar \\\`baz \\\\\\\\$\\\\\\\\$ \\\``"#, src(6,1,7)),
            (r#"`foo \`bar \\\`baz \\\\\\\`qux \\\\\\\\\\\\\\\\$ \\\\\\\\\\\\\\\\$ \\\\\\\` \\\``"#, src(6,1,7)),

            // Missing third to last backtick
            (r#"`foo \`bar \\\`baz \\\\\\\\$\\\\\\\\$ \``"#, src(14,1,15)),
            (r#"`foo \`bar \\\`baz \\\\\\\`qux \\\\\\\\\\\\\\\\$ \\\\\\\\\\\\\\\\$ \\\\\\\` \``"#, src(14,1,15)),

            // Missing fourth to last backtick
            (r#"`foo \`bar \\\`baz \\\\\\\`qux \\\\\\\\\\\\\\\\$ \\\\\\\\\\\\\\\\$ \\\`\``"#, src(26,1,27)),
        ];

        for &(s, p) in &src {
            let correct = Unmatched(Token::Backtick, p);
            match make_parser(s).backticked_command_substitution() {
                Ok(w) => panic!("Unexpectedly parsed the source \"{}\" as\n{:?}", s, w),
                Err(ref err) => if err != &correct {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           s, correct, err);
                },
            }
        }
    }

    #[test]
    fn test_backticked_invalid_maintains_accurate_source_positions() {
        let src = [
            (r#"`foo ${invalid param}`"#, src(14,1,15)),
            (r#"`foo \`bar ${invalid param}\``"#, src(20,1,21)),
            (r#"`foo \`bar \\\`baz ${invalid param} \\\`\``"#, src(28,1,29)),
            (r#"`foo \`bar \\\`baz \\\\\\\`qux ${invalid param} \\\\\\\` \\\`\``"#, src(40,1,41)),
        ];

        for &(s, p) in &src {
            let correct = BadSubst(Token::Whitespace(String::from(" ")), p);
            match make_parser(s).backticked_command_substitution() {
                Ok(w) => panic!("Unexpectedly parsed the source \"{}\" as\n{:?}", s, w),
                Err(ref err) => if err != &correct {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           s, correct, err);
                },
            }
        }
    }

    #[test]
    fn test_backticked_invalid_missing_opening_backtick() {
        let mut p = make_parser("foo`");
        assert_eq!(
            Err(Unexpected(Token::Name(String::from("foo")), src(0,1,1))),
            p.backticked_command_substitution()
        );
    }

    #[test]
    fn test_arithmetic_substitution_valid() {
        use syntax::ast::Arithmetic::*;

        fn x() -> Box<Arithmetic> { Box::new(Var(String::from("x"))) }
        fn y() -> Box<Arithmetic> { Box::new(Var(String::from("y"))) }
        fn z() -> Box<Arithmetic> { Box::new(Var(String::from("z"))) }

        let cases = vec!(
            ("$(( x ))", *x()),
            ("$(( 5 ))",   Literal(5)),
            ("$(( 0 ))",   Literal(0)),
            ("$(( 010 ))", Literal(8)),
            ("$(( 0xa ))", Literal(10)),
            ("$(( 0Xa ))", Literal(10)),
            ("$(( 0xA ))", Literal(10)),
            ("$(( 0XA ))", Literal(10)),
            ("$(( x++ ))", PostIncr(String::from("x"))),
            ("$(( x-- ))", PostDecr(String::from("x"))),
            ("$(( ++x ))", PreIncr(String::from("x"))),
            ("$(( --x ))", PreDecr(String::from("x"))),
            ("$(( +x ))", UnaryPlus(x())),
            ("$(( -x ))", UnaryMinus(x())),
            ("$(( !x ))", LogicalNot(x())),
            ("$(( ~x ))", BitwiseNot(x())),
            ("$(( x ** y))", Pow(x(), y())),
            ("$(( x * y ))", Mult(x(), y())),
            ("$(( x / y ))", Div(x(), y())),
            ("$(( x % y ))", Modulo(x(), y())),
            ("$(( x + y ))", Add(x(), y())),
            ("$(( x - y ))", Sub(x(), y())),
            ("$(( x << y ))", ShiftLeft(x(), y())),
            ("$(( x >> y ))", ShiftRight(x(), y())),
            ("$(( x < y ))", Less(x(), y())),
            ("$(( x <= y ))", LessEq(x(), y())),
            ("$(( x > y ))", Great(x(), y())),
            ("$(( x >= y ))", GreatEq(x(), y())),
            ("$(( x == y ))", Eq(x(), y())),
            ("$(( x != y ))", NotEq(x(), y())),
            ("$(( x & y ))", BitwiseAnd(x(), y())),
            ("$(( x ^ y ))", BitwiseXor(x(), y())),
            ("$(( x | y ))", BitwiseOr(x(), y())),
            ("$(( x && y ))", LogicalAnd(x(), y())),
            ("$(( x || y ))", LogicalOr(x(), y())),
            ("$(( x ? y : z ))", Ternary(x(), y(), z())),
            ("$(( x = y ))",   Assign(String::from("x"), y())),
            ("$(( x *= y ))",  Assign(String::from("x"), Box::new(Mult(x(), y())))),
            ("$(( x /= y ))",  Assign(String::from("x"), Box::new(Div(x(), y())))),
            ("$(( x %= y ))",  Assign(String::from("x"), Box::new(Modulo(x(), y())))),
            ("$(( x += y ))",  Assign(String::from("x"), Box::new(Add(x(), y())))),
            ("$(( x -= y ))",  Assign(String::from("x"), Box::new(Sub(x(), y())))),
            ("$(( x <<= y ))", Assign(String::from("x"), Box::new(ShiftLeft(x(), y())))),
            ("$(( x >>= y ))", Assign(String::from("x"), Box::new(ShiftRight(x(), y())))),
            ("$(( x &= y ))",  Assign(String::from("x"), Box::new(BitwiseAnd(x(), y())))),
            ("$(( x ^= y ))",  Assign(String::from("x"), Box::new(BitwiseXor(x(), y())))),
            ("$(( x |= y ))",  Assign(String::from("x"), Box::new(BitwiseOr(x(), y())))),
            ("$(( x = 5, x + y ))", Sequence(vec!(
                    Assign(String::from("x"), Box::new(Literal(5))),
                    Add(x(), y())
            ))),
            ("$(( x + (y - z) ))", Add(x(), Box::new(Sub(y(), z())))),
        );

        for (s, a) in cases.into_iter() {
            let correct = word_subst(ParameterSubstitution::Arith(Some(a)));
            match make_parser(s).parameter() {
                Ok(w) => if w != correct {
                    panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", s, w, correct)
                },
                Err(err) => panic!("Failed to parse the source \"{}\": {}", s, err),
            }
        }

        let correct = word_subst(ParameterSubstitution::Arith(None));
        assert_eq!(correct, make_parser("$(( ))").parameter().unwrap());
    }

    #[test]
    fn test_arithmetic_substitution_left_to_right_associativity() {
        use syntax::ast::Arithmetic::*;

        fn x() -> Box<Arithmetic> { Box::new(Var(String::from("x"))) }
        fn y() -> Box<Arithmetic> { Box::new(Var(String::from("y"))) }
        fn z() -> Box<Arithmetic> { Box::new(Var(String::from("z"))) }

        macro_rules! check {
            ($constructor:path, $op:tt) => {{
                let correct = word_subst(ParameterSubstitution::Arith(Some(
                    $constructor(Box::new($constructor(x(), y())), z())
                )));

                let src = format!("$((x {0} y {0} z))", stringify!($op));
                match make_parser(&src).parameter() {
                    Ok(w) => if w != correct {
                        panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", src, w, correct)
                    },
                    Err(err) => panic!("Failed to parse the source \"{}\": {}", src, err),
                }
            }};

            (assig: $constructor:path, $op:tt) => {{
                let correct = word_subst(ParameterSubstitution::Arith(Some(
                    Assign(String::from("x"), Box::new(
                        $constructor(x(), Box::new(Assign(String::from("y"), Box::new($constructor(y(), z())))))
                    ))
                )));

                let src = format!("$((x {0}= y {0}= z))", stringify!($op));
                match make_parser(&src).parameter() {
                    Ok(w) => if w != correct {
                        panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", src, w, correct)
                    },
                    Err(err) => panic!("Failed to parse the source \"{}\": {}", src, err),
                }
            }};
        }

        check!(Mult,       * );
        check!(Div,        / );
        check!(Modulo,     % );
        check!(Add,        + );
        check!(Sub,        - );
        check!(ShiftLeft,  <<);
        check!(ShiftRight, >>);
        check!(Less,       < );
        check!(LessEq,     <=);
        check!(Great ,     > );
        check!(GreatEq,    >=);
        check!(Eq,         ==);
        check!(NotEq,      !=);
        check!(BitwiseAnd, & );
        check!(BitwiseXor, ^ );
        check!(BitwiseOr,  | );
        check!(LogicalAnd, &&);
        check!(LogicalOr,  ||);

        check!(assig: Mult,       * );
        check!(assig: Div,        / );
        check!(assig: Modulo,     % );
        check!(assig: Add,        + );
        check!(assig: Sub,        - );
        check!(assig: ShiftLeft,  <<);
        check!(assig: ShiftRight, >>);
        check!(assig: BitwiseAnd, & );
        check!(assig: BitwiseXor, ^ );
        check!(assig: BitwiseOr,  | );

        let correct = word_subst(ParameterSubstitution::Arith(Some(
            Assign(String::from("x"), Box::new(Assign(String::from("y"), z())))
        )));
        assert_eq!(correct, make_parser("$(( x = y = z ))").parameter().unwrap());
    }

    #[test]
    fn test_arithmetic_substitution_right_to_left_associativity() {
        use syntax::ast::Arithmetic::*;

        fn x() -> Box<Arithmetic> { Box::new(Var(String::from("x"))) }
        fn y() -> Box<Arithmetic> { Box::new(Var(String::from("y"))) }
        fn z() -> Box<Arithmetic> { Box::new(Var(String::from("z"))) }
        fn w() -> Box<Arithmetic> { Box::new(Var(String::from("w"))) }
        fn v() -> Box<Arithmetic> { Box::new(Var(String::from("v"))) }

        let cases = vec!(
            ("$(( x ** y ** z ))", Pow(x(), Box::new(Pow(y(), z())))),
            ("$(( x ? y ? z : w : v ))", Ternary(x(), Box::new(Ternary(y(), z(), w())), v())),
        );

        for (s, a) in cases.into_iter() {
            let correct = word_subst(ParameterSubstitution::Arith(Some(a)));
            match make_parser(s).parameter() {
                Ok(w) => if w != correct {
                    panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", s, w, correct)
                },
                Err(err) => panic!("Failed to parse the source \"{}\": {}", s, err),
            }
        }
    }

    #[test]
    fn test_arithmetic_substitution_invalid() {
        let cases = vec!(
            // Pre/post increment/decrement must be applied on a variable
            // Otherwise becomes `expr+(+expr)` or `expr-(-expr)`
            ("$(( 5++ ))", Unexpected(Token::ParenClose, src(8,1,9))),
            ("$(( 5-- ))", Unexpected(Token::ParenClose, src(8,1,9))),
            ("$(( (x + y)++ ))", Unexpected(Token::ParenClose, src(14,1,15))),
            ("$(( (x + y)-- ))", Unexpected(Token::ParenClose, src(14,1,15))),

            // Pre/post increment/decrement must be applied on a variable
            ("$(( ++5 ))", Unexpected(Token::Literal(String::from("5")), src(6,1,7))),
            ("$(( --5 ))", Unexpected(Token::Literal(String::from("5")), src(6,1,7))),
            ("$(( ++(x + y) ))", Unexpected(Token::ParenOpen, src(6,1,7))),
            ("$(( --(x + y) ))", Unexpected(Token::ParenOpen, src(6,1,7))),

            // Incomplete commands
            ("$(( + ))", Unexpected(Token::ParenClose, src(6,1,7))),
            ("$(( - ))", Unexpected(Token::ParenClose, src(6,1,7))),
            ("$(( ! ))", Unexpected(Token::ParenClose, src(6,1,7))),
            ("$(( ~ ))", Unexpected(Token::ParenClose, src(6,1,7))),
            ("$(( x ** ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x *  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x /  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x %  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x +  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x -  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x << ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x >> ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x <  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x <= ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x >  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x >= ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x == ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x != ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x &  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x ^  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x |  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x && ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x || ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x =  ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x *= ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x /= ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x %= ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x += ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x -= ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x <<=))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x >>=))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x &= ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x ^= ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x |= ))", Unexpected(Token::ParenClose, src(9,1,10))),
            ("$(( x ? y : ))", Unexpected(Token::ParenClose, src(12,1,13))),
            ("$(( x ?     ))", Unexpected(Token::ParenClose, src(12,1,13))),
            ("$(( x = 5, ))", Unexpected(Token::ParenClose, src(11,1,12))),
            ("$(( x + () ))", Unexpected(Token::ParenClose, src(9,1,10))),

            // Missing first operand
            ("$(( ** y  ))", Unexpected(Token::Star, src(4,1,5))),
            ("$(( * y   ))", Unexpected(Token::Star, src(4,1,5))),
            ("$(( / y   ))", Unexpected(Token::Slash, src(4,1,5))),
            ("$(( % y   ))", Unexpected(Token::Percent, src(4,1,5))),
            ("$(( << y  ))", Unexpected(Token::DLess, src(4,1,5))),
            ("$(( >> y  ))", Unexpected(Token::DGreat, src(4,1,5))),
            ("$(( < y   ))", Unexpected(Token::Less, src(4,1,5))),
            ("$(( <= y  ))", Unexpected(Token::Less, src(4,1,5))),
            ("$(( > y   ))", Unexpected(Token::Great, src(4,1,5))),
            ("$(( >= y  ))", Unexpected(Token::Great, src(4,1,5))),
            ("$(( == y  ))", Unexpected(Token::Equals, src(4,1,5))),
            ("$(( & y   ))", Unexpected(Token::Amp, src(4,1,5))),
            ("$(( ^ y   ))", Unexpected(Token::Caret, src(4,1,5))),
            ("$(( | y   ))", Unexpected(Token::Pipe, src(4,1,5))),
            ("$(( && y  ))", Unexpected(Token::AndIf, src(4,1,5))),
            ("$(( || y  ))", Unexpected(Token::OrIf, src(4,1,5))),
            ("$(( = y   ))", Unexpected(Token::Equals, src(4,1,5))),
            ("$(( *= y  ))", Unexpected(Token::Star, src(4,1,5))),
            ("$(( /= y  ))", Unexpected(Token::Slash, src(4,1,5))),
            ("$(( %= y  ))", Unexpected(Token::Percent, src(4,1,5))),
            ("$(( <<= y ))", Unexpected(Token::DLess, src(4,1,5))),
            ("$(( >>= y ))", Unexpected(Token::DGreat, src(4,1,5))),
            ("$(( &= y  ))", Unexpected(Token::Amp, src(4,1,5))),
            ("$(( ^= y  ))", Unexpected(Token::Caret, src(4,1,5))),
            ("$(( |= y  ))", Unexpected(Token::Pipe, src(4,1,5))),
            ("$(( ? y : z ))", Unexpected(Token::Question, src(4,1,5))),
            ("$(( , x + y ))", Unexpected(Token::Comma, src(4,1,5))),

            // Each of the following leading tokens will be parsed as unary
            // operators, thus the error will occur on the `=`.
            ("$(( != y  ))", Unexpected(Token::Equals, src(5,1,6))),
            ("$(( += y  ))", Unexpected(Token::Equals, src(5,1,6))),
            ("$(( -= y  ))", Unexpected(Token::Equals, src(5,1,6))),
        );

        for (s, correct) in cases.into_iter() {
            match make_parser(s).parameter() {
                Ok(w) => panic!("Unexpectedly parsed the source \"{}\" as\n{:?}", s, w),
                Err(ref err) => if err != &correct {
                    panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                           s, correct, err);
                },
            }
        }
    }

    #[test]
    fn test_arithmetic_substitution_precedence() {
        use syntax::ast::Arithmetic::*;

        fn var(x: &str) -> Box<Arithmetic> { Box::new(Var(String::from(x))) }

        let cases = vec!(
            ("~o++",   BitwiseNot(Box::new(PostIncr(String::from("o"))))),
            ("~(o+p)", BitwiseNot(Box::new(Add(var("o"), var("p"))))),
            ("-o++",   UnaryMinus(Box::new(PostIncr(String::from("o"))))),
            ("-(o+p)", UnaryMinus(Box::new(Add(var("o"), var("p"))))),
            ("++o",    PreIncr(String::from("o"))),
        );

        for (s, end) in cases.into_iter() {
            let correct = word_subst(ParameterSubstitution::Arith(Some(
                Sequence(vec!(
                    *var("x"),
                    Assign(String::from("a"), Box::new(
                        Ternary(var("b"), var("c"), Box::new(
                            LogicalOr(var("d"), Box::new(
                                LogicalAnd(var("e"), Box::new(
                                    BitwiseOr(var("f"), Box::new(
                                        BitwiseXor(var("g"), Box::new(
                                            BitwiseAnd(var("h"), Box::new(
                                                Eq(var("i"), Box::new(
                                                    Less(var("j"), Box::new(
                                                        ShiftLeft(var("k"), Box::new(
                                                            Add(var("l"), Box::new(
                                                                Mult(var("m"), Box::new(
                                                                    Pow(var("n"), Box::new(end))
                                                                ))
                                                            ))
                                                        ))
                                                    ))
                                                ))
                                            ))
                                        ))
                                    ))
                                ))
                            ))
                        ))
                    ))
                ))
            )));

            let src = format!("$(( x , a = b?c: d || e && f | g ^ h & i == j < k << l + m * n ** {} ))", s);
            match make_parser(&src).parameter() {
                Ok(w) => if w != correct {
                    panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", src, w, correct)
                },
                Err(err) => panic!("Failed to parse the source \"{}\": {}", src, err),
            }
        }
    }

    #[test]
    fn test_arithmetic_substitution_operators_of_equal_precedence() {
        use syntax::ast::Arithmetic::*;

        fn x() -> Box<Arithmetic> { Box::new(Var(String::from("x"))) }
        fn y() -> Box<Arithmetic> { Box::new(Var(String::from("y"))) }
        fn z() -> Box<Arithmetic> { Box::new(Var(String::from("z"))) }
        fn w() -> Box<Arithmetic> { Box::new(Var(String::from("w"))) }

        let cases = vec!(
            ("$(( x != y == z ))", Eq(Box::new(NotEq(x(), y())), z())),
            ("$(( x == y != z ))", NotEq(Box::new(Eq(x(), y())), z())),

            ("$(( x <  y < z ))", Less(Box::new(Less(x(), y())), z())),
            ("$(( x <= y < z ))", Less(Box::new(LessEq(x(), y())), z())),
            ("$(( x >  y < z ))", Less(Box::new(Great(x(), y())), z())),
            ("$(( x >= y < z ))", Less(Box::new(GreatEq(x(), y())), z())),

            ("$(( x << y >> z ))", ShiftRight(Box::new(ShiftLeft(x(), y())), z())),
            ("$(( x >> y << z ))", ShiftLeft(Box::new(ShiftRight(x(), y())), z())),

            ("$(( x + y - z ))", Sub(Box::new(Add(x(), y())), z())),
            ("$(( x - y + z ))", Add(Box::new(Sub(x(), y())), z())),

            ("$(( x * y / z % w ))", Modulo(Box::new(Div(Box::new(Mult(x(), y())), z())), w())),
            ("$(( x * y % z / w ))", Div(Box::new(Modulo(Box::new(Mult(x(), y())), z())), w())),
            ("$(( x / y * z % w ))", Modulo(Box::new(Mult(Box::new(Div(x(), y())), z())), w())),
            ("$(( x / y % z * w ))", Mult(Box::new(Modulo(Box::new(Div(x(), y())), z())), w())),
            ("$(( x % y * z / w ))", Div(Box::new(Mult(Box::new(Modulo(x(), y())), z())), w())),
            ("$(( x % y / z * w ))", Mult(Box::new(Div(Box::new(Modulo(x(), y())), z())), w())),

            ("$(( +!~x ))", UnaryPlus(Box::new(LogicalNot(Box::new(BitwiseNot(x())))))),
            ("$(( +~!x ))", UnaryPlus(Box::new(BitwiseNot(Box::new(LogicalNot(x())))))),
            ("$(( !+~x ))", LogicalNot(Box::new(UnaryPlus(Box::new(BitwiseNot(x())))))),
            ("$(( !~+x ))", LogicalNot(Box::new(BitwiseNot(Box::new(UnaryPlus(x())))))),
            ("$(( ~+!x ))", BitwiseNot(Box::new(UnaryPlus(Box::new(LogicalNot(x())))))),
            ("$(( ~!+x ))", BitwiseNot(Box::new(LogicalNot(Box::new(UnaryPlus(x())))))),

            ("$(( -!~x ))", UnaryMinus(Box::new(LogicalNot(Box::new(BitwiseNot(x())))))),
            ("$(( -~!x ))", UnaryMinus(Box::new(BitwiseNot(Box::new(LogicalNot(x())))))),
            ("$(( !-~x ))", LogicalNot(Box::new(UnaryMinus(Box::new(BitwiseNot(x())))))),
            ("$(( !~-x ))", LogicalNot(Box::new(BitwiseNot(Box::new(UnaryMinus(x())))))),
            ("$(( ~-!x ))", BitwiseNot(Box::new(UnaryMinus(Box::new(LogicalNot(x())))))),
            ("$(( ~!-x ))", BitwiseNot(Box::new(LogicalNot(Box::new(UnaryMinus(x())))))),

            ("$(( !~++x ))", LogicalNot(Box::new(BitwiseNot(Box::new(PreIncr(String::from("x"))))))),
            ("$(( ~!++x ))", BitwiseNot(Box::new(LogicalNot(Box::new(PreIncr(String::from("x"))))))),
            ("$(( !~--x ))", LogicalNot(Box::new(BitwiseNot(Box::new(PreDecr(String::from("x"))))))),
            ("$(( ~!--x ))", BitwiseNot(Box::new(LogicalNot(Box::new(PreDecr(String::from("x"))))))),

            ("$(( -+x ))", UnaryMinus(Box::new(UnaryPlus(x())))),
            ("$(( +-x ))", UnaryPlus(Box::new(UnaryMinus(x())))),
        );

        for (s, a) in cases.into_iter() {
            let correct = word_subst(ParameterSubstitution::Arith(Some(a)));
            match make_parser(s).parameter() {
                Ok(w) => if w != correct {
                    panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", s, w, correct)
                },
                Err(err) => panic!("Failed to parse the source \"{}\": {}", s, err),
            }
        }
    }

    #[test]
    fn ensure_parse_errors_are_send_and_sync() {
        fn send_and_sync<T: Send + Sync>() {}
        send_and_sync::<ParseError>();
    }

    #[test]
    fn ensure_parser_could_be_send_and_sync() {
        fn send_and_sync<T: Send + Sync>() {}
        send_and_sync::<Parser<::std::vec::IntoIter<Token>, builder::DefaultBuilder>>();
    }
}
