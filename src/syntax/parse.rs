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
    /// Encoutnered a word that could not be interpreted as a valid file descriptor.
    BadFd(ast::Word),
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
    col: u64,
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

    /// The column number of the input where the error occured.
    pub fn col(&self) -> u64 {
        self.col
    }
}

impl ::std::error::Error for Error {
    fn description(&self) -> &str {
        match self.kind {
            BadFd(_)      => "bad file descriptor found",
            Unexpected(_) => "unexpected token found",
            UnexpectedEOF => "unexpected end of input",
        }
    }
}

impl ::std::fmt::Display for Error {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match self.kind {
            BadFd(ref badfd) => write!(fmt, "bad file descriptor: {}", badfd),
            Unexpected(ref t) => write!(fmt, "found unexpected token '{}' on line {}", t, self.line),
            UnexpectedEOF => fmt.write_str("unexpected end of input"),
        }
    }
}

/// A Token iterator that keeps track of how many lines have been read.
struct TokenIter<I: Iterator<Item = Token>> {
    iter: ::std::iter::Peekable<I>,
    line: u64,
    col: u64,
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
            Name(ref s)       |
            Literal(ref s)    |
            Whitespace(ref s) |
            Assignment(ref s) => s.chars().filter(|&c| c == '\n').count() as u64,

            Newline => 1,
            _ => 0,
        };

        self.line += newlines;
        self.col += if newlines == 0 { next.len() as u64 } else { 0 };
        Some(next)
    }
}

impl<I: Iterator<Item = Token>> TokenIter<I> {
    /// Creates a new TokenIter from another Token iterator.
    fn new(iter: I) -> TokenIter<I> {
        TokenIter { iter: iter.peekable(), line: 1, col: 1 }
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
    /// Construct an `Unexpected` error using the given token. If `None` specified, the next
    /// token in the iterator will be used (or `UnexpectedEOF` if none left).
    fn make_unexpected_err(&mut self, tok: Option<Token>) -> Error {
        Error {
            line: self.iter.line,
            col: self.iter.col,
            kind: tok.or_else(|| self.iter.next()).map_or(UnexpectedEOF, |t| Unexpected(t)),
        }
    }

    fn make_bad_fd_error(&mut self, w: ast::Word) -> Error {
        Error {
            line: self.iter.line,
            col: self.iter.col,
            kind: BadFd(w),
        }
    }

    /// Creates a new Parser from a Token iterator.
    pub fn new(t: T) -> Parser<T> {
        Parser { iter: TokenIter::new(t) }
    }

    /// Parses a single complete command.
    ///
    /// For example, `foo && bar; baz` will yield two complete
    /// commands: And(foo, bar), and Simple(baz).
    pub fn complete_command(&mut self) -> Result<Option<ast::Command>> {
        try!(self.linebreak());

        if self.iter.peek().is_none() {
            return Ok(None);
        }

        let mut cmd = try!(self.and_or());

        match self.iter.peek() {
            Some(&Semi) => { self.iter.next(); },
            Some(&Amp) => {
                self.iter.next();
                cmd = ast::Command::Job(Box::new(cmd));
            },

            _ => {},
        }

        try!(self.linebreak());
        Ok(Some(cmd))
    }

    /// Parses compound AND/OR commands.
    ///
    /// Commands are left associative. For example `foo || bar && baz`
    /// parses to And(Or(foo, bar), baz).
    pub fn and_or(&mut self) -> Result<ast::Command> {
        let mut cmd = try!(self.pipeline());

        loop {
            match self.iter.peek() {
                Some(&OrIf)  |
                Some(&AndIf) => {},
                _ => break,
            }


            let ty = self.iter.next().unwrap();
            try!(self.linebreak());
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
    /// For example `[!] foo | bar`.
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
                try!(self.linebreak());
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
        Ok(ast::Command::Simple(Box::new(try!(self.simple_command()))))
    }

    /// Tries to parse a simple command, e.g. `cmd arg1 arg2 >redirect`.
    ///
    /// A valid command is expected to have at least an executable name, or a single
    /// variable assignment or redirection. Otherwise an error will be returned.
    pub fn simple_command(&mut self) -> Result<ast::SimpleCommand> {
        let mut cmd: Option<ast::Word> = None;
        let mut args = Vec::new();
        let mut vars = Vec::new();
        let mut io = Vec::new();

        loop {
            if let Some(&Assignment(_)) = self.iter.peek() {
                if let Some(Assignment(var)) = self.iter.next() {
                    let word = try!(self.word()).unwrap_or(ast::Word::Literal(String::new()));
                    vars.push((var, word));
                } else {
                    unreachable!();
                }

                // Make sure we continue checking for assignments,
                // otherwise it they can be interpreted as literal words.
                continue;
            }

            // A fd candidate must not be separated from the redirect token by whitespace
            let exec = match try!(self.word_preserve_trailing_whitespace()) {
                // If we found a fd candidate, try to parse a redirect with it
                Some(w) => match try!(self.maybe_redirect(Some(&w))) {
                    // Looks like there was a redirect, we should keep checking
                    Some(redirect) => { io.push(redirect); continue; },
                    // Word was either not numeric, or no redirect following
                    // so this word must be the executable of the command
                    None => w,
                },

                // Otherwise if no word is present, we are probably at a redirect
                None => match try!(self.maybe_redirect(None)) {
                    // Looks like there was a redirect, we should keep checking
                    Some(redirect) => { io.push(redirect); continue; },
                    // No redirects left, we should hit the command next
                    None => break,
                }
            };

            // Since there are no more assignments present and the current
            // word is not a fd candidate it must be the first real word,
            // and thus the executable name.
            debug_assert_eq!(cmd, None);
            cmd = Some(exec);
            break;
        }

        // Now that all assignments are taken care of, any other occurances of `=` will be
        // treated as literals when we attempt to parse a word out.
        loop {
            // A fd candidate must not be separated from the redirect token by whitespace
            match try!(self.word_preserve_trailing_whitespace()) {
                Some(w) => match try!(self.maybe_redirect(Some(&w))) {
                    Some(redirect) => io.push(redirect),
                    None => if cmd.is_none() { cmd = Some(w); } else { args.push(w) },
                },

                None => match try!(self.maybe_redirect(None)) {
                    Some(redirect) => io.push(redirect),
                    None => break,
                },
            }
        }

        // "Blank" commands are only allowed if redirection occurs
        // or if there is some variable assignment
        if cmd.is_none() && vars.is_empty() && io.is_empty() {
            return Err(self.make_unexpected_err(None));
        }

        Ok(ast::SimpleCommand {
            cmd: cmd,
            vars: vars,
            args: args,
            io: io,
        })
    }

    /// Parses a continuous list of redirections and will error if any words
    /// that are not valid file descriptors are found. Essentially used for
    /// parsing redirection lists after a `ast::CompoundCommand`.
    pub fn redirect_list(&mut self) -> Result<Vec<ast::Redirect>> {
        let mut list = Vec::new();
        loop {
            let word = try!(self.word_preserve_trailing_whitespace());
            match try!(self.maybe_redirect(word.as_ref())) {
                Some(io) => list.push(io),
                None if word.is_some() => return Err(self.make_bad_fd_error(word.unwrap())),
                None => break,
            }
        }

        Ok(list)
    }

    /// Parses a redirection token followed by a file path or descriptor as appropriate.
    ///
    /// For example, redirecting output `>out`, input `< in`, duplication `1>&2`,
    /// closing `2>&-`. To avoid complicating the return signature based on checking
    /// if a preceeding word is a valid file descriptor (and returning it if it isn't),
    /// the caller is responsible for performing this check and supplying the descriptor
    /// to the method.
    pub fn redirect(&mut self, src_fd: Option<u32>) -> Result<ast::Redirect> {
        use std::str::FromStr;

        // Sanity check that we really do have a redirect token
        let redir_tok = match self.iter.next() {
            Some(tok@Less)      |
            Some(tok@Great)     |
            Some(tok@DGreat)    |
            Some(tok@Clobber)   |
            Some(tok@LessAnd)   |
            Some(tok@GreatAnd)  |
            Some(tok@LessGreat) => tok,

            t => return Err(self.make_unexpected_err(t)),
        };

        // Ensure we have a path (or fd for duplication)
        let (dup_fd, path) = match try!(self.word()) {
            Some(w) => (u32::from_str(&w.to_string()).ok(), w),
            None => return Err(self.make_unexpected_err(None)),
        };

        let close = path == ast::Word::Literal(String::from("-"));

        let redirect = match redir_tok {
            Less      => ast::Redirect::Read(src_fd, path),
            Great     => ast::Redirect::Write(src_fd, path),
            DGreat    => ast::Redirect::Append(src_fd, path),
            Clobber   => ast::Redirect::Clobber(src_fd, path),
            LessGreat => ast::Redirect::ReadWrite(src_fd, path),

            LessAnd   if close            => ast::Redirect::CloseRead(src_fd),
            GreatAnd  if close            => ast::Redirect::CloseWrite(src_fd),
            LessAnd   if dup_fd.is_some() => ast::Redirect::DupRead(src_fd, dup_fd.unwrap()),
            GreatAnd  if dup_fd.is_some() => ast::Redirect::DupWrite(src_fd, dup_fd.unwrap()),

            // Duplication fd is not valid
            LessAnd  |
            GreatAnd => return Err(self.make_bad_fd_error(path)),

            _ => unreachable!(),
        };

        Ok(redirect)
    }

    /// Similar to `Parser::redirect`, but it accepts a word that may
    /// be a potential file descriptor. If it can be interpreted as such,
    /// (or no word is supplied) it is passed down to `Parser::redirect`.
    /// Otherwise no redirection will be parsed (an no error returned).
    fn maybe_redirect(&mut self, num: Option<&ast::Word>)
        -> Result<Option<ast::Redirect>>
    {
        use std::str::FromStr;

        let fd = match num {
            Some(n) => match u32::from_str(&n.to_string()).ok() {
                Some(fd) => Some(fd),
                None => return Ok(None),
            },
            None => None,
        };

        let redirect = match self.iter.peek() {
            Some(&Less)      |
            Some(&Great)     |
            Some(&LessAnd)   |
            Some(&GreatAnd)  |
            Some(&DGreat)    |
            Some(&LessGreat) |
            Some(&Clobber)   |
            Some(&DLess)     |
            Some(&DLessDash) => Some(try!(self.redirect(fd))),
            _ => None,
        };

        Ok(redirect)
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
    pub fn word(&mut self) -> Result<Option<ast::Word>> {
        let ret = try!(self.word_preserve_trailing_whitespace());
        self.skip_whitespace();
        Ok(ret)
    }

    /// Identical to `Parser::word()` but preserves trailing whitespace.
    pub fn word_preserve_trailing_whitespace(&mut self) -> Result<Option<ast::Word>> {
        self.skip_whitespace();

        let mut words = Vec::new();
        loop {
            match self.iter.peek() {
                Some(&CurlyOpen)          |
                Some(&CurlyClose)         |
                Some(&SingleQuote)        |
                Some(&ParamAt)            |
                Some(&ParamStar)          |
                Some(&ParamPound)         |
                Some(&ParamQuestion)      |
                Some(&ParamDash)          |
                Some(&ParamDollar)        |
                Some(&ParamBang)          |
                Some(&Dollar)             |
                Some(&Pound)              |
                Some(&ParamPositional(_)) |
                Some(&Assignment(_))      |
                Some(&Name(_))            |
                Some(&Literal(_))         => {},

                _ => break,
            }

            let w = match self.iter.next().unwrap() {
                // Assignments are only treated as such if they occur beforea command is
                // found. Any "Assignments" afterward should be treated as literals.
                //
                // Unless we are explicitly parsing a brace group, `{` and `}` should
                // be treated as literals.
                //
                // Also, comments are only recognized where a Newline is valid, thus '#'
                // becomes a literal if it occurs in the middle of a word.
                tok@Pound |
                tok@CurlyOpen  |
                tok@CurlyClose |
                tok@Assignment(_) => ast::Word::Literal(tok.to_string()),

                Name(s)    |
                Literal(s) => ast::Word::Literal(s),

                Dollar             |
                ParamAt            |
                ParamStar          |
                ParamPound         |
                ParamQuestion      |
                ParamDash          |
                ParamDollar        |
                ParamBang          |
                ParamPositional(_) => try!(self.parameter()),

                SingleQuote => {
                    // Make sure we actually find the closing quote before EOF
                    let mut found_close_quot = false;
                    let contents = self.iter.by_ref()
                        .take_while(|t| if t == &SingleQuote {
                            found_close_quot = true;
                            false // stop collecting
                        } else {
                            true // keep collecting literals
                        })
                        .map(|t| t.to_string())
                        .collect::<Vec<String>>()
                        .concat();

                    if found_close_quot {
                        ast::Word::Literal(contents)
                    } else {
                        return Err(self.make_unexpected_err(None));
                    }
                },

                _ => unreachable!(),
            };

            words.push(w);
        }

        let ret = if words.len() == 0 {
            None
        } else if words.len() == 1 {
            Some(words.pop().unwrap())
        } else {
            Some(ast::Word::Concat(words))
        };

        Ok(ret)
    }

    /// Parses a parameter such as `$$`, `$1`, `$foo`, etc.
    ///
    /// Since it is possible that a leading `$` is not followed by a valid
    /// parameter, the `$` will be treated as a literal. Thus this method
    /// returns a `ast::Word` instead of a `ast::Parameter`.
    pub fn parameter(&mut self) -> Result<ast::Word> {
        use syntax::ast::Parameter::*;
        use syntax::ast::Word::{Param, Literal};

        let param = match self.iter.next() {
            Some(ParamAt)            => Param(At),
            Some(ParamStar)          => Param(Star),
            Some(ParamPound)         => Param(Pound),
            Some(ParamQuestion)      => Param(Question),
            Some(ParamDash)          => Param(Dash),
            Some(ParamDollar)        => Param(Dollar),
            Some(ParamBang)          => Param(Bang),
            Some(ParamPositional(p)) => Param(Positional(p)),

            Some(Token::Dollar) => if let Some(&Name(_)) = self.iter.peek() {
                if let Some(Name(n)) = self.iter.next() {
                    Param(Var(n))
                } else {
                    unreachable!()
                }
            } else {
                Literal(Token::Dollar.to_string())
            },

            t => return Err(self.make_unexpected_err(t)),
        };

        Ok(param)
    }

    /// Keeps parsing complete commands until a given delimiter (or EOF) is found,
    /// without consuming it. Whitespace after commands is skipped, and will not
    /// be recognized as a delimiter. Useful in parsing do-groups or curly-groups.
    pub fn command_list(&mut self, delimiters: &[&Token]) -> Result<Vec<ast::Command>> {
        let mut cmds = Vec::new();
        loop {
            match self.iter.peek() {
                None => break,
                Some(next) => if delimiters.iter().any(|delim| delim == &next) {
                    break;
                }
            }

            match try!(self.complete_command()) {
                Some(c) => cmds.push(c),
                None => break,
            }

            self.skip_whitespace();
        }

        return Ok(cmds);
    }

    /// Parses any number of sequential commands between the `do` and `done`
    /// keywords. Each of the keywords must be a literal token, and cannot be
    /// quoted or concatenated.
    pub fn do_group(&mut self) -> Result<Vec<ast::Command>> {
        match self.iter.next() {
            Some(Token::Name(ref kw))    if kw == "do" => {},
            Some(Token::Literal(ref kw)) if kw == "do" => {},
            t => return Err(self.make_unexpected_err(t)),
        }

        let done_name = Token::Name(String::from("done"));
        let done_lit  = Token::Literal(String::from("done"));
        let result = try!(self.command_list(&[&done_lit, &done_name]));

        match self.iter.next() {
            Some(ref kw) if kw == &done_lit || kw == &done_name => Ok(result),
            t => Err(self.make_unexpected_err(t)),
        }
    }

    /// Parses any number of sequential commands between balanced `{` and `}`
    /// keywords. Each of the keywords must be a literal token, and cannot be quoted.
    pub fn brace_group(&mut self) -> Result<Vec<ast::Command>> {
        match self.iter.next() {
            Some(Token::CurlyOpen) => {},
            t => return Err(self.make_unexpected_err(t)),
        }

        let result = try!(self.command_list(&[&Token::CurlyClose]));

        match self.iter.next() {
            Some(Token::CurlyClose) => Ok(result),
            t => Err(self.make_unexpected_err(t)),
        }
    }

    /// Parses loop commands like `while` and `until` but does not parse any
    /// redirections that may follow.
    ///
    /// Since they are compound commands (and can have redirections applied to
    /// the entire loop) this method returns the relevant parts of the loop command,
    /// without constructing an AST node, it so that the caller can do so with redirections.
    ///
    /// Return structure is Result(is_until, guard_commands, body_commands).
    pub fn loop_command(&mut self) -> Result<(bool, Vec<ast::Command>, Vec<ast::Command>)> {
        let until = match self.iter.next() {
            Some(Token::Name(ref kw))    if kw == "while" => false,
            Some(Token::Literal(ref kw)) if kw == "while" => false,

            Some(Token::Name(ref kw))    if kw == "until" => true,
            Some(Token::Literal(ref kw)) if kw == "until" => true,
            t => return Err(self.make_unexpected_err(t)),
        };

        let guard = try!(self.command_list(&[
            &Token::Literal(String::from("do")),
            &Token::Name(String::from("do"))
        ]));

        let body = try!(self.do_group());

        Ok((until, guard, body))
    }

    /// Parses a single `if` command but does not parse any redirections that may follow.
    ///
    /// Since `if` is a compound command (and can have redirections applied to it) this
    /// method returns the relevant parts of the `if` command, without constructing an
    /// AST node, it so that the caller can do so with redirections.
    ///
    /// Return structure is Result( (condition, body)+, else_part ).
    pub fn if_command(&mut self) -> Result<(
        Vec<(Vec<ast::Command>, Vec<ast::Command>)>,
        Option<Vec<ast::Command>>)>
    {
        match self.iter.next() {
            Some(Token::Name(ref kw))    if kw == "if" => {},
            Some(Token::Literal(ref kw)) if kw == "if" => {},
            t => return Err(self.make_unexpected_err(t)),
        }

        let then_toks = [
            &Token::Name(String::from("then")),
            &Token::Literal(String::from("then")),
        ];

        let fi_name = Token::Name(String::from("fi"));
        let fi_lit  = Token::Literal(String::from("fi"));

        let post_body_toks = [
            &Token::Name(String::from("else")),
            &Token::Literal(String::from("else")),

            &Token::Name(String::from("elif")),
            &Token::Literal(String::from("elif")),

            &fi_name,
            &fi_lit,
        ];

        let post_else_toks = [
            &fi_name,
            &fi_lit,
        ];

        let mut branches = Vec::new();
        loop {
            let guard = try!(self.command_list(&then_toks));
            // Make sure we explicitly raise an error if guard branch is empty
            if guard.is_empty() {
                return Err(self.make_unexpected_err(None));
            }

            match self.iter.next() {
                Some(Token::Name(ref kw))    if kw == "then" => {},
                Some(Token::Literal(ref kw)) if kw == "then" => {},
                t => return Err(self.make_unexpected_err(t)),
            }

            // Make sure we explicitly raise an error if body branch is empty
            let body = try!(self.command_list(&post_body_toks));
            if guard.is_empty() {
                return Err(self.make_unexpected_err(None));
            }

            branches.push((guard, body));

            let els = match self.iter.next() {
                Some(Token::Name(ref kw))    if kw == "elif" => continue,
                Some(Token::Literal(ref kw)) if kw == "elif" => continue,

                // Make sure we explicitly raise an error if else branch is empty
                Some(Token::Name(ref kw))    if kw == "else" => {
                    let els = try!(self.command_list(&post_else_toks));
                    if els.is_empty() { return Err(self.make_unexpected_err(None)); } else { Some(els) }
                },
                Some(Token::Literal(ref kw)) if kw == "else" => {
                    let els = try!(self.command_list(&post_else_toks));
                    if els.is_empty() { return Err(self.make_unexpected_err(None)); } else { Some(els) }
                }

                Some(Token::Name(ref kw))    if kw == "fi"   => None,
                Some(Token::Literal(ref kw)) if kw == "fi"   => None,

                t => return Err(self.make_unexpected_err(t)),
            };

            // Make sure we consume the `fi` keyword
            if els.is_some() {
                match self.iter.next() {
                    Some(Token::Name(ref kw))    if kw == "fi"   => {},
                    Some(Token::Literal(ref kw)) if kw == "fi"   => {},
                    t => return Err(self.make_unexpected_err(t)),
                }
            }

            return Ok((branches, els))
        }
    }

    /// Skips over any encountered whitespace but preserves newlines.
    #[inline]
    pub fn skip_whitespace(&mut self) {
        while let Some(&Whitespace(_)) = self.iter.peek() {
            self.iter.next();
        }
    }

    /// Parses zero or more `Token::Newline`s, skipping whitespace and preserving comments.
    pub fn linebreak(&mut self) -> Result<Vec<ast::Newline>> {
        let mut lines = Vec::new();

        loop {
            match self.iter.peek() {
                Some(&Newline)       |
                Some(&Pound)         |
                Some(&Whitespace(_)) => {},
                _ => break,
            }

            let comment = match self.iter.next() {
                Some(Newline) => None,
                Some(Pound) => Some(self.iter.by_ref()
                        .take_while(|t| t != &Newline)
                        .map(|t| t.to_string())
                        .collect::<Vec<String>>()
                        .concat()
                ),

                Some(Whitespace(_)) => continue,
                _ => unreachable!(),
            };

            lines.push(ast::Newline(comment));
        }

        Ok(lines)
    }

}

#[cfg(test)]
mod test {
    use syntax::lexer::Lexer;

    use syntax::ast::*;
    use syntax::ast::Command::*;
    use syntax::ast::CompoundCommand::*;
    use syntax::parse::*;
    use syntax::token::Token;

    fn make_parser(src: &str) -> Parser<Lexer<::std::str::Chars>> {
        Parser::new(Lexer::new(src.chars()))
    }

    fn make_parser_from_tokens(src: Vec<Token>) -> Parser<::std::vec::IntoIter<Token>> {
        Parser::new(src.into_iter())
    }

    fn sample_simple_command() -> (Option<Word>, Vec<Word>, Vec<(String, Word)>, Vec<Redirect>) {
        (
            Some(Word::Literal(String::from("foo"))),
            vec!(
                Word::Literal(String::from("bar")),
                Word::Literal(String::from("baz")),
            ),
            vec!(
                (String::from("var"), Word::Literal(String::from("val"))),
                (String::from("ENV"), Word::Literal(String::from("true"))),
            ),
            vec!(
                Redirect::Clobber(Some(2),   Word::Literal(String::from("clob"))),
                Redirect::ReadWrite(Some(3), Word::Literal(String::from("rw"))),
                Redirect::Read(None,         Word::Literal(String::from("in"))),
            ),
        )
    }

    #[test]
    fn test_linebreak_valid_with_comments_and_whitespace() {
        let mut p = make_parser("\n\t\t\t\n # comment1\n#comment2\n   \n");
        assert_eq!(p.linebreak().unwrap(), vec!(
                Newline(None),
                Newline(None),
                Newline(Some(String::from(" comment1"))),
                Newline(Some(String::from("comment2"))),
                Newline(None)
            )
        );
    }

    #[test]
    fn test_linebreak_valid_empty() {
        let mut p = make_parser("");
        assert_eq!(p.linebreak().unwrap(), vec!());
    }

    #[test]
    fn test_linebreak_valid_nonnewline() {
        let mut p = make_parser("hello world");
        assert_eq!(p.linebreak().unwrap(), vec!());
    }

    #[test]
    fn test_linebreak_valid_eof_instead_of_newline() {
        let mut p = make_parser("#comment");
        assert_eq!(p.linebreak().unwrap(), vec!(Newline(Some(String::from("comment")))));
    }

    #[test]
    fn test_linebreak_single_quote_insiginificant() {
        let mut p = make_parser("#unclosed quote ' comment");
        assert_eq!(p.linebreak().unwrap(), vec!(Newline(Some(String::from("unclosed quote ' comment")))));
    }

    #[test]
    fn test_linebreak_double_quote_insiginificant() {
        let mut p = make_parser("#unclosed quote \" comment");
        assert_eq!(p.linebreak().unwrap(), vec!(Newline(Some(String::from("unclosed quote \" comment")))));
    }

    #[test]
    fn test_skip_whitespace_preserve_newline() {
        let mut p = make_parser("    \t\t \t \t\n   ");
        p.skip_whitespace();
        p.linebreak().ok().expect("Parser::skip_whitespace skips newlines");
    }

    #[test]
    fn test_skip_whitespace_preserve_comments() {
        let mut p = make_parser("    \t\t \t \t#comment\n   ");
        p.skip_whitespace();
        assert_eq!(p.linebreak().unwrap().pop().unwrap(), Newline(Some(String::from("comment"))));
    }

    #[test]
    fn test_and_or_correct_associativity() {
        let mut p = make_parser("foo || bar && baz");
        let parse = p.and_or().unwrap();

        if let And(
            box Or( box Simple(box ref foo), box Simple(box ref bar)),
            box Simple(box ref baz)
        ) = parse {
            assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
            assert_eq!(bar.cmd.as_ref().unwrap(), &Word::Literal(String::from("bar")));
            assert_eq!(baz.cmd.as_ref().unwrap(), &Word::Literal(String::from("baz")));
            return;
        }

        panic!("Incorrect parse result for Parse::and_or: {:?}", parse);
    }

    #[test]
    fn test_and_or_valid_with_newlines_after_operator() {
        let mut p = make_parser("foo ||\n\n\n\nbar && baz");
        let parse = p.and_or().unwrap();

        if let And(
            box Or( box Simple(box ref foo), box Simple(box ref bar)),
            box Simple(box ref baz)
        ) = parse {
            assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
            assert_eq!(bar.cmd.as_ref().unwrap(), &Word::Literal(String::from("bar")));
            assert_eq!(baz.cmd.as_ref().unwrap(), &Word::Literal(String::from("baz")));
            return;
        }

        panic!("Incorrect parse result for Parse::and_or: {:?}", parse);
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
        let parse = p.pipeline().unwrap();
        if let Pipe(true, ref cmds) = parse {
            if let [
                Simple(box ref foo),
                Simple(box ref bar),
                Simple(box ref baz),
            ] = &cmds[..] {
                assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
                assert_eq!(bar.cmd.as_ref().unwrap(), &Word::Literal(String::from("bar")));
                assert_eq!(baz.cmd.as_ref().unwrap(), &Word::Literal(String::from("baz")));
                return;
            }
        }

        panic!("Incorrect parse result for Parse::pipeline: {:?}", parse);
    }

    #[test]
    fn test_pipeline_valid_bangs_in_and_or() {
        let mut p = make_parser("! foo | bar || ! baz && ! foobar");
        let parse = p.and_or().unwrap();
        if let And(box Or(box Pipe(true, _), box Pipe(true, _)), box Pipe(true, _)) = parse {
            return;
        }

        panic!("Incorrect parse result for Parse::and_or with several `!`: {:?}", parse);
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
        let comment = p.linebreak().unwrap();
        assert_eq!(comment, vec!(Newline(Some(String::from("world")))));
    }

    #[test]
    fn test_complete_command_job() {
        let mut p = make_parser("foo && bar & baz");
        let cmd1 = p.complete_command().unwrap().expect("failed to parse first command");
        let cmd2 = p.complete_command().unwrap().expect("failed to parse second command");

        if let (
            &Job(box And(box Simple(box ref foo), box Simple(box ref bar))),
            &Simple(box ref baz),
        ) = (&cmd1, &cmd2) {
            assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
            assert_eq!(bar.cmd.as_ref().unwrap(), &Word::Literal(String::from("bar")));
            assert_eq!(baz.cmd.as_ref().unwrap(), &Word::Literal(String::from("baz")));
            return;
        }

        panic!("Incorrect parse result for Parse::complete_command:\n{:?}\n{:?}", cmd1, cmd2);
    }

    #[test]
    fn test_complete_command_non_eager_parse() {
        let mut p = make_parser("foo && bar; baz\n\nqux");
        let cmd1 = p.complete_command().unwrap().expect("failed to parse first command");
        let cmd2 = p.complete_command().unwrap().expect("failed to parse second command");
        let cmd3 = p.complete_command().unwrap().expect("failed to parse third command");

        if let (&And(box Simple(box ref foo), box Simple(box ref bar)),
            &Simple(box ref baz), &Simple(box ref qux)) = (&cmd1, &cmd2, &cmd3) {
                assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
                assert_eq!(bar.cmd.as_ref().unwrap(), &Word::Literal(String::from("bar")));
                assert_eq!(baz.cmd.as_ref().unwrap(), &Word::Literal(String::from("baz")));
                assert_eq!(qux.cmd.as_ref().unwrap(), &Word::Literal(String::from("qux")));
                return;
        }

        panic!("Incorrect parse result for Parse::complete_command: {:?}\n{:?}\n{:?}", cmd1, cmd2, cmd3);
    }

    #[test]
    fn test_complete_command_valid_no_input() {
        let mut p = make_parser("");
        p.complete_command().ok().expect("no input caused an error");
    }

    #[test]
    fn test_parameters_short() {
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
            assert_eq!(p.parameter().unwrap(), Word::Param(param));
        }

        assert_eq!(Word::Literal(String::from("$")), p.parameter().unwrap());
        p.parameter().unwrap_err(); // Stream should be exhausted
    }

    #[test]
    #[ignore] // FIXME: enable once implemented
    fn test_parameters_short_in_curlies() {
        let words = vec!(
            Parameter::At,
            Parameter::Star,
            Parameter::Pound,
            Parameter::Question,
            Parameter::Dash,
            Parameter::Dollar,
            Parameter::Bang,
            Parameter::Var(String::from("foo")),
            // FIXME: check for positional parameters, e.g. ${3} or ${100}
        );

        let mut p = make_parser("${@}${*}${#}${?}${-}${$}${!}${foo}");
        for param in words {
            assert_eq!(p.parameter().unwrap(), Word::Param(param));
        }

        p.parameter().unwrap_err(); // Stream should be exhausted
    }

    #[test]
    fn test_word_preserve_trailing_whitespace() {
        let mut p = make_parser("test       ");
        p.word_preserve_trailing_whitespace().unwrap();
        assert!(p.iter.next().is_some());
    }

    #[test]
    fn test_redirect_valid_close_without_whitespace() {
        let mut p = make_parser(">&-");
        assert_eq!(Redirect::CloseWrite(None), p.redirect(None).unwrap());
    }

    #[test]
    fn test_redirect_valid_close_with_whitespace() {
        let mut p = make_parser("<&       -");
        assert_eq!(Redirect::CloseRead(None), p.redirect(None).unwrap());
    }

    #[test]
    fn test_redirect_invalid_close_without_whitespace() {
        let mut p = make_parser(">&-asdf");
        p.redirect(None).unwrap_err();
    }

    #[test]
    fn test_redirect_invalid_close_with_whitespace() {
        let mut p = make_parser("<&       -asdf");
        p.redirect(None).unwrap_err();
    }

    #[test]
    fn test_redirect_fd_immediately_preceeding_redirection() {
        let mut p = make_parser("foo 1>>out");
        let cmd = p.simple_command().unwrap();
        assert_eq!(vec!(Redirect::Append(Some(1), Word::Literal(String::from("out")))), cmd.io);
    }

    #[test]
    fn test_redirect_fd_must_immediately_preceed_redirection() {
        let mut p = make_parser("foo 1 <>out");
        let cmd = p.simple_command().unwrap();
        assert_eq!(vec!(Redirect::ReadWrite(None, Word::Literal(String::from("out")))), cmd.io);
    }

    #[test]
    fn test_redirect_valid_dup_with_fd() {
        let mut p = make_parser("foo 1>&2");
        let cmd = p.simple_command().unwrap();
        assert_eq!(vec!(Redirect::DupWrite(Some(1), 2)), cmd.io);
    }

    #[test]
    fn test_redirect_valid_dup_without_fd() {
        let mut p = make_parser("foo 1 <&2");
        let cmd = p.simple_command().unwrap();
        assert_eq!(vec!(Redirect::DupRead(None, 2)), cmd.io);
    }

    #[test]
    fn test_redirect_valid_dup_with_whitespace() {
        let mut p = make_parser("foo 1<& 2");
        let cmd = p.simple_command().unwrap();
        assert_eq!(vec!(Redirect::DupRead(Some(1), 2)), cmd.io);
    }

    #[test]
    fn test_redirect_honors_arguments() {
        let mut p = make_parser(">| file1 >>file2");
        let correct1 = Redirect::Clobber(Some(3), Word::Literal(String::from("file1")));
        let correct2 = Redirect::Append(None, Word::Literal(String::from("file2")));
        assert_eq!(correct1, p.redirect(Some(3)).unwrap());
        assert_eq!(correct2, p.redirect(None).unwrap());
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
        assert_eq!(vec!(Redirect::CloseRead(Some(1234))), cmd.io);
    }

    #[test]
    fn test_redirect_dst_fd_need_not_be_single_token() {
        let mut p = make_parser_from_tokens(vec!(
            Token::GreatAnd,
            Token::Literal(String::from("12")),
            Token::Literal(String::from("34")),
        ));

        assert_eq!(Redirect::DupWrite(None, 1234), p.redirect(None).unwrap());
    }

    #[test]
    fn test_maybe_redirect_stops_if_argument_not_numeric() {
        let mut p = make_parser(">file");
        assert_eq!(None, p.maybe_redirect(Some(&Word::Literal(String::from("abc")))).unwrap());
        p.redirect(None).unwrap();
    }

    #[test]
    fn test_maybe_redirect_continues_if_argument_numeric() {
        let mut p = make_parser(">file");
        let correct = Redirect::Write(Some(123), Word::Literal(String::from("file")));
        assert_eq!(Some(correct), p.maybe_redirect(Some(&Word::Literal(String::from("123")))).unwrap());
    }

    #[test]
    fn test_maybe_redirect_continues_if_no_argument() {
        let mut p = make_parser("<file");
        let correct = Redirect::Read(None, Word::Literal(String::from("file")));
        assert_eq!(Some(correct), p.maybe_redirect(None).unwrap());
    }

    #[test]
    fn test_simple_command_valid_assignments_at_start_of_command() {
        let mut p = make_parser("var=val ENV=true foo bar baz");
        let (cmd, args, vars, _) = sample_simple_command();
        let correct = SimpleCommand { cmd: cmd, args: args, vars: vars, io: vec!() };
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_assignments_after_start_of_command_should_be_args() {
        let mut p = make_parser("var=val ENV=true foo var2=val2 bar baz var3=val3");
        let (cmd, mut args, vars, _) = sample_simple_command();
        args.insert(0, Word::Concat(vec!(Word::Literal(String::from("var2=")), Word::Literal(String::from("val2")))));
        args.push(Word::Concat(vec!(Word::Literal(String::from("var3=")), Word::Literal(String::from("val3")))));
        let correct = SimpleCommand { cmd: cmd, args: args, vars: vars, io: vec!() };
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_redirections_at_start_of_command() {
        let mut p = make_parser("2>|clob 3<>rw <in var=val ENV=true foo bar baz");
        let (cmd, args, vars, io) = sample_simple_command();
        let correct = SimpleCommand { cmd: cmd, args: args, vars: vars, io: io };
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_redirections_at_end_of_command() {
        let mut p = make_parser("var=val ENV=true foo bar baz 2>|clob 3<>rw <in");
        let (cmd, args, vars, io) = sample_simple_command();
        let correct = SimpleCommand { cmd: cmd, args: args, vars: vars, io: io };
        assert_eq!(correct, p.simple_command().unwrap());
    }

    #[test]
    fn test_simple_command_redirections_throughout_the_command() {
        let mut p = make_parser("2>|clob var=val 3<>rw ENV=true foo bar <in baz 4>&-");
        let (cmd, args, vars, mut io) = sample_simple_command();
        io.push(Redirect::CloseWrite(Some(4)));
        let correct = SimpleCommand { cmd: cmd, args: args, vars: vars, io: io };
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
            Redirect::Append(Some(1), Word::Literal(String::from("out"))),
            Redirect::DupRead(None, 2),
            Redirect::CloseWrite(Some(2)),
        ));
    }

    #[test]
    fn test_redirect_list_rejects_non_fd_words() {
        let mut p = make_parser("1>>out <in 2>&- abc");
        p.redirect_list().unwrap_err();
        let mut p = make_parser("1>>out abc<in 2>&-");
        p.redirect_list().unwrap_err();
    }

    #[test]
    fn test_do_group_valid() {
        let mut p = make_parser("do foo\nbar; baz; done");
        let cmds = p.do_group().unwrap();
        if let [
            Simple(box ref foo),
            Simple(box ref bar),
            Simple(box ref baz),
        ] = &cmds[..] {
            assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
            assert_eq!(bar.cmd.as_ref().unwrap(), &Word::Literal(String::from("bar")));
            assert_eq!(baz.cmd.as_ref().unwrap(), &Word::Literal(String::from("baz")));
            return;
        }

        panic!("Incorrect parse result for Parse::do_group: {:?}", cmds);
    }

    #[test]
    fn test_do_group_invalid_missing_separator() {
        let mut p = make_parser("do foo\nbar; baz done");
        p.do_group().unwrap_err();
    }

    #[test]
    fn test_do_group_valid_keyword_delimited_by_separator() {
        let mut p = make_parser("do foo done; done");
        let cmds = p.do_group().unwrap();
        if let [Simple(box ref foo)] = &cmds[..] {
            assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
            assert_eq!(foo.args[0], Word::Literal(String::from("done")));
            return;
        }

        panic!("Incorrect parse result for Parse::do_group: {:?}", cmds);
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
        let mut p = make_parser("'do' foo\nbar; baz; done");
        p.do_group().unwrap_err();
        let mut p = make_parser("do foo\nbar; baz; 'done'");
        p.do_group().unwrap_err();
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
    fn test_brace_group_valid() {
        let mut p = make_parser("{ foo\nbar; baz; }");
        let cmds = p.brace_group().unwrap();
        if let [
            Simple(box ref foo),
            Simple(box ref bar),
            Simple(box ref baz),
        ] = &cmds[..] {
            assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
            assert_eq!(bar.cmd.as_ref().unwrap(), &Word::Literal(String::from("bar")));
            assert_eq!(baz.cmd.as_ref().unwrap(), &Word::Literal(String::from("baz")));
            return;
        }

        panic!("Incorrect parse result for Parse::brace_group: {:?}", cmds);
    }

    #[test]
    fn test_brace_group_invalid_missing_separator() {
        let mut p = make_parser("{ foo\nbar; baz }");
        p.brace_group().unwrap_err();
    }

    #[test]
    fn test_brace_group_valid_keyword_delimited_by_separator() {
        let mut p = make_parser("{ foo }; }");
        let cmds = p.brace_group().unwrap();
        if let [Simple(box ref foo)] = &cmds[..] {
            assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
            assert_eq!(foo.args[0], Word::Literal(String::from("}")));
            return;
        }

        panic!("Incorrect parse result for Parse::brace_group: {:?}", cmds);
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
        let mut p = make_parser("'{' foo\nbar; baz; }");
        p.brace_group().unwrap_err();
        let mut p = make_parser("{ foo\nbar; baz; '}'");
        p.brace_group().unwrap_err();
    }

    #[test]
    fn test_loop_command_while_valid() {
        let mut p = make_parser("while guard1; guard2; do foo\nbar; baz; done");
        let (until, guards, cmds) = p.loop_command().unwrap();
        assert_eq!(until, false);
        if let [
            Simple(box ref guard1),
            Simple(box ref guard2),
        ] = &guards[..] {
            assert_eq!(guard1.cmd.as_ref().unwrap(), &Word::Literal(String::from("guard1")));
            assert_eq!(guard2.cmd.as_ref().unwrap(), &Word::Literal(String::from("guard2")));

            if let [
                Simple(box ref foo),
                Simple(box ref bar),
                Simple(box ref baz),
            ] = &cmds[..] {
                assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
                assert_eq!(bar.cmd.as_ref().unwrap(), &Word::Literal(String::from("bar")));
                assert_eq!(baz.cmd.as_ref().unwrap(), &Word::Literal(String::from("baz")));
                return;
            }
        }

        panic!("Incorrect parse result for Parse::loop_command: {:?}", cmds);
    }

    #[test]
    fn test_loop_command_until_valid() {
        let mut p = make_parser("until guard1\n guard2\n do foo\nbar; baz; done");
        let (until, guards, cmds) = p.loop_command().unwrap();
        assert_eq!(until, true);
        if let [
            Simple(box ref guard1),
            Simple(box ref guard2),
        ] = &guards[..] {
            assert_eq!(guard1.cmd.as_ref().unwrap(), &Word::Literal(String::from("guard1")));
            assert_eq!(guard2.cmd.as_ref().unwrap(), &Word::Literal(String::from("guard2")));

            if let [
                Simple(box ref foo),
                Simple(box ref bar),
                Simple(box ref baz),
            ] = &cmds[..] {
                assert_eq!(foo.cmd.as_ref().unwrap(), &Word::Literal(String::from("foo")));
                assert_eq!(bar.cmd.as_ref().unwrap(), &Word::Literal(String::from("bar")));
                assert_eq!(baz.cmd.as_ref().unwrap(), &Word::Literal(String::from("baz")));
                return;
            }
        }
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
        let mut p = make_parser("'while' guard do foo\nbar; baz; done");
        p.loop_command().unwrap_err();
        let mut p = make_parser("'until' guard do foo\nbar; baz; done");
        p.loop_command().unwrap_err();
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
    fn test_if_command_while_valid_with_else() {
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
                assert_eq!(body2.io,  vec!(Redirect::Append(Some(2), Word::Literal(String::from("app")))));

                let els = els.as_ref().unwrap();
                assert_eq!(els.len(), 1);
                if let Simple(ref els) = els[0] {
                    assert_eq!(els.cmd.as_ref().unwrap(), &Word::Literal(String::from("else")));
                    return;
                }
            }
        }

        panic!("Incorrect parse result for Parse::if_command: {:?}", (branches, els));
    }

    #[test]
    fn test_if_command_while_valid_without_else() {
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
                assert_eq!(body2.io,  vec!(Redirect::Append(Some(2), Word::Literal(String::from("app")))));

                assert_eq!(els, None);
                return;
            }
        }

        panic!("Incorrect parse result for Parse::if_command: {:?}", (branches, els));
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
        let mut p = make_parser("'if' guard1; then body1; elif guard2; then body2; else else; fi");
        p.if_command().unwrap_err();
        let mut p = make_parser("if guard1; then body1; elif guard2; then body2; else else; 'fi'");
        p.if_command().unwrap_err();
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
}

