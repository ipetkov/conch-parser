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
            Name(ref s)       |
            Literal(ref s)    |
            Whitespace(ref s) |
            Assignment(ref s) => s.chars().filter(|&c| c == '\n').count() as u64,

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
    /// Construct an `Unexpected` error using the given token. If `None` specified, the next
    /// token in the iterator will be used (or `UnexpectedEOF` if none left).
    fn make_unexpected_err(&mut self, tok: Option<Token>) -> Error {
        Error {
            line: self.iter.line,
            kind: tok.or_else(|| self.iter.next()).map_or(UnexpectedEOF, |t| Unexpected(t)),
        }
    }

    /// Creates a new Parser from a Token iterator.
    pub fn new(t: T) -> Parser<T> {
        Parser { iter: TokenIter::new(t) }
    }

    pub fn complete_command(&mut self) -> Result<Option<ast::Command>> {
        try!(self.linebreak());

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
        self.simple_command()
    }

    /// Tries to parse a simple command, e.g. "cmd arg1 arg2".
    ///
    /// An error will be returned if not even a command name can be found, thus
    /// caller should be expecting the presense of a simple command with certainty.
    pub fn simple_command(&mut self) -> Result<ast::Command> {
        let cmd = match try!(self.word()) {
            Some(w) => w,
            None => return Err(self.make_unexpected_err(None))
        };

        let mut args = Vec::new();
        while let Some(w) = try!(self.word()) {
            args.push(w);
        }

        Ok(ast::Command::Simple { cmd: cmd, args: args })
    }

    /// Parses a whitespace delimited chunk of text, honoring space quoting rules,
    /// and skipping leading space.
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
        self.skip_whitespace();

        let mut words = Vec::new();
        loop {
            match self.iter.peek() {
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
                // Also, comments are only recognized where a Newline is valid, thus '#'
                // becomes a literal if it occurs in the middle of a word.
                tok@Pound |
                tok@Assignment(_) => ast::Word::Literal(tok.to_string()),

                Name(s)    |
                Literal(s) => ast::Word::Literal(s),

                ParamAt            => ast::Word::Param(ast::Parameter::At),
                ParamStar          => ast::Word::Param(ast::Parameter::Star),
                ParamPound         => ast::Word::Param(ast::Parameter::Pound),
                ParamQuestion      => ast::Word::Param(ast::Parameter::Question),
                ParamDash          => ast::Word::Param(ast::Parameter::Dash),
                ParamDollar        => ast::Word::Param(ast::Parameter::Dollar),
                ParamBang          => ast::Word::Param(ast::Parameter::Bang),
                ParamPositional(p) => ast::Word::Param(ast::Parameter::Positional(p)),

                Dollar => if let Some(&Name(_)) = self.iter.peek() {
                    if let Some(Name(n)) = self.iter.next() {
                        ast::Word::Param(ast::Parameter::Var(n))
                    } else {
                        unreachable!()
                    }
                } else {
                    ast::Word::Literal("$".to_string())
                },

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

        // Fastforward through any whitespace for sanity
        self.skip_whitespace();
        Ok(ret)
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
    use syntax::parse::*;
    use syntax::token::*;

    fn make_parser(src: &str) -> Parser<Lexer<::std::str::Chars>> {
        Parser::new(Lexer::new(src.chars()))
    }

    fn make_parser_from_tokens(src: Vec<Token>) -> Parser<::std::vec::IntoIter<Token>> {
        Parser::new(src.into_iter())
    }

    #[test]
    fn test_linebreak_valid_with_comments_and_whitespace() {
        let mut p = make_parser("\n\t\t\t\n # comment1\n#comment2\n   \n");
        assert_eq!(p.linebreak().unwrap(), vec!(
                Newline(None),
                Newline(None),
                Newline(Some(" comment1".to_string())),
                Newline(Some("comment2".to_string())),
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
        assert_eq!(p.linebreak().unwrap(), vec!(Newline(Some("comment".to_string()))));
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
        assert_eq!(p.linebreak().unwrap().pop().unwrap(), Newline(Some("comment".to_string())));
    }

    #[test]
    fn test_and_or_correct_associativity() {
        let mut p = make_parser("foo || bar && baz");

        if let And(
            box Or( box Simple { cmd: foo, .. }, box Simple { cmd: bar, .. }),
            box Simple { cmd: baz, .. }
        ) = p.and_or().unwrap() {
            assert_eq!(foo, Word::Literal("foo".to_string()));
            assert_eq!(bar, Word::Literal("bar".to_string()));
            assert_eq!(baz, Word::Literal("baz".to_string()));
            return;
        }

        panic!("Incorrect parse result for Parse::and_or");
    }

    #[test]
    fn test_and_or_valid_with_newlines_after_operator() {
        let mut p = make_parser("foo ||\n\n\n\nbar && baz");

        if let And(
            box Or( box Simple { cmd: foo, .. }, box Simple { cmd: bar, .. }),
            box Simple { cmd: baz, .. }
        ) = p.and_or().unwrap() {
            assert_eq!(foo, Word::Literal("foo".to_string()));
            assert_eq!(bar, Word::Literal("bar".to_string()));
            assert_eq!(baz, Word::Literal("baz".to_string()));
            return;
        }

        panic!("Incorrect parse result for Parse::and_or");
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
        if let Pipe(true, cmds) = p.pipeline().unwrap() {
            if let [
                Simple { cmd: ref foo, .. },
                Simple { cmd: ref bar, .. },
                Simple { cmd: ref baz, .. },
            ] = &cmds[..] {
                assert_eq!(*foo, Word::Literal("foo".to_string()));
                assert_eq!(*bar, Word::Literal("bar".to_string()));
                assert_eq!(*baz, Word::Literal("baz".to_string()));
                return;
            }
        }

        panic!("Incorrect parse result for Parse::pipeline");
    }

    #[test]
    fn test_pipeline_valid_bangs_in_and_or() {
        let mut p = make_parser("! foo | bar || ! baz && ! foobar");
        if let And(box Or(box Pipe(true, _), box Pipe(true, _)), box Pipe(true, _)) = p.and_or().unwrap() {
            return;
        }

        panic!("Incorrect parse result for Parse::and_or with several !");
    }

    #[test]
    fn test_pipeline_no_bang_single_cmd_optimize_wrapper_out() {
        let mut p = make_parser("foo");
        if let Pipe(..) = p.pipeline().unwrap() {
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
                    Word::Literal("hello".to_string()),
                    Word::Literal("#".to_string()),
                    Word::Literal("world".to_string()),
        )));
    }

    #[test]
    fn test_comment_can_start_if_whitespace_before_pound() {
        let mut p = make_parser("hello #world");
        p.word().unwrap().expect("no valid word was discovered");
        let comment = p.linebreak().unwrap();
        assert_eq!(comment, vec!(Newline(Some("world".to_string()))));
    }
}

