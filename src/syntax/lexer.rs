//! This module defines a lexer to recognize tokens of the shell language.

use super::token::Token;
use super::token::Token::*;
use self::TokenOrLiteral::*;

#[derive(PartialEq, Eq, Debug)]
enum TokenOrLiteral {
    Tok(Token),
    Escaped(Option<Token>),
    Lit(char),
}

/// Converts raw characters into shell tokens.
pub struct Lexer<I: Iterator<Item = char>> {
    inner: ::std::iter::Peekable<I>,
    peeked: Option<TokenOrLiteral>,
}

impl<I: Iterator<Item = char>> Lexer<I> {
    /// Creates a new Lexer from any char iterator.
    pub fn new(iter: I) -> Lexer<I> {
        Lexer {
            inner: iter.peekable(),
            peeked: None,
        }
    }

    #[inline]
    fn next_is(&mut self, c: char) -> bool {
        let is = self.inner.peek() == Some(&c);
        if is { self.inner.next(); }
        is
    }

    fn next_internal(&mut self) -> Option<TokenOrLiteral> {
        if self.peeked.is_some() {
            return self.peeked.take();
        }

        let cur = match self.inner.next() {
            Some(c) => c,
            None => return None,
        };

        let tok = match cur {
            '\n' => Newline,
            '!' => Bang,
            '~' => Tilde,
            '#' => Pound,
            '*' => Star,
            '?' => Question,
            '%' => Percent,
            '-' => Dash,
            '=' => Equals,
            '+' => Plus,
            ':' => Colon,
            '@' => At,

            // Make sure that we treat the next token as a single character,
            // preventing multi-char tokens from being recognized. This is
            // important because something like `\&&` would mean that the
            // first & is a literal while the second retains its properties.
            // We will let the parser deal with what actually becomes a literal.
            '\\' => return Some(Escaped(self.inner.next().and_then(|c| {
                Lexer::new(::std::iter::once(c)).next()
            }))),

            '\'' => SingleQuote,
            '"' => DoubleQuote,
            '`' => Backtick,

            ';' => if self.next_is(';') { DSemi } else { Semi },
            '&' => if self.next_is('&') { AndIf } else { Amp  },
            '|' => if self.next_is('|') { OrIf  } else { Pipe },

            '(' => ParenOpen,
            ')' => ParenClose,
            '{' => CurlyOpen,
            '}' => CurlyClose,
            '[' => SquareOpen,
            ']' => SquareClose,

            '$' => match self.inner.peek() {
                // Positional parameters are 0-9, so we only
                // need to check a single digit ahead.
                Some(&d) if d.is_digit(10) => {
                    self.inner.next();
                    ParamPositional(d.to_digit(10).unwrap() as u8)
                },
                _ => Dollar,
            },

            '<' => if self.next_is('<') {
                if self.next_is('-') { DLessDash } else { DLess }
            } else if self.next_is('&') {
                LessAnd
            } else if self.next_is('>') {
                LessGreat
            } else {
                Less
            },

            '>' => if self.next_is('&') {
                GreatAnd
            } else if self.next_is('>') {
                DGreat
            } else if self.next_is('|') {
                Clobber
            } else {
                Great
            },

            // Newlines are valid whitespace, however, we want to tokenize them separately!
            c if c.is_whitespace() => {
                if c == '\r' && self.next_is('\n') {
                    Newline
                } else {
                    let mut buf = String::new();
                    buf.push(c);

                    // NB: Can't use filter here because it will advance the iterator too far.
                    loop {
                        match self.inner.peek() {
                            Some(&'\r') => {
                                self.inner.next();
                                if let Some(&'\n') = self.inner.peek() {
                                    break;
                                } else {
                                    buf.push('\r');
                                }
                            },
                            Some(&c) if c.is_whitespace() && c != '\n' =>
                                buf.push(self.inner.next().unwrap()),
                            _ => break,
                        }
                    }

                    Whitespace(buf)
                }
            },

            c => return Some(Lit(c)),
        };

        Some(Tok(tok))
    }
}

impl<I: Iterator<Item = char>> Iterator for Lexer<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        fn name_start_char(c: char) -> bool {
            c == '_' || c.is_alphabetic()
        }

        fn is_digit(c: char) -> bool {
            c.is_digit(10)
        }

        fn name_char(c: char) -> bool {
            is_digit(c) || name_start_char(c)
        }

        match self.next_internal() {
            None => None,
            Some(Tok(t)) => Some(t),
            Some(Escaped(t)) => {
                debug_assert_eq!(self.peeked, None);
                self.peeked = t.map(Tok);
                Some(Backslash)
            },

            Some(Lit(c)) => {
                let is_name = name_start_char(c);
                let mut word = String::new();
                word.push(c);

                loop {
                    match self.next_internal() {
                        // If we hit a token, delimit the current word w/o losing the token
                        Some(tok@Tok(_)) |
                        Some(tok@Escaped(_)) => {
                            debug_assert_eq!(self.peeked, None);
                            self.peeked = Some(tok);
                            break;
                        },

                        // Make sure we delimit valid names whenever a non-name char comes along
                        Some(Lit(c)) if is_name && !name_char(c) => {
                            debug_assert_eq!(self.peeked, None);
                            self.peeked = Some(Lit(c));
                            return Some(Name(word));
                        },

                        // Otherwise, keep consuming characters for the literal
                        Some(Lit(c)) => word.push(c),

                        None => break,
                    }
                }

                if is_name {
                    Some(Name(word))
                } else {
                    Some(Literal(word))
                }
            },
        }
    }
}

#[cfg(test)]
mod test {
    use syntax::token::Token;
    use syntax::token::Token::*;

    macro_rules! check_tok {
        ($fn_name:ident, $tok:expr) => {
            #[test]
            #[allow(non_snake_case)]
            fn $fn_name() {
                let s = format!("{}", $tok);
                let mut lex = super::Lexer::new(s.chars());
                assert_eq!($tok, lex.next().unwrap());
            }
        }
    }

    macro_rules! lex_str {
        ($fn_name:ident, $s:expr, $($tok:expr),+ ) => {
            #[test]
            #[allow(non_snake_case)]
            fn $fn_name() {
                let lex = super::Lexer::new($s.chars());
                let tokens: Vec<Token> = lex.collect();
                assert_eq!(tokens, vec!( $($tok),+ ));
            }
        }
    }

    check_tok!(check_Newline, Newline);
    check_tok!(check_ParenOpen, ParenOpen);
    check_tok!(check_ParenClose, ParenClose);
    check_tok!(check_CurlyOpen, CurlyOpen);
    check_tok!(check_CurlyClose, CurlyClose);
    check_tok!(check_SquareOpen, SquareOpen);
    check_tok!(check_SquareClose, SquareClose);
    check_tok!(check_Dollar, Dollar);
    check_tok!(check_Bang, Bang);
    check_tok!(check_Semi, Semi);
    check_tok!(check_Amp, Amp);
    check_tok!(check_Less, Less);
    check_tok!(check_Great, Great);
    check_tok!(check_Pipe, Pipe);
    check_tok!(check_Tilde, Tilde);
    check_tok!(check_Star, Star);
    check_tok!(check_Question, Question);
    check_tok!(check_Percent, Percent);
    check_tok!(check_Dash, Dash);
    check_tok!(check_Equals, Equals);
    check_tok!(check_Plus, Plus);
    check_tok!(check_Colon, Colon);
    check_tok!(check_At, At);
    check_tok!(check_Pound, Pound);
    check_tok!(check_DoubleQuote, DoubleQuote);
    check_tok!(check_Backtick, Backtick);
    check_tok!(check_AndIf, AndIf);
    check_tok!(check_OrIf, OrIf);
    check_tok!(check_DSemi, DSemi);
    check_tok!(check_DLess, DLess);
    check_tok!(check_DGreat, DGreat);
    check_tok!(check_GreatAnd, GreatAnd);
    check_tok!(check_LessAnd, LessAnd);
    check_tok!(check_DLessDash, DLessDash);
    check_tok!(check_Clobber, Clobber);
    check_tok!(check_LessGreat, LessGreat);
    check_tok!(check_Whitespace, Whitespace(String::from(" \t\r")));
    check_tok!(check_Name, Name(String::from("abc_23_defg")));
    check_tok!(check_Literal, Literal(String::from(",abcdefg80hijklmnop")));
    check_tok!(check_ParamPositional, ParamPositional(9));

    lex_str!(check_RN_is_newline, "\r\n", Newline);
    lex_str!(check_R_is_newline_only_when_followed_by_N, "\r\r\n", Whitespace(String::from("\r")), Newline);

    lex_str!(check_greedy_Amp,    "&&&",  AndIf, Amp);
    lex_str!(check_greedy_Pipe,   "|||",  OrIf, Pipe);
    lex_str!(check_greedy_Semi,   ";;;",  DSemi, Semi);
    lex_str!(check_greedy_Less,   "<<<",  DLess, Less);
    lex_str!(check_greedy_Great,  ">>>",  DGreat, Great);
    lex_str!(check_greedy_Less2,  "<<<-", DLess, Less, Dash);

    lex_str!(check_bad_Assigmnent_and_value, "5foobar=test",
        Literal(String::from("5foobar")),
        Equals,
        Name(String::from("test"))
    );

    lex_str!(check_Literal_and_Name_combo, "hello ,asdf5_ 6world __name ^.abc _test2",
             Name(String::from("hello")),
             Whitespace(String::from(" ")),
             Literal(String::from(",asdf5_")),
             Whitespace(String::from(" ")),
             Literal(String::from("6world")),
             Whitespace(String::from(" ")),
             Name(String::from("__name")),
             Whitespace(String::from(" ")),
             Literal(String::from("^.abc")),
             Whitespace(String::from(" ")),
             Name(String::from("_test2"))
     );

    lex_str!(check_escape_Backslash,       "\\\\",  Backslash, Backslash);
    lex_str!(check_escape_AndIf,           "\\&&",  Backslash, Amp, Amp);
    lex_str!(check_escape_DSemi,           "\\;;",  Backslash, Semi, Semi);
    lex_str!(check_escape_DLess,           "\\<<",  Backslash, Less, Less);
    lex_str!(check_escape_DLessDash,       "\\<<-", Backslash, Less, Less, Dash);
    lex_str!(check_escape_ParamPositional, "\\$0",  Backslash, Dollar, Literal(String::from("0")));
    lex_str!(check_escape_Whitespace,      "\\  ",  Backslash, Whitespace(String::from(" ")), Whitespace(String::from(" ")));
    lex_str!(check_escape_Name,            "\\ab",  Backslash, Name(String::from("a")), Name(String::from("b")));
    lex_str!(check_escape_Literal,         "\\^3",  Backslash, Literal(String::from("^")), Literal(String::from("3")));

    lex_str!(check_no_tokens_lost, "word\\'", Name(String::from("word")), Backslash, SingleQuote);
}
