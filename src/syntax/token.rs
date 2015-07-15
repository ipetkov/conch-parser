//! This module defines the tokens of the shell language.

use std::fmt;
use self::Token::*;

/// The representation of (context free) shell tokens.
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Token {
    /// \n
    Newline,

    /// (
    ParenOpen,
    /// )
    ParenClose,
    /// {
    CurlyOpen,
    /// }
    CurlyClose,

    /// !
    Bang,
    /// ~
    Tilde,
    /// \#
    Pound,
    /// *
    Star,
    /// ?
    Question,
    /// \\
    Backslash,
    /// %
    Percent,

    /// '
    SingleQuote,
    /// "
    DoubleQuote,
    /// `
    Backtick,

    /// ;
    Semi,
    /// &
    Amp,
    /// |
    Pipe,
    /// &&
    AndIf,
    /// ||
    OrIf,
    /// ;;
    DSemi,

    /// <
    Less,
    /// \>
    Great,
    /// <<
    DLess,
    /// \>>
    DGreat,
    /// \>&
    GreatAnd,
    /// <&
    LessAnd,
    /// <<-
    DLessDash,
    /// \>|
    Clobber,
    /// <>
    LessGreat,

    /// $
    Dollar,
    /// $@
    ///
    /// Must be its own token to avoid lumping the `@` with a `Literal`
    /// since it doesn't have its own token.
    ParamAt,
    /// $-
    ///
    /// Must be its own token to avoid lumping the `-` with a `Literal`
    /// since it doesn't have its own token.
    ParamDash,
    /// $0, $1, ..., $9
    ///
    /// Must be its own token to avoid lumping the positional parameter
    /// as a `Literal` if the parameter is concatenated to something.
    ParamPositional(u8),

    /// Any string of whitespace characters NOT including a newline.
    Whitespace(String),

    /// Any literal delimited by whitespace.
    Literal(String),
    /// A Literal capable of being used as a variable or function name. According to the POSIX
    /// standard it should only contain alphanumerics or underscores, and does not start with a digit.
    Name(String),

    /// A `Name` that was immediately followed by an equals sign, e.g. `foo=` becomes Assignment("foo").
    Assignment(String),
}

impl fmt::Display for Token {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            Newline             => fmt.write_str("\n"),
            ParenOpen           => fmt.write_str("("),
            ParenClose          => fmt.write_str(")"),
            CurlyOpen           => fmt.write_str("{"),
            CurlyClose          => fmt.write_str("}"),
            Dollar              => fmt.write_str("$"),
            Bang                => fmt.write_str("!"),
            Semi                => fmt.write_str(";"),
            Amp                 => fmt.write_str("&"),
            Less                => fmt.write_str("<"),
            Great               => fmt.write_str(">"),
            Pipe                => fmt.write_str("|"),
            Tilde               => fmt.write_str("~"),
            Pound               => fmt.write_str("#"),
            Star                => fmt.write_str("*"),
            Question            => fmt.write_str("?"),
            Backslash           => fmt.write_str("\\"),
            Percent             => fmt.write_str("%"),
            SingleQuote         => fmt.write_str("\'"),
            DoubleQuote         => fmt.write_str("\""),
            Backtick            => fmt.write_str("`"),
            AndIf               => fmt.write_str("&&"),
            OrIf                => fmt.write_str("||"),
            DSemi               => fmt.write_str(";;"),
            DLess               => fmt.write_str("<<"),
            DGreat              => fmt.write_str(">>"),
            GreatAnd            => fmt.write_str(">&"),
            LessAnd             => fmt.write_str("<&"),
            DLessDash           => fmt.write_str("<<-"),
            Clobber             => fmt.write_str(">|"),
            LessGreat           => fmt.write_str("<>"),
            ParamAt             => fmt.write_str("$@"),
            ParamDash           => fmt.write_str("$-"),
            Whitespace(ref s)   => fmt.write_str(s),
            Name(ref s)         => fmt.write_str(s),
            Literal(ref s)      => fmt.write_str(s),
            ParamPositional(p)  => write!(fmt, "${}", p),
            Assignment(ref s)   => write!(fmt, "{}=", s),
        }
    }
}

impl Token {
    /// Returns the number of characters it took to recognize a token.
    pub fn len(&self) -> usize {
        match *self {
            Newline     |
            ParenOpen   |
            ParenClose  |
            CurlyOpen   |
            CurlyClose  |
            Dollar      |
            Bang        |
            Star        |
            Question    |
            Backslash   |
            Percent     |
            Semi        |
            Amp         |
            Less        |
            Great       |
            Pipe        |
            Tilde       |
            Pound       |
            SingleQuote |
            DoubleQuote |
            Backtick    => 1,

            AndIf         |
            OrIf          |
            DSemi         |
            DLess         |
            DGreat        |
            GreatAnd      |
            LessAnd       |
            Clobber       |
            LessGreat     |
            ParamAt       |
            ParamDash     |
            ParamPositional(_) => 2,

            DLessDash => 3,

            Whitespace(ref s) |
            Literal(ref s)    |
            Name(ref s)       => s.len(),
            Assignment(ref s) => s.len() + 1, // Don't forget the '='
        }
    }

    /// Indicates whether a word can be delimited by this token
    /// when the token is **not** quoted or escaped.
    pub fn is_word_delimiter(&self) -> bool {
        match *self {
            Newline           |
            ParenOpen         |
            ParenClose        |
            Semi              |
            Amp               |
            Less              |
            Great             |
            Pipe              |
            AndIf             |
            OrIf              |
            DSemi             |
            DLess             |
            DGreat            |
            GreatAnd          |
            LessAnd           |
            DLessDash         |
            Clobber           |
            LessGreat         |
            Whitespace(_) => true,

            Bang               |
            Star               |
            Question           |
            Backslash          |
            SingleQuote        |
            DoubleQuote        |
            Backtick           |
            Percent            |
            CurlyOpen          |
            CurlyClose         |
            Dollar             |
            Tilde              |
            Pound              |
            ParamAt            |
            ParamDash          |
            Name(_)            |
            Literal(_)         |
            ParamPositional(_) |
            Assignment(_)      => false,
        }
    }
}
