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
    /// [
    SquareOpen,
    /// ]
    SquareClose,

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
    /// -
    Dash,
    /// =
    Equals,
    /// +
    Plus,
    /// :
    Colon,
    /// @
    At,
    /// ^
    Caret,
    /// /
    Slash,
    /// ,
    Comma,

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
}

impl fmt::Display for Token {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            Newline             => fmt.write_str("\n"),
            ParenOpen           => fmt.write_str("("),
            ParenClose          => fmt.write_str(")"),
            CurlyOpen           => fmt.write_str("{"),
            CurlyClose          => fmt.write_str("}"),
            SquareOpen          => fmt.write_str("["),
            SquareClose         => fmt.write_str("]"),
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
            Dash                => fmt.write_str("-"),
            Equals              => fmt.write_str("="),
            Plus                => fmt.write_str("+"),
            Colon               => fmt.write_str(":"),
            At                  => fmt.write_str("@"),
            Caret               => fmt.write_str("^"),
            Slash               => fmt.write_str("/"),
            Comma               => fmt.write_str(","),
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
            Whitespace(ref s)   => fmt.write_str(s),
            Name(ref s)         => fmt.write_str(s),
            Literal(ref s)      => fmt.write_str(s),
            ParamPositional(p)  => write!(fmt, "${}", p),
        }
    }
}

impl Token {
    /// Returns if the token's length is zero.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of characters it took to recognize a token.
    pub fn len(&self) -> usize {
        match *self {
            Newline     |
            ParenOpen   |
            ParenClose  |
            CurlyOpen   |
            CurlyClose  |
            SquareOpen  |
            SquareClose |
            Dollar      |
            Bang        |
            Star        |
            Question    |
            Backslash   |
            Percent     |
            Dash        |
            Equals      |
            Plus        |
            Colon       |
            At          |
            Caret       |
            Slash       |
            Comma       |
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
            ParamPositional(_) => 2,

            DLessDash => 3,

            Whitespace(ref s) |
            Literal(ref s)    |
            Name(ref s)       => s.len(),
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
            Dash               |
            Equals             |
            Plus               |
            Colon              |
            At                 |
            Caret              |
            Slash              |
            Comma              |
            CurlyOpen          |
            CurlyClose         |
            SquareOpen         |
            SquareClose        |
            Dollar             |
            Tilde              |
            Pound              |
            Name(_)            |
            Literal(_)         |
            ParamPositional(_) => false,
        }
    }
}
