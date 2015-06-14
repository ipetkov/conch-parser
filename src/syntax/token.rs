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

    /// $
    Dollar,
    /// !
    Bang,
    /// ;
    Semi,
    /// &
    Amp,
    /// <
    Less,
    /// \>
    Great,
    /// |
    Pipe,
    /// ~
    Tilde,
    /// \#
    Pound,
    /// '
    SingleQuote,
    /// "
    DoubleQuote,
    /// `
    Backtick,

    /// &&
    AndIf,
    /// ||
    OrIf,
    /// ;;
    DSemi,

    /// <<
    DLess,
    /// \>>
    DGreat,
    /// \>&
    GreatAnd,
    /// <&
    LessAnd,
    /// \>&-
    GreatAndDash,
    /// <&-
    LessAndDash,
    /// <<-
    DLessDash,
    /// \>|
    Clobber,
    /// <>
    LessGreat,

    /// $@
    ParamAt,
    /// $*
    ParamStar,
    /// $#
    ParamPound,
    /// $?
    ParamQuestion,
    /// $-
    ParamDash,
    /// $$
    ParamDollar,
    /// $!
    ParamBang,
    /// $0, $1, ..., $9
    ParamPositional(u8),

    /// Any string of whitespace characters NOT including a newline.
    Whitespace(String),

    /// Any literal delimited by whitespace.
    Literal(String),
    /// A Literal that contains only alphanumerics or underscores, and does not start with a digit.
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
            GreatAndDash        => fmt.write_str(">&-"),
            LessAndDash         => fmt.write_str("<&-"),
            DLessDash           => fmt.write_str("<<-"),
            Clobber             => fmt.write_str(">|"),
            LessGreat           => fmt.write_str("<>"),
            ParamAt             => fmt.write_str("$@"),
            ParamStar           => fmt.write_str("$*"),
            ParamPound          => fmt.write_str("$#"),
            ParamQuestion       => fmt.write_str("$?"),
            ParamDash           => fmt.write_str("$-"),
            ParamDollar         => fmt.write_str("$$"),
            ParamBang           => fmt.write_str("$!"),
            Whitespace(ref s)   => fmt.write_str(s),
            Name(ref s)         => fmt.write_str(s),
            Literal(ref s)      => fmt.write_str(s),
            ParamPositional(p)  => write!(fmt, "${}", p),
            Assignment(ref s)   => write!(fmt, "{}=", s),
        }
    }
}
