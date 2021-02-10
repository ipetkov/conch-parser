use crate::error::ParseError;
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse::SourcePos;
use crate::token::Token;

/// A macro that will consume and a token from an iterator when a specified pattern
/// is matched, then run the corresponding action. If nothing is matched, the
/// default expression is run.
macro_rules! eat_maybe {
    ($iter:ident, {
        $($tok:pat $(if $if_expr:expr)? => $body:expr),+,
    }) => {
        eat_maybe!($iter, {
            $($tok $(if $if_expr)? => $body),+;
            _ => {},
        })
    };

    ($iter:ident, {
        $($tok:pat $(if $if_expr:expr)? => $body:expr),+;
        _ => $default:expr,
    }) => {{
        let mut mp = $crate::iter::MultipeekIterator::multipeek($iter);
        match mp.peek_next() {
            $(Some($tok) $(if $if_expr)? => {
                drop(mp);
                $iter.next();
                $body
            }),+
            _ => {
                drop(mp);
                $default
            },
        }
    }};
}

/// A macro that will consume a specified token from an iterator
/// and run a corresponding action expression to do something with the token,
/// or it will construct and return an appropriate Unexpected error.
macro_rules! eat {
    ($iter:ident, {
        $($tok:pat $(if $if_expr:expr)? => $body:expr),+,
    }) => {{
        let pos = $iter.pos();
        match $iter.next() {
            $(Some($tok) $(if $if_expr)? => $body),+,
            t => return Err($crate::parse2::combinators::make_unexpected_err_parts(pos, t).into()),
        }
    }};
}

mod and_or;
mod arith;
mod linebreak;
mod parameter;
mod pipeline;
mod redirect;
mod simple_command;
mod skip_whitespace;
mod word;

pub use self::and_or::{and_or_list, AndOrList};
pub use self::arith::{
    arith_add, arith_assig, arith_bitwise_and, arith_bitwise_or, arith_bitwise_xor, arith_eq,
    arith_ineq, arith_logical_and, arith_logical_or, arith_mult, arith_post_incr, arith_pow,
    arith_shift, arith_subst, arith_ternary, arith_unary_op, arith_var,
};
pub use self::linebreak::{linebreak, newline};
pub use self::parameter::param_inner;
pub use self::pipeline::{pipeline, Pipeline};
pub use self::redirect::{redirect, redirect_list};
pub use self::simple_command::simple_command;
pub use self::skip_whitespace::skip_whitespace;
pub use self::word::word;

fn make_unexpected_err<I>(iter: &mut I) -> ParseError
where
    I: ?Sized + PositionIterator<Item = Token>,
{
    make_unexpected_err_parts(iter.pos(), iter.next())
}

fn make_unexpected_err_parts(pos: SourcePos, tok: Option<Token>) -> ParseError {
    tok.map_or(ParseError::UnexpectedEOF, |t| {
        ParseError::Unexpected(t, pos)
    })
}

/// Checks that one of the specified tokens appears as a reserved word.
///
/// The token must be followed by a token which delimits a word when it is
/// unquoted/unescaped.
///
/// If a reserved word is found, the token which it matches will be
/// returned in case the caller cares which specific reserved word was found.
pub(crate) fn peek_reserved_token<'a, I>(iter: &mut I, tokens: &'a [Token]) -> Option<&'a Token>
where
    I: ?Sized + MultipeekIterator<Item = Token>,
{
    debug_assert!(!tokens.is_empty());

    skip_whitespace(iter);

    let mut mp = iter.multipeek();
    mp.peek_next()
        .and_then(|tok| tokens.iter().find(|&t| t == tok))
        .filter(|_| match mp.peek_next() {
            Some(delim) => delim.is_word_delimiter(),
            None => true, // EOF is also a valid delimeter
        })
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
pub(crate) fn peek_reserved_word<I>(iter: &mut I, words: &[&'static str]) -> Option<&'static str>
where
    I: ?Sized + MultipeekIterator<Item = Token>,
{
    debug_assert!(!words.is_empty());

    skip_whitespace(iter);

    let mut mp = iter.multipeek();
    mp.peek_next()
        .and_then(|tok| match tok {
            Token::Name(kw) | Token::Literal(kw) => words.iter().find(|&w| w == kw).copied(),
            _ => None,
        })
        .filter(|_| match mp.peek_next() {
            Some(delim) => delim.is_word_delimiter(),
            None => true, // EOF is also a valid delimeter
        })
}
