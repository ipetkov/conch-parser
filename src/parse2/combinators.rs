use crate::error::ParseError;
use crate::iter::PositionIterator;
use crate::parse::SourcePos;
use crate::token::Token;

/// A macro that will consume and a token from an iterator when a specified pattern
/// is matched, then run the corresponding action. If nothing is matched, the
/// default expression is run.
macro_rules! eat_maybe {
    ($iter:ident, {
        $($($tok:pat)|+ $(if $if_expr:expr)? => $body:expr),+,
    }) => {
        eat_maybe!($iter, {
            $($($tok)|+ $(if $if_expr)? => $body),+;
            _ => {},
        })
    };

    ($iter:ident, {
        $($($tok:pat)|+ $(if $if_expr:expr)? => $body:expr),+;
        _ => $default:expr,
    }) => {{
        let mut mp = $crate::iter::MultipeekIterator::multipeek($iter);
        match mp.peek_next() {
            $($(Some($tok))|+ $(if $if_expr)? => {
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
        $($($tok:pat)|+ $(if $if_expr:expr)? => $body:expr),+,
    }) => {{
        let pos = $iter.pos();
        match $iter.next() {
            $($(Some($tok))|+ $(if $if_expr)? => $body),+,
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
mod reserved;
mod simple_command;
mod skip_whitespace;
mod word;

pub use self::and_or::and_or_list;
pub use self::arith::{
    arith_add, arith_assig, arith_bitwise_and, arith_bitwise_or, arith_bitwise_xor, arith_eq,
    arith_ineq, arith_logical_and, arith_logical_or, arith_mult, arith_post_incr, arith_pow,
    arith_shift, arith_subst, arith_ternary, arith_unary_op, arith_var,
};
pub use self::linebreak::{linebreak, newline};
pub use self::parameter::parameter;
pub use self::pipeline::{pipeline, Pipeline};
pub use self::redirect::{redirect, redirect_list};
pub use self::reserved::{peek_reserved_token, peek_reserved_word, reserved_token, reserved_word};
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
