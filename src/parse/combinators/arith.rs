use crate::error::ParseError;
use crate::iter::{Multipeek, PositionIterator};
use crate::parse::combinators;
use crate::token::Token;

/// Parses an arithmetic variable name in the form `name` or `$name`.
pub fn arith_var<I>(iter: &mut I) -> Result<String, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
{
    combinators::skip_whitespace(iter);
    eat_maybe!(iter, {
        Token::Dollar => {},
    });
    eat!(iter, {
        Token::Name(n) => Ok(n),
    })
}
