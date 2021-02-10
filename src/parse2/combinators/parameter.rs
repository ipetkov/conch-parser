use crate::ast::builder::{ComplexWordKind, SimpleWordKind, WordKind};
use crate::ast::Parameter;
use crate::error::ParseError;
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse2::{combinators, Parser};
use crate::token::Token;

/// Parses a valid parameter that can appear inside a set of curly braces.
pub fn param_inner<I>(iter: &mut I) -> Result<Parameter<String>, ParseError>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
{
    use std::str::FromStr;

    let start_pos = iter.pos();
    let param = match iter.next() {
        Some(Token::Star) => Parameter::Star,
        Some(Token::Pound) => Parameter::Pound,
        Some(Token::Question) => Parameter::Question,
        Some(Token::Dollar) => Parameter::Dollar,
        Some(Token::Bang) => Parameter::Bang,
        Some(Token::Dash) => Parameter::Dash,
        Some(Token::At) => Parameter::At,

        Some(Token::Name(n)) => Parameter::Var(n),
        Some(t @ Token::Literal(_)) => match u32::from_str(t.as_str()) {
            Ok(n) => Parameter::Positional(n),
            Err(_) => return Err(ParseError::BadSubst(t, start_pos)),
        },

        Some(t) => return Err(ParseError::BadSubst(t, start_pos)),
        None => return Err(ParseError::UnexpectedEOF),
    };

    Ok(param)
}
