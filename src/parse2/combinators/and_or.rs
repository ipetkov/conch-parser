use crate::ast::{AndOr, AndOrList};
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse2::combinators;
use crate::parse2::Parser;
use crate::token::Token;

/// Parses a sequence of `&&`/`||` commands.
pub fn and_or_list<I, P>(iter: &mut I, mut pipeline: P) -> Result<AndOrList<P::Output>, P::Error>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
    P: Parser<I>,
{
    let first = pipeline.parse(iter)?;
    let mut rest = Vec::new();

    loop {
        combinators::skip_whitespace(iter);
        let constructor = eat_maybe!(iter, {
            Token::AndIf => AndOr::And,
            Token::OrIf => AndOr::Or;
            _ => break,
        });

        let next = pipeline.parse(iter)?;
        rest.push(constructor(next));
    }

    Ok(AndOrList { first, rest })
}
