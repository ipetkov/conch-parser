use crate::ast::{self, builder};
use crate::iter::{Multipeek, PositionIterator};
use crate::parse2::combinators;
use crate::parse2::Parser;
use crate::token::Token;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AndOrList<T> {
    pub first: T,
    pub rest: Vec<(Vec<builder::Newline>, ast::AndOr<T>)>,
}

/// Parses a sequence of `&&`/`||` commands.
pub fn and_or_list<I, P>(
    iter: &mut I,
    mut pipeline_parser: P,
) -> Result<AndOrList<P::Output>, P::Error>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    P: Parser<I>,
{
    let first = pipeline_parser.parse(iter)?;
    let mut rest = Vec::new();

    loop {
        combinators::skip_whitespace(iter);
        let is_and = eat_maybe!(iter, {
            Token::AndIf => true,
            Token::OrIf  => false;
            _ => break,
        });

        let post_sep_comments = combinators::linebreak(iter);
        let next = pipeline_parser.parse(iter)?;

        let next = if is_and {
            ast::AndOr::And(next)
        } else {
            ast::AndOr::Or(next)
        };

        rest.push((post_sep_comments, next));
    }

    Ok(AndOrList { first, rest })
}
