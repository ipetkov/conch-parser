use crate::ast::RedirectOrCmdWord;
use crate::error::ParseError;
use crate::iter::{Multipeek, PositionIterator};
use crate::parse2::combinators;
use crate::parse2::Parser;
use crate::token::Token;

/// Parses a continuous list of redirections and will error if any words
/// that are not valid file descriptors are found. Essentially used for
/// parsing redirection lists after a compound command like `while` or `if`.
pub fn redirect_list<I, W, R, P>(iter: &mut I, mut redirect: P) -> Result<Vec<R>, P::Error>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    P: Parser<I, Output = Option<RedirectOrCmdWord<R, W>>>,
    P::Error: From<ParseError>,
{
    let mut list = Vec::new();
    loop {
        combinators::skip_whitespace(iter);
        let start = iter.pos();
        match redirect.parse(iter)? {
            Some(RedirectOrCmdWord::Redirect(r)) => list.push(r),
            Some(RedirectOrCmdWord::CmdWord(_)) => {
                let err = ParseError::BadFd {
                    start,
                    end: iter.pos(),
                };
                return Err(err.into());
            }
            None => break,
        }
    }

    Ok(list)
}
