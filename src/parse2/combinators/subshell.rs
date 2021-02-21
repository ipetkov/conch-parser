use crate::error::{ParseError, UnmatchedError};
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse2::{combinators, Parser};
use crate::token::Token;

pub struct Subshell<C, T> {
    pub body: Vec<combinators::LeadingComments<C, T>>,
    pub trailing_comments: C,
}

/// Parses any number of sequential commands between balanced `(` and `)`.
pub fn subshell<I, PL, P, C>(
    empty_body_ok: bool,
    iter: &mut I,
    mut linebreak: PL,
    mut command: P,
) -> Result<Subshell<PL::Output, P::Output>, ParseError>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
    PL: Parser<I, Error = ParseError>,
    P: Parser<I, Output = C, Error = ParseError>,
{
    let start_pos = iter.pos();
    eat!(iter, {
        Token::ParenOpen => {},
    });

    let mut body = Vec::new();

    loop {
        let leading_comments = linebreak.parse(iter)?;

        let mut mp = iter.multipeek();
        match mp.peek_next() {
            Some(Token::ParenClose) => {
                drop(mp);

                if body.is_empty() && !empty_body_ok {
                    return Err(combinators::make_unexpected_err(iter));
                }

                iter.next();
                return Ok(Subshell {
                    body,
                    trailing_comments: leading_comments,
                });
            }
            None => {
                let err = ParseError::from(UnmatchedError {
                    token: Token::ParenOpen,
                    pos: start_pos,
                });
                return Err(err.into());
            }
            Some(_) => {}
        };
        drop(mp);

        body.push(combinators::LeadingComments {
            leading_comments,
            item: command.parse(iter)?,
        });
    }
}
