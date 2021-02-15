use crate::error::ParseError;
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse2::combinators;
use crate::parse2::Parser;
use crate::token::Token;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pipeline<T> {
    pub invert_status: bool,
    pub cmds: Vec<T>,
}

/// Parses either a single command or a pipeline of commands.
///
/// For example `[!] foo | bar`.
pub fn pipeline<I, P>(iter: &mut I, mut command_parser: P) -> Result<Pipeline<P::Output>, P::Error>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
    P: Parser<I>,
    P::Error: From<ParseError>,
{
    combinators::skip_whitespace(iter);
    let invert_status = eat_maybe!(iter, {
        Token::Bang => true;
        _ => false,
    });

    let mut cmds = Vec::new();
    loop {
        combinators::skip_whitespace(iter);

        // We've already passed an apropriate spot for !, so it
        // is an error if it appears before the start of a command.
        if Some(&Token::Bang) == iter.multipeek().peek_next() {
            return Err(P::Error::from(combinators::make_unexpected_err(iter)));
        }

        cmds.push(command_parser.parse(iter)?);

        combinators::skip_whitespace(iter);

        eat_maybe!(iter, {
            Token::Pipe => {};
            _ => {
                return Ok(Pipeline {
                    invert_status,
                    cmds,
                });
            },
        });
    }
}
