use crate::error::ParseError;
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse2::{combinators, Parser};
use crate::token::Token;

/// Parses commands until a resered word (or EOF)
/// is reached, without consuming the reserved word.
pub fn command_group<I, PC, P>(
    iter: &mut I,
    reserved_words: &[&str],
    mut linebreak: PC,
    mut command: P,
) -> Result<
    combinators::TrailingComments<
        Vec<combinators::LeadingComments<PC::Output, P::Output>>,
        PC::Output,
    >,
    P::Error,
>
where
    I: ?Sized + MultipeekIterator<Item = Token>,
    PC: Parser<I>,
    P: Parser<I>,
    P::Error: From<PC::Error>,
{
    let mut cmds = Vec::new();
    let trailing_comments = loop {
        let leading_comments = linebreak.parse(iter)?;

        if combinators::peek_reserved_word(iter, reserved_words).is_some()
            || iter.multipeek().peek_next().is_none()
        {
            break leading_comments;
        }

        let item = command.parse(iter)?;
        cmds.push(combinators::LeadingComments {
            leading_comments,
            item,
        });
    };

    Ok(combinators::TrailingComments {
        item: cmds,
        trailing_comments,
    })
}

/// Parses any number of sequential commands between the `do` and `done` reserved words.
pub fn do_group<I, PC, P>(
    iter: &mut I,
    linebreak: PC,
    command: P,
) -> Result<
    combinators::TrailingComments<
        Vec<combinators::LeadingComments<PC::Output, P::Output>>,
        PC::Output,
    >,
    ParseError,
>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
    PC: Parser<I, Error = ParseError>,
    P: Parser<I, Error = ParseError>,
{
    let start_pos = iter.pos();
    combinators::reserved_word(iter, &["do"])
        .ok_or_else(|| combinators::make_unexpected_err(iter))?;

    let result = command_group(iter, &["done"], linebreak, command)?;

    if result.item.is_empty() {
        return Err(combinators::make_unexpected_err(iter));
    }

    combinators::reserved_word(iter, &["done"]).ok_or_else(|| ParseError::IncompleteCmd {
        cmd: "do",
        cmd_pos: start_pos,
        kw: "done",
        kw_pos: iter.pos(),
    })?;

    Ok(result)
}
