use crate::error::ParseError;
use crate::iter::PositionIterator;
use crate::token::Token;

/// A macro that will consume and a token from an iterator when a specified pattern
/// is matched, then run the corresponding action. If nothing is matched, the
/// default block is run.
macro_rules! eat_maybe {
    ($iter:expr, { $($tok:pat => $blk:block),+ }) => {
        eat_maybe!($iter, { $($tok => $blk),+; _ => {} })
    };

    ($iter:expr, { $($tok:pat => $blk:block),+,}) => {
        eat_maybe!($iter, { $($tok => $blk),+ })
    };

    ($iter:expr, { $($tok:pat => $blk:block),+; _ => $default:block }) => {
        eat_maybe!($iter, { $($tok => $blk),+; _ => $default, })
    };

    ($iter:expr, { $($tok:pat => $blk:block),+; _ => $default:block, }) => {{
        let mut mp = $crate::iter::Multipeek::multipeek($iter);
        match mp.peek_next() {
            $(Some($tok) => {
                drop(mp);
                $iter.next();
                $blk
            }),+
            _ => $default,
        }
    }};
}

mod linebreak;
mod pipeline;
mod skip_whitespace;

pub use self::linebreak::{linebreak, newline};
pub use self::pipeline::{pipeline, Pipeline};
pub use self::skip_whitespace::skip_whitespace;

pub trait Parser<I: ?Sized> {
    type Output;
    type Error;

    fn parse(&mut self, cx: &mut I) -> Result<Self::Output, Self::Error>;
}

impl<F, I, O, E> Parser<I> for F
where
    I: ?Sized,
    F: ?Sized + FnMut(&mut I) -> Result<O, E>,
{
    type Output = O;
    type Error = E;

    fn parse(&mut self, cx: &mut I) -> Result<Self::Output, Self::Error> {
        (*self)(cx)
    }
}

fn make_unexpected_err<I>(iter: &mut I) -> ParseError
where
    I: ?Sized + PositionIterator<Item = Token>,
{
    let pos = iter.pos();
    iter.next().map_or(ParseError::UnexpectedEOF, |t| {
        ParseError::Unexpected(t, pos)
    })
}
