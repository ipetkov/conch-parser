use crate::ast::builder::{ComplexWordKind, SimpleWordKind, WordKind};
use crate::error::ParseError;
use crate::iter::{Balanced, Multipeek, PeekablePositionIterator};
use crate::parse2::{combinators, Parser};
use crate::token::Token;

/// Parses a whitespace delimited chunk of text, honoring space quoting rules,
/// and skipping leading and trailing whitespace.
///
/// Since there are a large number of possible tokens that constitute a word,
/// (such as literals, parameters, variables, etc.) the caller may not know
/// for sure whether to expect a word, thus an optional result is returned
/// in the event that no word exists.
///
/// Note that an error can still arise if partial tokens are present
/// (e.g. malformed parameter).
pub fn word<I, C, PP, PB, PD>(
    mut iter: &mut I,
    mut parameter: PP,
    mut backticked: PB,
    mut double_quoted: PD,
) -> Result<Option<ComplexWordKind<C>>, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PeekablePositionIterator,
    PP: Parser<I, Output = SimpleWordKind<C>, Error = ParseError>,
    PB: Parser<I, Output = SimpleWordKind<C>, Error = ParseError>,
    PD: Parser<I, Output = Vec<SimpleWordKind<C>>, Error = ParseError>,
{
    combinators::skip_whitespace(iter);

    // Make sure we don't consume comments,
    // e.g. if a # is at the start of a word.
    if Some(&Token::Pound) == iter.multipeek().peek_next() {
        return Ok(None);
    }

    let mut words = Vec::new();
    loop {
        match iter.peek() {
            Some(Token::Backtick) => {
                words.push(WordKind::Simple(backticked.parse(iter)?));
                continue;
            }

            Some(Token::Dollar) | Some(Token::ParamPositional(_)) => {
                words.push(WordKind::Simple(parameter.parse(iter)?));
                continue;
            }

            Some(Token::DoubleQuote) => {
                words.push(WordKind::DoubleQuoted(double_quoted.parse(iter)?));
                continue;
            }

            Some(Token::SingleQuote) => {
                let mut buf = String::new();
                for t in Balanced::single_quoted(&mut iter) {
                    buf.push_str(t?.as_str())
                }

                words.push(WordKind::SingleQuoted(buf));
                continue;
            }

            Some(Token::CurlyOpen)
            | Some(Token::CurlyClose)
            | Some(Token::SquareOpen)
            | Some(Token::SquareClose)
            | Some(Token::Pound)
            | Some(Token::Star)
            | Some(Token::Question)
            | Some(Token::Tilde)
            | Some(Token::Bang)
            | Some(Token::Backslash)
            | Some(Token::Percent)
            | Some(Token::Dash)
            | Some(Token::Equals)
            | Some(Token::Plus)
            | Some(Token::Colon)
            | Some(Token::At)
            | Some(Token::Caret)
            | Some(Token::Slash)
            | Some(Token::Comma)
            | Some(Token::Name(_))
            | Some(Token::Literal(_)) => {}

            Some(Token::Newline)
            | Some(Token::ParenOpen)
            | Some(Token::ParenClose)
            | Some(Token::Semi)
            | Some(Token::Amp)
            | Some(Token::Pipe)
            | Some(Token::AndIf)
            | Some(Token::OrIf)
            | Some(Token::DSemi)
            | Some(Token::Less)
            | Some(Token::Great)
            | Some(Token::DLess)
            | Some(Token::DGreat)
            | Some(Token::GreatAnd)
            | Some(Token::LessAnd)
            | Some(Token::DLessDash)
            | Some(Token::Clobber)
            | Some(Token::LessGreat)
            | Some(Token::Whitespace(_))
            | None => break,
        }

        let w = match iter.next().unwrap() {
           // Unless we are explicitly parsing a brace group, `{` and `}` should
           // be treated as literals.
           //
           // Also, comments are only recognized where a Newline is valid, thus '#'
           // becomes a literal if it occurs in the middle of a word.
           tok @ Token::Bang      |
           tok @ Token::Pound     |
           tok @ Token::Percent   |
           tok @ Token::Dash      |
           tok @ Token::Equals    |
           tok @ Token::Plus      |
           tok @ Token::At        |
           tok @ Token::Caret     |
           tok @ Token::Slash     |
           tok @ Token::Comma     |
           tok @ Token::CurlyOpen |
           tok @ Token::CurlyClose => WordKind::Simple(SimpleWordKind::Literal(tok.to_string())),

           Token::Name(s) | Token::Literal(s) => WordKind::Simple(SimpleWordKind::Literal(s)),

           Token::Star => WordKind::Simple(SimpleWordKind::Star),
           Token::Question => WordKind::Simple(SimpleWordKind::Question),
           Token::Tilde => WordKind::Simple(SimpleWordKind::Tilde),
           Token::SquareOpen => WordKind::Simple(SimpleWordKind::SquareOpen),
           Token::SquareClose => WordKind::Simple(SimpleWordKind::SquareClose),
           Token::Colon => WordKind::Simple(SimpleWordKind::Colon),

           Token::Backslash => match iter.next() {
               // Escaped newlines become whitespace and a delimiter.
               // Alternatively, can't escape EOF, just ignore the slash
               Some(Token::Newline) | None => break,
               Some(t) => WordKind::Simple(SimpleWordKind::Escaped(t.to_string())),
           },

           // Parameters, double quoting, and backticks should have been
           // handled while peeking above.
           Token::Backtick           |
           Token::Dollar             |
           Token::ParamPositional(_) |
           Token::DoubleQuote        |
           // All word delimiters should have
           // broken the loop while peeking above.
           Token::Newline            |
           Token::ParenOpen          |
           Token::ParenClose         |
           Token::SingleQuote        |
           Token::Semi               |
           Token::Amp                |
           Token::Pipe               |
           Token::AndIf              |
           Token::OrIf               |
           Token::DSemi              |
           Token::Less               |
           Token::Great              |
           Token::DLess              |
           Token::DGreat             |
           Token::GreatAnd           |
           Token::LessAnd            |
           Token::DLessDash          |
           Token::Clobber            |
           Token::LessGreat          |
           Token::Whitespace(_) => unreachable!(),
       };

        words.push(w);
    }

    let ret = if words.is_empty() {
        None
    } else if words.len() == 1 {
        Some(ComplexWordKind::Single(words.pop().unwrap()))
    } else {
        Some(ComplexWordKind::Concat(words))
    };

    Ok(ret)
}
