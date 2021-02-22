use crate::error::ParseError;
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse2::combinators;
use crate::token::Token;

/// Checks that one of the specified tokens appears as a reserved word.
///
/// The token must be followed by a token which delimits a word when it is
/// unquoted/unescaped.
///
/// If a reserved word is found, the token which it matches will be
/// returned in case the caller cares which specific reserved word was found.
pub fn peek_reserved_token<'a, I>(iter: &mut I, tokens: &'a [Token]) -> Option<&'a Token>
where
    I: ?Sized + MultipeekIterator<Item = Token>,
{
    debug_assert!(!tokens.is_empty());

    combinators::skip_whitespace(iter);

    let mut mp = iter.multipeek();
    mp.peek_next()
        .and_then(|tok| tokens.iter().find(|&t| t == tok))
        .filter(|_| match mp.peek_next() {
            Some(delim) => delim.is_word_delimiter(),
            None => true, // EOF is also a valid delimeter
        })
}

/// Checks that one of the specified tokens appears as a reserved word
/// and consumes it, returning the token it matched in case the caller
/// cares which specific reserved word was found.
pub fn reserved_token<I>(iter: &mut I, tokens: &[Token]) -> Result<Token, ParseError>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
{
    match peek_reserved_token(iter, tokens) {
        Some(_) => Ok(iter.next().unwrap()),
        None => {
            // If the desired token is next, but we failed to find a reserved
            // token (because the token after it isn't a valid delimeter)
            // then the following token is the unexpected culprit, so we should
            // skip the upcoming one before forming the error.
            let skip_one = {
                let mut mp = iter.multipeek();
                let peeked = mp.peek_next();
                tokens.iter().any(|t| Some(t) == peeked)
            };

            if skip_one {
                iter.next();
            }
            Err(combinators::make_unexpected_err(iter))
        }
    }
}

/// Checks that one of the specified strings appears as a reserved word.
///
/// The word must appear as a single token, unquoted and unescaped, and
/// must be followed by a token which delimits a word when it is
/// unquoted/unescaped. The reserved word may appear as a `Token::Name`
/// or a `Token::Literal`.
///
/// If a reserved word is found, the string which it matches will be
/// returned in case the caller cares which specific reserved word was found.
pub fn peek_reserved_word<'a, I>(iter: &mut I, words: &[&'a str]) -> Option<&'a str>
where
    I: ?Sized + MultipeekIterator<Item = Token>,
{
    debug_assert!(!words.is_empty());

    combinators::skip_whitespace(iter);

    let mut mp = iter.multipeek();
    mp.peek_next()
        .and_then(|tok| match tok {
            Token::Name(kw) | Token::Literal(kw) => words.iter().find(|&w| w == kw).copied(),
            _ => None,
        })
        .filter(|_| match mp.peek_next() {
            Some(delim) => delim.is_word_delimiter(),
            None => true, // EOF is also a valid delimeter
        })
}

/// Checks that one of the specified strings appears as a reserved word
/// and consumes it, returning the string it matched in case the caller
/// cares which specific reserved word was found.
pub fn reserved_word<'a, I>(iter: &mut I, words: &[&'a str]) -> Option<&'a str>
where
    I: ?Sized + MultipeekIterator<Item = Token>,
{
    peek_reserved_word(iter, words).map(|s| {
        iter.next();
        s
    })
}
