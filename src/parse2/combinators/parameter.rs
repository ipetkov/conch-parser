use crate::ast::builder::{ComplexWordKind, SimpleWordKind, WordKind};
use crate::ast::Parameter;
use crate::error::ParseError;
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse2::Parser;
use crate::token::Token;

/// Parses everything between the curly braces of a parameter substitution.
///
/// For example, given `${<param><colon><operator><word>}`, this function will consume
/// the parameter, colon, operator, and word.
pub fn param_subst_body<I, C, PP, PS>(
    iter: &mut I,
    mut param: PP,
    mut param_subst_word: PS,
) -> Result<SimpleWordKind<C>, ParseError>
where
    I: ?Sized + MultipeekIterator<Item = Token>,
    PP: Parser<I, Output = Parameter<String>, Error = ParseError>,
    PS: Parser<I, Output = Option<ComplexWordKind<C>>, Error = ParseError>,
{
    use crate::ast::builder::ParameterSubstitutionKind as PSK;
    enum DashOrQuestion {
        Dash,
        Question,
        None,
    }

    let param = param.parse(iter)?;
    let has_colon = eat_maybe!(iter, {

        Token::Colon => true;
        _ => false,
    });

    let dash_or_question;
    let constructor = eat_maybe!(iter, {
        Token::Dash => {
            dash_or_question = DashOrQuestion::Dash;
            PSK::Default
        },
        Token::Equals => {
            dash_or_question = DashOrQuestion::None;
            PSK::Assign
        },
        Token::Question => {
            dash_or_question = DashOrQuestion::Question;
            PSK::Error
        },
        Token::Plus => {
            dash_or_question = DashOrQuestion::None;
            PSK::Alternative
        };

        _ => return Ok(SimpleWordKind::Param(param)),
    });

    let word = param_subst_word.parse(iter)?;
    let maybe_len = !has_colon && word.is_none() && matches!(param, Parameter::Pound);

    let ret = match dash_or_question {
        // We must carefully check if we get ${#-} or ${#?}, in which case
        // we have parsed a Len substitution and not something else
        DashOrQuestion::Dash if maybe_len => PSK::Len(Parameter::Dash),
        DashOrQuestion::Question if maybe_len => PSK::Len(Parameter::Question),
        _ => constructor(has_colon, param, word),
    };

    Ok(SimpleWordKind::Subst(Box::new(ret)))
}

/// Parses the word part of a parameter substitution, up to but not
/// including the closing curly brace.
///
/// All tokens that normally cannot be part of a word will be treated
/// as literals.
pub fn param_subst_word<I, C, P>(
    iter: &mut I,
    mut word: P,
) -> Result<Option<ComplexWordKind<C>>, ParseError>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
    P: Parser<I, Output = Option<ComplexWordKind<C>>, Error = ParseError>,
{
    let mut words = Vec::new();
    'capture_words: loop {
        'capture_literals: loop {
            let mut mp = iter.multipeek();
            let found_backslash = match mp.peek_next() {
                None | Some(Token::CurlyClose) => break 'capture_words,

                Some(Token::Backslash) => true,

                // Tokens that are normally skipped or ignored either always or at the
                // start of a word (e.g. #), we want to make sure we capture these ourselves.
                Some(t @ Token::Pound)
                | Some(t @ Token::ParenOpen)
                | Some(t @ Token::ParenClose)
                | Some(t @ Token::Semi)
                | Some(t @ Token::Amp)
                | Some(t @ Token::Pipe)
                | Some(t @ Token::AndIf)
                | Some(t @ Token::OrIf)
                | Some(t @ Token::DSemi)
                | Some(t @ Token::Less)
                | Some(t @ Token::Great)
                | Some(t @ Token::DLess)
                | Some(t @ Token::DGreat)
                | Some(t @ Token::GreatAnd)
                | Some(t @ Token::LessAnd)
                | Some(t @ Token::DLessDash)
                | Some(t @ Token::Clobber)
                | Some(t @ Token::LessGreat)
                | Some(t @ Token::Whitespace(_))
                | Some(t @ Token::Newline) => {
                    let w = t.as_str().to_owned();
                    words.push(WordKind::Simple(SimpleWordKind::Literal(w)));
                    false
                }

                // Tokens that are always part of a word,
                // don't have to handle them differently.
                Some(Token::CurlyOpen)
                | Some(Token::SquareOpen)
                | Some(Token::SquareClose)
                | Some(Token::SingleQuote)
                | Some(Token::DoubleQuote)
                | Some(Token::Star)
                | Some(Token::Question)
                | Some(Token::Tilde)
                | Some(Token::Bang)
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
                | Some(Token::Literal(_))
                | Some(Token::Backtick)
                | Some(Token::Dollar)
                | Some(Token::ParamPositional(_)) => break 'capture_literals,
            };

            // Escaped newlines are considered whitespace and usually ignored,
            // so we have to manually capture here.
            let skip_twice = if found_backslash {
                if let Some(Token::Newline) = mp.peek_next() {
                    let w = Token::Newline.as_str().to_owned();
                    words.push(WordKind::Simple(SimpleWordKind::Escaped(w)));
                    true
                } else {
                    // Backslash is escaping something other than newline,
                    // capture it like a regular word.
                    break 'capture_literals;
                }
            } else {
                false
            };

            drop(mp);
            iter.next(); // Skip the first token that was peeked above
            if skip_twice {
                iter.next();
            }
        }

        // FIXME: make a wrapped iterator here which stops on Token::CurlyClose
        match word.parse(iter)? {
            Some(ComplexWordKind::Single(w)) => words.push(w),
            Some(ComplexWordKind::Concat(ws)) => words.extend(ws),
            None => break 'capture_words,
        }
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
