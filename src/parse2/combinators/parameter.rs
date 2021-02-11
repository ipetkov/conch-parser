use crate::ast::builder::{
    CommandGroup, ComplexWordKind, ParameterSubstitutionKind, SimpleWordKind, WordKind,
};
use crate::ast::{Arithmetic, Parameter};
use crate::error::{ParseError, UnmatchedError};
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse2::{combinators, parse_fn, Parser};
use crate::token::Token;

/// Parses a parameters such as `$$`, `$1`, `$foo`, etc, or
/// parameter substitutions such as `$(cmd)`, `${param-word}`, etc.
///
/// Since it is possible that a leading `$` is not followed by a valid
/// parameter, the `$` should be treated as a literal. Thus this method
/// returns an `Word`, which will capture both cases where a literal or
/// parameter is parsed.
pub fn parameter<I, C, PA, PS, PW>(
    iter: &mut I,
    arith_subst: PA,
    subshell: PS,
    word: PW,
) -> Result<SimpleWordKind<C>, ParseError>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
    PA: Parser<I, Output = Arithmetic<String>, Error = ParseError>,
    PS: Parser<I, Output = CommandGroup<C>, Error = ParseError>,
    PW: Parser<I, Output = Option<ComplexWordKind<C>>, Error = ParseError>,
{
    eat!(iter, {
        Token::ParamPositional(p) => {
            let param = Parameter::Positional(p as u32);
            Ok(SimpleWordKind::Param(param))
        },

        Token::Dollar => {
            let mut mp = iter.multipeek();
            match mp.peek_next() {
                Some(Token::Star)     |
                Some(Token::Pound)    |
                Some(Token::Question) |
                Some(Token::Dollar)   |
                Some(Token::Bang)     |
                Some(Token::Dash)     |
                Some(Token::At)       |
                Some(Token::Name(_)) => {
                    drop(mp);
                    Ok(SimpleWordKind::Param(param_inner(iter)?))
                },

                Some(Token::ParenOpen) |
                Some(Token::CurlyOpen) => {
                    drop(mp);
                    param_subst(iter, arith_subst, subshell, word)
                },

                _ => Ok(SimpleWordKind::Literal(Token::Dollar.to_string())),
            }
        },
    })
}

/// Parses a parameter substitution in the form of `${...}`, `$(...)`, or `$((...))`.
///
/// Caller is responsible for parsing the opening `$`.
fn param_subst<I, C, PA, PS, PW>(
    iter: &mut I,
    mut arith_subst: PA,
    mut subshell: PS,
    mut word: PW,
) -> Result<SimpleWordKind<C>, ParseError>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
    PA: Parser<I, Output = Arithmetic<String>, Error = ParseError>,
    PS: Parser<I, Output = CommandGroup<C>, Error = ParseError>,
    PW: Parser<I, Output = Option<ComplexWordKind<C>>, Error = ParseError>,
{
    enum SubstType {
        Arith,
        Subshell,
        Regular,
    };

    let mut mp = iter.multipeek();
    let ty = match mp.peek_next() {
        Some(Token::ParenOpen) => {
            if matches!(mp.peek_next(), Some(Token::ParenOpen)) {
                SubstType::Arith
            } else {
                SubstType::Subshell
            }
        }
        Some(Token::CurlyOpen) => SubstType::Regular,
        _ => {
            drop(mp);
            return Err(combinators::make_unexpected_err(iter));
        }
    };
    drop(mp);

    let parse_param_subst_word = parse_fn(|iter| param_subst_word(iter, &mut word));

    let subst = match ty {
        SubstType::Arith => {
            iter.next(); // Skip past ParenOpen
            iter.next(); // Skip past ParenOpen

            // If we hit a paren right off the bat either the body is empty
            // or there is a stray paren which will result in an error either
            // when we look for the closing parens or sometime after.
            combinators::skip_whitespace(iter);
            let arith = eat_maybe!(iter, {
                Token::ParenClose => None;
                _ => {
                    let ret = Some(arith_subst.parse(iter)?);
                    combinators::skip_whitespace(iter);
                    eat!(iter, { Token::ParenClose => {}, });
                    ret
                },
            });

            // Some shells allow the closing parens to have whitespace in between
            combinators::skip_whitespace(iter);
            eat!(iter, { Token::ParenClose => {}, });

            ParameterSubstitutionKind::Arith(arith)
        }
        SubstType::Subshell => ParameterSubstitutionKind::Command(subshell.parse(iter)?),
        SubstType::Regular => {
            let curly_open_pos = iter.pos();
            iter.next(); // Skip the CurlyOpen

            let param = param_inner(iter)?;
            let param_is_pound = matches!(param, Parameter::Pound);

            let ret = eat_maybe!(iter, {
                Token::Percent => eat_maybe!(iter, {
                    Token::Percent => {
                        let word = param_subst_word(iter, parse_param_subst_word)?;
                        ParameterSubstitutionKind::RemoveLargestSuffix(param, word)
                    };
                    _ => {
                        let word = param_subst_word(iter, parse_param_subst_word)?;
                        ParameterSubstitutionKind::RemoveSmallestSuffix(param, word)
                    },
                }),

                Token::Pound => eat_maybe!(iter, {
                    Token::Pound => {
                        let word = param_subst_word(iter, parse_param_subst_word)?;
                        ParameterSubstitutionKind::RemoveLargestPrefix(param, word)
                    };
                    _ => {
                        let word = param_subst_word(iter, parse_param_subst_word)?;
                        if word.is_none() && param_is_pound {
                            // Handle ${##} case
                            ParameterSubstitutionKind::Len(Parameter::Pound)
                        } else {
                            ParameterSubstitutionKind::RemoveSmallestPrefix(param, word)
                        }
                    },
                });

                _ => {
                    if param_is_pound {
                        let mut mp = iter.multipeek();
                        match mp.peek_next() {
                            Some(Token::Colon)    |
                            Some(Token::Dash)     |
                            Some(Token::Equals)   |
                            Some(Token::Question) |
                            Some(Token::Plus)     |
                            Some(Token::CurlyClose) => {
                                drop(mp);
                                let ret = param_subst_body(iter, param, parse_param_subst_word)?;
                                let pos = iter.pos();
                                match iter.next() {
                                    Some(Token::CurlyClose) => return Ok(ret),
                                    Some(t) => return Err(ParseError::BadSubst(t, pos)),
                                    None => return Err(ParseError::from(UnmatchedError {
                                        token: Token::CurlyOpen,
                                        pos: curly_open_pos,
                                    })),
                                };
                            },

                            // Otherwise we must have ${#param}
                            _ => {
                                drop(mp);
                                let param = param_inner(iter)?;
                                ParameterSubstitutionKind::Len(param)
                            }
                        }
                    } else {
                        // Otherwise we have ${param...}
                        let ret = param_subst_body(iter, param, parse_param_subst_word)?;
                        let pos = iter.pos();
                        match iter.next() {
                            Some(Token::CurlyClose) => return Ok(ret),
                            Some(t) => return Err(ParseError::BadSubst(t, pos)),
                            None => return Err(ParseError::from(UnmatchedError {
                                token: Token::CurlyOpen,
                                pos: curly_open_pos,
                            })),
                        };
                    }
                },
            });

            eat_maybe!(iter, {
                Token::CurlyClose => {};
                _ => return Err(ParseError::from(UnmatchedError{
                    token: Token::CurlyOpen,
                    pos: curly_open_pos
                })),
            });

            ret
        }
    };

    Ok(SimpleWordKind::Subst(Box::new(subst)))
}

/// Parses everything between the curly braces of a parameter substitution.
///
/// For example, given `${<param><colon><operator><word>}`, this function will consume
/// the parameter, colon, operator, and word.
fn param_subst_body<I, C, P>(
    iter: &mut I,
    param: Parameter<String>,
    mut param_subst_word: P,
) -> Result<SimpleWordKind<C>, ParseError>
where
    I: ?Sized + MultipeekIterator<Item = Token>,
    P: Parser<I, Output = Option<ComplexWordKind<C>>, Error = ParseError>,
{
    use crate::ast::builder::ParameterSubstitutionKind as PSK;
    enum DashOrQuestion {
        Dash,
        Question,
        None,
    }

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
fn param_subst_word<I, C, P>(
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
fn param_inner<I>(iter: &mut I) -> Result<Parameter<String>, ParseError>
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
