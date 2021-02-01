use crate::ast::Arithmetic;
use crate::error::ParseError;
use crate::iter::{Multipeek, PositionIterator};
use crate::parse2::combinators;
use crate::parse2::Parser;
use crate::token::Token;

/// Parses expressions such as `(expr)`, numeric literals, `var`, `var++`, or `var--`.
/// Numeric literals must appear as a single `Literal` token. `Name` tokens will be
/// treated as variables.
pub fn arith_post_incr<I, PS, PV>(
    iter: &mut I,
    mut arith_subst: PS,
    mut arith_var: PV,
) -> Result<Arithmetic<String>, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    PS: Parser<I, Output = Arithmetic<String>, Error = ParseError>,
    PV: Parser<I, Output = String, Error = ParseError>,
{
    combinators::skip_whitespace(iter);
    eat_maybe!(iter, {
        Token::ParenOpen => {
            let expr = arith_subst.parse(iter)?;
            combinators::skip_whitespace(iter);
            eat!(iter, {
                Token::ParenClose => {},
            });
            return Ok(expr);
        },
    });

    let num = {
        let mut mp = iter.multipeek();
        if let Some(Token::Literal(s)) = mp.peek_next() {
            if s.starts_with("0x") || s.starts_with("0X") {
                // from_str_radix does not like it when 0x is present
                // in the string to parse, thus we should strip it off.
                // Also, if the string is empty from_str_radix will return
                // an error; shells like bash and zsh treat `0x` as `0x0`
                // so we will do the same.
                let num = &s[2..];
                if num.is_empty() {
                    Some(0)
                } else {
                    isize::from_str_radix(&s[2..], 16).ok()
                }
            } else if s.starts_with('0') {
                isize::from_str_radix(s, 8).ok()
            } else {
                isize::from_str_radix(s, 10).ok()
            }
        } else {
            None
        }
    };

    let expr = match num {
        Some(num) => {
            // Make sure we consume the Token::Literal which holds the number
            iter.next();
            Arithmetic::Literal(num)
        }
        None => {
            let var = arith_var.parse(iter)?;

            // We must be extra careful here because post-increment has a higher precedence
            // than addition/subtraction meaning post-increment operations will be parsed
            // before addition. Thus we should be absolutely certain we should parse a
            // post-increment operator and avoid confusing it with an addition operation
            // that is yet to be parsed.
            let post_incr = {
                combinators::skip_whitespace(iter);
                let mut mp = iter.multipeek();
                match mp.peek_next() {
                    Some(Token::Plus) => mp.peek_next() == Some(&Token::Plus),
                    Some(Token::Dash) => mp.peek_next() == Some(&Token::Dash),
                    _ => false,
                }
            };

            if post_incr {
                eat!(iter, {
                    Token::Plus => eat!(iter, {
                        Token::Plus => Arithmetic::PostIncr(var),
                    }),
                    Token::Dash => eat!(iter, {
                        Token::Dash => Arithmetic::PostDecr(var),
                    }),
                })
            } else {
                Arithmetic::Var(var)
            }
        }
    };
    Ok(expr)
}

/// Parses an arithmetic variable name in the form `name` or `$name`.
pub fn arith_var<I>(iter: &mut I) -> Result<String, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
{
    combinators::skip_whitespace(iter);
    eat_maybe!(iter, {
        Token::Dollar => {},
    });
    eat!(iter, {
        Token::Name(n) => Ok(n),
    })
}
