use crate::ast::Arithmetic;
use crate::error::ParseError;
use crate::iter::{Multipeek, PositionIterator};
use crate::parse2::combinators;
use crate::parse2::Parser;
use crate::token::Token;

macro_rules! arith_parse {
    (
        $(#[$fn_attr:meta])*
        pub fn $fn_name:ident,
        $next:ident,
        $($tok:pat => $constructor:path),+,
    ) => {
        $(#[$fn_attr])*
        pub fn $fn_name<T, I, P>(iter: &mut I, mut $next: P) -> Result<P::Output, ParseError>
        where
            I: ?Sized + Multipeek<Item = Token> + PositionIterator,
            P: Parser<I, Output = Arithmetic<T>, Error = ParseError>,
        {
            let mut expr = $next.parse(iter)?;
            loop {
                combinators::skip_whitespace(iter);
                eat_maybe!(iter, {
                    $($tok => {
                        let next = $next.parse(iter)?;
                        expr = $constructor(Box::new(expr), Box::new(next));
                    }),+;
                    _ => break,
                });
            }
            Ok(expr)
        }
    }
}

/// Parses expressions such as `expr == expr` or `expr != expr`.
pub fn arith_eq<T, I, P>(iter: &mut I, mut arith_ineq: P) -> Result<P::Output, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    P: Parser<I, Output = Arithmetic<T>, Error = ParseError>,
{
    let mut expr = arith_ineq.parse(iter)?;
    loop {
        combinators::skip_whitespace(iter);
        let eq_type = eat_maybe!(iter, {
            Token::Equals => true,
            Token::Bang => false;
            _ => break,
        });

        eat!(iter, {
            Token::Equals => {},
        });

        let next = arith_ineq.parse(iter)?;
        expr = if eq_type {
            Arithmetic::Eq(Box::new(expr), Box::new(next))
        } else {
            Arithmetic::NotEq(Box::new(expr), Box::new(next))
        };
    }
    Ok(expr)
}

/// Parses expressions such as `expr < expr`,`expr <= expr`,`expr > expr`,`expr >= expr`.
pub fn arith_ineq<T, I, P>(iter: &mut I, mut arith_shift: P) -> Result<P::Output, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    P: Parser<I, Output = Arithmetic<T>, Error = ParseError>,
{
    let mut expr = arith_shift.parse(iter)?;
    loop {
        combinators::skip_whitespace(iter);
        eat_maybe!(iter, {
            Token::Less => {
                let eq = eat_maybe!(iter, {
                    Token::Equals => true;
                    _ => false,
                });
                let next = arith_shift.parse(iter)?;

                expr = if eq {
                    Arithmetic::LessEq(Box::new(expr), Box::new(next))
                } else {
                    Arithmetic::Less(Box::new(expr), Box::new(next))
                };
            },
            Token::Great => {
                let eq = eat_maybe!(iter, {
                    Token::Equals => true;
                    _ => false,
                });
                let next = arith_shift.parse(iter)?;

                expr = if eq {
                    Arithmetic::GreatEq(Box::new(expr), Box::new(next))
                } else {
                    Arithmetic::Great(Box::new(expr), Box::new(next))
                };
            };
            _ => break,
        });
    }
    Ok(expr)
}

arith_parse! {
    /// Parses expressions such as `expr << expr` or `expr >> expr`.
    pub fn arith_shift,
    arith_add,
    Token::DLess => Arithmetic::ShiftLeft,
    Token::DGreat => Arithmetic::ShiftRight,
}

arith_parse! {
    /// Parses expressions such as `expr + expr` or `expr - expr`.
    pub fn arith_add,
    arith_mult,
    Token::Plus => Arithmetic::Add,
    Token::Dash => Arithmetic::Sub,
}

arith_parse! {
    /// Parses expressions such as `expr * expr`, `expr / expr`, or `expr % expr`.
    pub fn arith_mult,
    arith_pow,
    Token::Star => Arithmetic::Mult,
    Token::Slash => Arithmetic::Div,
    Token::Percent => Arithmetic::Modulo,
}

/// Parses expressions such as `expr ** expr`.
pub fn arith_pow<T, I, P>(iter: &mut I, mut arith_unary_op: P) -> Result<P::Output, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    P: Parser<I, Output = Arithmetic<T>, Error = ParseError>,
{
    let expr = arith_unary_op.parse(iter)?;
    combinators::skip_whitespace(iter);

    // We must be extra careful here because ** has a higher precedence
    // than *, meaning power operations will be parsed before multiplication.
    // Thus we should be absolutely certain we should parse a ** operator
    // and avoid confusing it with a multiplication operation that is yet
    // to be parsed.
    let double_star = {
        let mut mp = iter.multipeek();
        let star = Some(&Token::Star);
        mp.peek_next() == star && mp.peek_next() == star
    };

    let ret = if double_star {
        iter.next();
        iter.next();

        let next = arith_pow(iter, arith_unary_op)?;
        Arithmetic::Pow(Box::new(expr), Box::new(next))
    } else {
        expr
    };

    Ok(ret)
}

/// Parses expressions such as `!expr`, `~expr`, `+expr`, `-expr`, `++var` and `--var`.
pub fn arith_unary_op<T, I, PI, PV>(
    iter: &mut I,
    mut arith_post_incr: PI,
    mut arith_var: PV,
) -> Result<Arithmetic<T>, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    PI: Parser<I, Output = Arithmetic<T>, Error = ParseError>,
    PV: Parser<I, Output = T, Error = ParseError>,
{
    combinators::skip_whitespace(iter);
    let expr = eat_maybe!(iter, {
        Token::Bang => {
            let next = arith_unary_op(iter, arith_post_incr, arith_var)?;
            Arithmetic::LogicalNot(Box::new(next))
        },
        Token::Tilde => {
            let next = arith_unary_op(iter, arith_post_incr, arith_var)?;
            Arithmetic::BitwiseNot(Box::new(next))
        },
        Token::Plus => eat_maybe!(iter, {
            // Although we can optimize this out, we'll let the caller handle
            // optimizations, in case it is interested in such redundant situations.
            Token::Dash => {
                let next = arith_unary_op(iter, arith_post_incr, arith_var)?;
                let next = Arithmetic::UnaryMinus(Box::new(next));
                Arithmetic::UnaryPlus(Box::new(next))
            },

            Token::Plus => Arithmetic::PreIncr(arith_var.parse(iter)?);

            _ => {
                let next = arith_unary_op(iter, arith_post_incr, arith_var)?;
                Arithmetic::UnaryPlus(Box::new(next))
            },
        }),

        Token::Dash => eat_maybe!(iter, {
            // Although we can optimize this out, we'll let the AST builder handle
            // optimizations, in case it is interested in such redundant situations.
            Token::Plus => {
                let next = arith_unary_op(iter, arith_post_incr, arith_var)?;
                let next = Arithmetic::UnaryPlus(Box::new(next));
                Arithmetic::UnaryMinus(Box::new(next))
            },

            Token::Dash => Arithmetic::PreDecr(arith_var.parse(iter)?);

            _ => {
                let next = arith_unary_op(iter, arith_post_incr, arith_var)?;
                Arithmetic::UnaryMinus(Box::new(next))
            },
        });

        _ => arith_post_incr.parse(iter)?,
    });

    Ok(expr)
}

/// Parses expressions such as `(expr)`, numeric literals, `var`, `var++`, or `var--`.
/// Numeric literals must appear as a single `Literal` token. `Name` tokens will be
/// treated as variables.
pub fn arith_post_incr<I, PS, PV>(
    iter: &mut I,
    mut arith_subst: PS,
    mut arith_var: PV,
) -> Result<Arithmetic<PV::Output>, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    PS: Parser<I, Output = Arithmetic<PV::Output>, Error = ParseError>,
    PV: Parser<I, Error = ParseError>,
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
