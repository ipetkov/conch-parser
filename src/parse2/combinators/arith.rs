use crate::ast::Arithmetic;
use crate::error::ParseError;
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse2::{combinators, Parser};
use crate::token::Token;

/// Parses the body of any arbitrary arithmetic expression, or a comma delimited
/// sequence of expressions. The caller is responsible for parsing the external
/// `$(( ))` tokens.
pub fn arith_subst<T, I, P>(iter: &mut I, mut arith_assig: P) -> Result<P::Output, ParseError>
where
    T: Clone,
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
    P: Parser<I, Output = Arithmetic<T>, Error = ParseError>,
{
    let first = arith_assig.parse(iter)?;
    combinators::skip_whitespace(iter);

    eat_maybe!(iter, {
        Token::Comma => {};
        _ => return Ok(first),
    });

    let mut exprs = Vec::new();
    exprs.push(first);

    loop {
        exprs.push(arith_assig.parse(iter)?);

        combinators::skip_whitespace(iter);
        eat_maybe!(iter, {
            Token::Comma => {};
            _ => break,
        });
    }

    Ok(Arithmetic::Sequence(exprs))
}

/// Parses expressions such as `var = expr` or `var op= expr`, where `op` is
/// any of the following operators: *, /, %, +, -, <<, >>, &, |, ^.
pub fn arith_assig<T, I, PT, PV>(
    iter: &mut I,
    mut arith_ternary: PT,
    mut arith_var: PV,
) -> Result<PT::Output, ParseError>
where
    T: Clone,
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
    PT: Parser<I, Output = Arithmetic<T>, Error = ParseError>,
    PV: Parser<I, Output = T, Error = ParseError>,
{
    combinators::skip_whitespace(iter);

    let mut is_assig = || {
        let mut mp = iter.multipeek();
        match mp.peek_next() {
            Some(Token::Name(_)) => {}
            Some(Token::Dollar) => match mp.peek_next() {
                Some(Token::Name(_)) => {}
                _ => return false,
            },
            _ => return false,
        };

        // If we got this far it looks like we have an expression
        // starting with a variable. Next we'll skip past any
        // whitespace and look for an operator. If we don't find an
        // expected operator, then it cannot be an assignment expression.
        loop {
            match mp.peek_next() {
                // Skip past whitespace
                Some(Token::Whitespace(_)) => continue,
                Some(Token::Backslash) => match mp.peek_next() {
                    Some(Token::Newline) => continue,
                    _ => return false,
                },

                // Recognize a `var =` asignment so long as we don't find `var ==`
                Some(Token::Equals) => return Some(&Token::Equals) != mp.peek_next(),

                Some(Token::Star) | Some(Token::Slash) | Some(Token::Percent)
                | Some(Token::Plus) | Some(Token::Dash) | Some(Token::DLess)
                | Some(Token::DGreat) | Some(Token::Amp) | Some(Token::Pipe)
                | Some(Token::Caret) => return Some(&Token::Equals) == mp.peek_next(),

                _ => return false,
            }
        }
    };

    if !is_assig() {
        return arith_ternary.parse(iter);
    }

    let var = arith_var.parse(iter)?;
    combinators::skip_whitespace(iter);

    let expr = eat_maybe!(iter, {
        Token::Equals => arith_assig(iter, arith_ternary, arith_var)?;
        _ => {
            let op = eat!(iter, {
                Token::Star    => Arithmetic::Mult,
                Token::Slash   => Arithmetic::Div,
                Token::Percent => Arithmetic::Modulo,
                Token::Plus    => Arithmetic::Add,
                Token::Dash    => Arithmetic::Sub,
                Token::DLess   => Arithmetic::ShiftLeft,
                Token::DGreat  => Arithmetic::ShiftRight,
                Token::Amp     => Arithmetic::BitwiseAnd,
                Token::Pipe    => Arithmetic::BitwiseOr,
                Token::Caret   => Arithmetic::BitwiseXor,
            });

            eat!(iter, {
                Token::Equals => {},
            });

            let value = Box::new(arith_assig(iter, arith_ternary, arith_var)?);
            let var = Box::new(Arithmetic::Var(var.clone()));

            (op)(var, value)
        },
    });

    Ok(Arithmetic::Assign(var, Box::new(expr)))
}

/// Parses expressions such as `expr ? expr : expr`.
pub fn arith_ternary<T, I>(
    iter: &mut I,
    // NB: need a trait object here to avoid recursively monomorphizing this
    // function with an infinite series of reference types...
    arith_logical_or: &mut dyn Parser<I, Output = Arithmetic<T>, Error = ParseError>,
) -> Result<Arithmetic<T>, ParseError>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
{
    let guard = arith_logical_or.parse(iter)?;
    combinators::skip_whitespace(iter);

    let ret = eat_maybe!(iter, {
        Token::Question => {
            let body = arith_ternary(iter, arith_logical_or)?;
            combinators::skip_whitespace(iter);
            eat!(iter, { Token::Colon => {}, });
            let els = arith_ternary(iter, arith_logical_or)?;
            Arithmetic::Ternary(Box::new(guard), Box::new(body), Box::new(els))
        };
        _ => guard,
    });

    Ok(ret)
}

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
            I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
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

arith_parse!(
    /// Parses expressions such as `expr || expr`.
    pub fn arith_logical_or,
    arith_logical_and,
    Token::OrIf => Arithmetic::LogicalOr,
);

arith_parse!(
    /// Parses expressions such as `expr && expr`.
    pub fn arith_logical_and,
    arith_bitwise_or,
    Token::AndIf => Arithmetic::LogicalAnd,
);

arith_parse!(
    /// Parses expressions such as `expr | expr`.
    pub fn arith_bitwise_or,
    arith_bitwise_xor,
    Token::Pipe => Arithmetic::BitwiseOr,
);

arith_parse!(
    /// Parses expressions such as `expr ^ expr`.
    pub fn arith_bitwise_xor,
    arith_bitwise_and,
    Token::Caret => Arithmetic::BitwiseXor,
);

arith_parse!(
    /// Parses expressions such as `expr & expr`.
    pub fn arith_bitwise_and,
    arith_eq,
    Token::Amp => Arithmetic::BitwiseAnd,
);

/// Parses expressions such as `expr == expr` or `expr != expr`.
pub fn arith_eq<T, I, P>(iter: &mut I, mut arith_ineq: P) -> Result<P::Output, ParseError>
where
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
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
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
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
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
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
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
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
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
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
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
{
    combinators::skip_whitespace(iter);
    eat_maybe!(iter, {
        Token::Dollar => {},
    });
    eat!(iter, {
        Token::Name(n) => Ok(n),
    })
}
