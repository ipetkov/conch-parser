use crate::ast::Arithmetic;
use crate::error::ParseError;
use crate::iter::{MultipeekIterator, PositionIterator};
use crate::parse2::{combinators, parse_fn, Parser};
use crate::token::Token;

/// A default implementation for parsing arithmetic substitutions.
///
/// The caller is responsible for parsing the external `$(( ))` tokens.
pub fn arith_subst<T, I>(iter: &mut I) -> Result<Arithmetic<T>, ParseError>
where
    T: From<String> + Clone,
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
{
    let arith_logical_or: &mut dyn Parser<_, Output = _, Error = _> =
        &mut parse_fn(arith_logical_or);

    combinators::arith_subst(
        iter,
        parse_fn(|iter| {
            combinators::arith_assig(
                iter,
                parse_fn(|iter| combinators::arith_ternary(iter, arith_logical_or)),
                parse_fn(arith_var),
            )
        }),
    )
}

fn arith_logical_or<T, I>(iter: &mut I) -> Result<Arithmetic<T>, ParseError>
where
    T: From<String> + Clone,
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
{
    combinators::arith_logical_or(
        iter,
        parse_fn(|iter| {
            combinators::arith_logical_and(
                iter,
                parse_fn(|iter| {
                    combinators::arith_bitwise_or(
                        iter,
                        parse_fn(|iter| {
                            combinators::arith_bitwise_xor(
                                iter,
                                parse_fn(|iter| {
                                    combinators::arith_bitwise_and(
                                        iter,
                                        parse_fn(|iter| {
                                            combinators::arith_eq(iter, parse_fn(arith_eq))
                                        }),
                                    )
                                }),
                            )
                        }),
                    )
                }),
            )
        }),
    )
}

fn arith_eq<T, I>(iter: &mut I) -> Result<Arithmetic<T>, ParseError>
where
    T: From<String> + Clone,
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
{
    combinators::arith_eq(
        iter,
        parse_fn(|iter| {
            combinators::arith_ineq(
                iter,
                parse_fn(|iter| {
                    combinators::arith_shift(
                        iter,
                        parse_fn(|iter| {
                            combinators::arith_add(
                                iter,
                                parse_fn(|iter| {
                                    combinators::arith_mult(
                                        iter,
                                        parse_fn(|iter| {
                                            combinators::arith_pow(
                                                iter,
                                                parse_fn(|iter| {
                                                    combinators::arith_unary_op(
                                                        iter,
                                                        parse_fn(|iter| {
                                                            combinators::arith_post_incr(
                                                                iter,
                                                                parse_fn(arith_subst),
                                                                parse_fn(arith_var),
                                                            )
                                                        }),
                                                        parse_fn(arith_var),
                                                    )
                                                }),
                                            )
                                        }),
                                    )
                                }),
                            )
                        }),
                    )
                }),
            )
        }),
    )
}

fn arith_var<T, I>(iter: &mut I) -> Result<T, ParseError>
where
    T: From<String>,
    I: ?Sized + MultipeekIterator<Item = Token> + PositionIterator,
{
    combinators::arith_var(iter).map(T::from)
}
