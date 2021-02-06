use crate::ast::Arithmetic;
use crate::error::ParseError;
use crate::iter::{Multipeek, PositionIterator};
use crate::parse2::combinators;
use crate::parse2::{parse_fn, Parser};
use crate::token::Token;
use std::marker::PhantomData;

#[derive(Debug, Copy, PartialEq, Eq)]
pub struct ArithParser<T> {
    phantom: PhantomData<T>,
}

impl<T> Default for ArithParser<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Clone for ArithParser<T> {
    fn clone(&self) -> Self {
        Self::new()
    }
}

impl<T> ArithParser<T> {
    pub fn new() -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

impl<T> ArithParser<T>
where
    T: From<String>,
{
    pub fn arith_assig<I, PS>(iter: &mut I, mut arith_subst: PS) -> Result<PS::Output, ParseError>
    where
        T: Clone,
        I: ?Sized + Multipeek<Item = Token> + PositionIterator,
        PS: Parser<I, Output = Arithmetic<T>, Error = ParseError>,
    {
        combinators::arith_assig(
            iter,
            parse_fn(|iter| {
                combinators::arith_ternary(
                    iter,
                    parse_fn(|iter| {
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
                                                                combinators::arith_eq(
                                                                    iter,
                                                                    parse_fn(|iter| {
                                                                        combinators::arith_ineq(
                                                                            iter,
                                                                            parse_fn(|iter| {
                                                                                combinators::arith_shift(
                                                                                iter,
                                                                                parse_fn(|iter| {
                                                                                    combinators::arith_add(iter, parse_fn(|iter| {
                                                                                    combinators::arith_mult(iter, parse_fn(|iter| {
                                                                                        combinators::arith_pow(
                                                                                            iter,
                                                                                            parse_fn(|iter| {
                                                                                                combinators::arith_unary_op(
                                                                                                    iter,
                                                                                                    parse_fn(|iter| {
                                                                                                        combinators::arith_post_incr(
                                                                                                            iter,
                                                                                                            parse_fn(|iter| {
                                                                                                                arith_subst.parse(iter)
                                                                                                            }),
                                                                                                            parse_fn(Self::arith_var),
                                                                                                        )
                                                                                                    }),
                                                                                                    parse_fn(Self::arith_var),
                                                                                                )
                                                                                            }),
                                                                                        )
                                                                                    }))
                                                                                }))
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
                                    }),
                                )
                            }),
                        )
                    }),
                )
            }),
            parse_fn(Self::arith_var),
        )
    }

    fn arith_var<I>(iter: &mut I) -> Result<T, ParseError>
    where
        I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    {
        combinators::arith_var(iter).map(T::from)
    }
}
