use crate::ast::Arithmetic;
use crate::error::ParseError;
use crate::iter::{Multipeek, PositionIterator};
use crate::parse2::combinators;
use crate::parse2::Parser;
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
    pub fn arith_add<I, PS>(iter: &mut I, mut arith_subst: PS) -> Result<PS::Output, ParseError>
    where
        I: ?Sized + Multipeek<Item = Token> + PositionIterator,
        PS: Parser<I, Output = Arithmetic<T>, Error = ParseError>,
    {
        combinators::arith_add(iter, |iter: &'_ mut _| {
            combinators::arith_mult(iter, |iter: &'_ mut _| {
                combinators::arith_pow(iter, |iter: &'_ mut _| {
                    combinators::arith_unary_op(
                        iter,
                        |iter: &'_ mut _| {
                            combinators::arith_post_incr(
                                iter,
                                |iter: &'_ mut _| arith_subst.parse(iter),
                                Self::arith_var,
                            )
                        },
                        Self::arith_var,
                    )
                })
            })
        })
    }


    fn arith_var<I>(iter: &mut I) -> Result<T, ParseError>
    where
        I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    {
        combinators::arith_var(iter).map(T::from)
    }
}
