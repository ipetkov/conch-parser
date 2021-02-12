mod arith;

pub mod combinators;

pub use self::arith::arith_subst;

pub trait Parser<I: ?Sized> {
    type Output;
    type Error;

    fn parse(&mut self, cx: &mut I) -> Result<Self::Output, Self::Error>;
}

impl<I, P> Parser<I> for &'_ mut P
where
    I: ?Sized,
    P: ?Sized + Parser<I>,
{
    type Output = P::Output;
    type Error = P::Error;

    fn parse(&mut self, cx: &mut I) -> Result<Self::Output, Self::Error> {
        (**self).parse(cx)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseFn<F> {
    f: F,
}

impl<F, I, O, E> Parser<I> for ParseFn<F>
where
    I: ?Sized,
    F: FnMut(&mut I) -> Result<O, E>,
{
    type Output = O;
    type Error = E;

    fn parse(&mut self, cx: &mut I) -> Result<Self::Output, Self::Error> {
        (self.f)(cx)
    }
}

pub fn parse_fn<I, F, O, E>(f: F) -> ParseFn<F>
where
    I: ?Sized,
    F: FnMut(&mut I) -> Result<O, E>,
{
    ParseFn { f }
}
