pub mod combinators;

pub trait Parser<I: ?Sized> {
    type Output;
    type Error;

    fn parse(&mut self, cx: &mut I) -> Result<Self::Output, Self::Error>;
}

impl<F, I, O, E> Parser<I> for F
where
    I: ?Sized,
    F: ?Sized + FnMut(&mut I) -> Result<O, E>,
{
    type Output = O;
    type Error = E;

    fn parse(&mut self, cx: &mut I) -> Result<Self::Output, Self::Error> {
        (*self)(cx)
    }
}
