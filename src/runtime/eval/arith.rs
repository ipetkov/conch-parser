//! A module that defines evaluating parameters and parameter subsitutions.

use runtime::ExpansionError;
use runtime::env::{StringWrapper, VariableEnvironment};
use syntax::ast::Arithmetic;

impl Arithmetic {
    /// Evaluates an arithmetic expression in the context of an environment.
    /// A mutable reference to the environment is needed since an arithmetic
    /// expression could mutate environment variables.
    pub fn eval<E: ?Sized>(&self, env: &mut E) -> Result<isize, ExpansionError>
        where E: VariableEnvironment,
              E::VarName: StringWrapper,
              E::Var: StringWrapper,
    {
        use syntax::ast::Arithmetic::*;

        let get_var = |env: &E, var| {
            env.var(var)
                .and_then(|s| s.as_str().parse().ok())
                .unwrap_or(0)
        };

        let ret = match *self {
            Literal(lit) => lit,
            Var(ref var) => get_var(env, var),

            PostIncr(ref var) => {
                let value = get_var(env, var);
                env.set_var(var.clone().into(), (value + 1).to_string().into());
                value
            },

            PostDecr(ref var) => {
                let value = get_var(env, var);
                env.set_var(var.clone().into(), (value - 1).to_string().into());
                value
            },

            PreIncr(ref var) => {
                let value = get_var(env, var) + 1;
                env.set_var(var.clone().into(), value.to_string().into());
                value
            },

            PreDecr(ref var) => {
                let value = get_var(env, var) - 1;
                env.set_var(var.clone().into(), value.to_string().into());
                value
            },

            UnaryPlus(ref expr)  => try!(expr.eval(env)).abs(),
            UnaryMinus(ref expr) => -try!(expr.eval(env)),
            BitwiseNot(ref expr) => try!(expr.eval(env)) ^ !0,
            LogicalNot(ref expr) => if try!(expr.eval(env)) == 0 { 1 } else { 0 },

            Less(ref left, ref right)    => if try!(left.eval(env)) <  try!(right.eval(env)) { 1 } else { 0 },
            LessEq(ref left, ref right)  => if try!(left.eval(env)) <= try!(right.eval(env)) { 1 } else { 0 },
            Great(ref left, ref right)   => if try!(left.eval(env)) >  try!(right.eval(env)) { 1 } else { 0 },
            GreatEq(ref left, ref right) => if try!(left.eval(env)) >= try!(right.eval(env)) { 1 } else { 0 },
            Eq(ref left, ref right)      => if try!(left.eval(env)) == try!(right.eval(env)) { 1 } else { 0 },
            NotEq(ref left, ref right)   => if try!(left.eval(env)) != try!(right.eval(env)) { 1 } else { 0 },

            Pow(ref left, ref right) => {
                let right = try!(right.eval(env));
                if right.is_negative() {
                    return Err(ExpansionError::NegativeExponent);
                } else {
                    try!(left.eval(env)).pow(right as u32)
                }
            },

            Div(ref left, ref right) => {
                let right = try!(right.eval(env));
                if right == 0 {
                    return Err(ExpansionError::DivideByZero);
                } else {
                    try!(left.eval(env)) / right
                }
            },

            Modulo(ref left, ref right) => {
                let right = try!(right.eval(env));
                if right == 0 {
                    return Err(ExpansionError::DivideByZero);
                } else {
                    try!(left.eval(env)) % right
                }
            },

            Mult(ref left, ref right)       => try!(left.eval(env)) *  try!(right.eval(env)),
            Add(ref left, ref right)        => try!(left.eval(env)) +  try!(right.eval(env)),
            Sub(ref left, ref right)        => try!(left.eval(env)) -  try!(right.eval(env)),
            ShiftLeft(ref left, ref right)  => try!(left.eval(env)) << try!(right.eval(env)),
            ShiftRight(ref left, ref right) => try!(left.eval(env)) >> try!(right.eval(env)),
            BitwiseAnd(ref left, ref right) => try!(left.eval(env)) &  try!(right.eval(env)),
            BitwiseXor(ref left, ref right) => try!(left.eval(env)) ^  try!(right.eval(env)),
            BitwiseOr(ref left, ref right)  => try!(left.eval(env)) |  try!(right.eval(env)),

            LogicalAnd(ref left, ref right) => if try!(left.eval(env)) != 0 {
                if try!(right.eval(env)) != 0 { 1 } else { 0 }
            } else {
                0
            },

            LogicalOr(ref left, ref right) => if try!(left.eval(env)) == 0 {
                if try!(right.eval(env)) != 0 { 1 } else { 0 }
            } else {
                1
            },

            Ternary(ref guard, ref thn, ref els) => if try!(guard.eval(env)) != 0 {
                try!(thn.eval(env))
            } else {
                try!(els.eval(env))
            },

            Assign(ref var, ref value) => {
                let value = try!(value.eval(env));
                env.set_var(var.clone().into(), value.to_string().into());
                value
            },

            Sequence(ref exprs) => {
                let mut last = 0;
                for e in exprs.iter() {
                    last = try!(e.eval(env));
                }
                last
            },
        };

        Ok(ret)
    }
}

#[cfg(test)]
mod tests {
    use runtime::ExpansionError;
    use runtime::env::{Env, VariableEnvironment};
    use syntax::ast::Arithmetic;

    #[test]
    fn test_eval_arith() {
        use ::std::isize::MAX;
        use syntax::ast::Arithmetic::*;

        fn lit(i: isize) -> Box<Arithmetic> {
            Box::new(Literal(i))
        }

        let mut env = Env::new();
        let env = &mut env;
        let var = "var name".to_owned();
        let var_value = 10;
        let var_string = "var string".to_owned();
        let var_string_value = "asdf";

        env.set_var(var.clone(),        var_value.to_string());
        env.set_var(var_string.clone(), var_string_value.to_owned());

        assert_eq!(Literal(5).eval(env), Ok(5));

        assert_eq!(Var(var.clone()).eval(env), Ok(var_value));
        assert_eq!(Var(var_string.clone()).eval(env), Ok(0));
        assert_eq!(Var("missing var".to_owned()).eval(env), Ok(0));

        assert_eq!(PostIncr(var.clone()).eval(env), Ok(var_value));
        assert_eq!(env.var(&var), Some(&(var_value + 1).to_string()));
        assert_eq!(PostDecr(var.clone()).eval(env), Ok(var_value + 1));
        assert_eq!(env.var(&var), Some(&var_value.to_string()));

        assert_eq!(PreIncr(var.clone()).eval(env), Ok(var_value + 1));
        assert_eq!(env.var(&var), Some(&(var_value + 1).to_string()));
        assert_eq!(PreDecr(var.clone()).eval(env), Ok(var_value));
        assert_eq!(env.var(&var), Some(&var_value.to_string()));

        assert_eq!(UnaryPlus(lit(5)).eval(env), Ok(5));
        assert_eq!(UnaryPlus(lit(-5)).eval(env), Ok(5));

        assert_eq!(UnaryMinus(lit(5)).eval(env), Ok(-5));
        assert_eq!(UnaryMinus(lit(-5)).eval(env), Ok(5));

        assert_eq!(BitwiseNot(lit(5)).eval(env), Ok(!5));
        assert_eq!(BitwiseNot(lit(0)).eval(env), Ok(!0));

        assert_eq!(LogicalNot(lit(5)).eval(env), Ok(0));
        assert_eq!(LogicalNot(lit(0)).eval(env), Ok(1));

        assert_eq!(Less(lit(1), lit(1)).eval(env), Ok(0));
        assert_eq!(Less(lit(1), lit(0)).eval(env), Ok(0));
        assert_eq!(Less(lit(0), lit(1)).eval(env), Ok(1));

        assert_eq!(LessEq(lit(1), lit(1)).eval(env), Ok(1));
        assert_eq!(LessEq(lit(1), lit(0)).eval(env), Ok(0));
        assert_eq!(LessEq(lit(0), lit(1)).eval(env), Ok(1));

        assert_eq!(Great(lit(1), lit(1)).eval(env), Ok(0));
        assert_eq!(Great(lit(1), lit(0)).eval(env), Ok(1));
        assert_eq!(Great(lit(0), lit(1)).eval(env), Ok(0));

        assert_eq!(GreatEq(lit(1), lit(1)).eval(env), Ok(1));
        assert_eq!(GreatEq(lit(1), lit(0)).eval(env), Ok(1));
        assert_eq!(GreatEq(lit(0), lit(1)).eval(env), Ok(0));

        assert_eq!(Eq(lit(0), lit(1)).eval(env), Ok(0));
        assert_eq!(Eq(lit(1), lit(1)).eval(env), Ok(1));

        assert_eq!(NotEq(lit(0), lit(1)).eval(env), Ok(1));
        assert_eq!(NotEq(lit(1), lit(1)).eval(env), Ok(0));

        assert_eq!(Pow(lit(4), lit(3)).eval(env), Ok(64));
        assert_eq!(Pow(lit(4), lit(0)).eval(env), Ok(1));
        assert_eq!(Pow(lit(4), lit(-2)).eval(env), Err(ExpansionError::NegativeExponent));

        assert_eq!(Div(lit(6), lit(2)).eval(env), Ok(3));
        assert_eq!(Div(lit(1), lit(0)).eval(env), Err(ExpansionError::DivideByZero));

        assert_eq!(Modulo(lit(6), lit(5)).eval(env), Ok(1));
        assert_eq!(Modulo(lit(1), lit(0)).eval(env), Err(ExpansionError::DivideByZero));

        assert_eq!(Mult(lit(3), lit(2)).eval(env), Ok(6));
        assert_eq!(Mult(lit(1), lit(0)).eval(env), Ok(0));

        assert_eq!(Add(lit(3), lit(2)).eval(env), Ok(5));
        assert_eq!(Add(lit(1), lit(0)).eval(env), Ok(1));

        assert_eq!(Sub(lit(3), lit(2)).eval(env), Ok(1));
        assert_eq!(Sub(lit(0), lit(1)).eval(env), Ok(-1));

        assert_eq!(ShiftLeft(lit(4), lit(3)).eval(env), Ok(32));

        assert_eq!(ShiftRight(lit(32), lit(2)).eval(env), Ok(8));

        assert_eq!(BitwiseAnd(lit(135), lit(97)).eval(env), Ok(1));
        assert_eq!(BitwiseAnd(lit(135), lit(0)).eval(env), Ok(0));
        assert_eq!(BitwiseAnd(lit(135), lit(MAX)).eval(env), Ok(135));

        assert_eq!(BitwiseXor(lit(135), lit(150)).eval(env), Ok(17));
        assert_eq!(BitwiseXor(lit(135), lit(0)).eval(env), Ok(135));
        assert_eq!(BitwiseXor(lit(135), lit(MAX)).eval(env), Ok(135 ^ MAX));

        assert_eq!(BitwiseOr(lit(135), lit(97)).eval(env), Ok(231));
        assert_eq!(BitwiseOr(lit(135), lit(0)).eval(env), Ok(135));
        assert_eq!(BitwiseOr(lit(135), lit(MAX)).eval(env), Ok(MAX));

        assert_eq!(LogicalAnd(lit(135), lit(97)).eval(env), Ok(1));
        assert_eq!(LogicalAnd(lit(135), lit(0)).eval(env), Ok(0));
        assert_eq!(LogicalAnd(lit(0), lit(0)).eval(env), Ok(0));

        assert_eq!(LogicalOr(lit(135), lit(97)).eval(env), Ok(1));
        assert_eq!(LogicalOr(lit(135), lit(0)).eval(env), Ok(1));
        assert_eq!(LogicalOr(lit(0), lit(0)).eval(env), Ok(0));

        assert_eq!(Ternary(lit(2), lit(4), lit(5)).eval(env), Ok(4));
        assert_eq!(Ternary(lit(0), lit(4), lit(5)).eval(env), Ok(5));

        assert_eq!(env.var(&var), Some(&(var_value).to_string()));
        assert_eq!(Assign(var.clone(), lit(42)).eval(env), Ok(42));
        assert_eq!(env.var(&var).map(|s| &**s), Some("42"));

        assert_eq!(Sequence(vec!(
            Assign("x".to_owned(), lit(5)),
            Assign("y".to_owned(), lit(10)),
            Add(Box::new(PreIncr("x".to_owned())), Box::new(PostDecr("y".to_owned()))),
        )).eval(env), Ok(16));

        assert_eq!(env.var("x").map(|s| &**s), Some("6"));
        assert_eq!(env.var("y").map(|s| &**s), Some("9"));
    }
}
