use runtime::env::{SubEnvironment, shallow_copy};

use std::borrow::Cow;
use std::rc::Rc;

/// An interface for getting shell and function arguments.
pub trait ArgumentsEnvironment<T: Clone> {
    /// Get the name of the shell.
    fn name(&self) -> &T;
    /// Get an argument at any index. Arguments are 1-indexed since the shell variable `$0`
    /// refers to the shell's name. Thus the first real argument starts at index 1.
    fn arg(&self, idx: usize) -> Option<&T>;
    /// Get the number of current arguments, NOT including the shell name.
    fn args_len(&self) -> usize;
    /// Get all current arguments as a possibly owned slice.
    fn args(&self) -> Cow<[T]>;
}

impl<'a, T, E: ?Sized> ArgumentsEnvironment<T> for &'a E
    where E: ArgumentsEnvironment<T>,
          T: Clone,
{
    fn name(&self) -> &T {
        (**self).name()
    }

    fn arg(&self, idx: usize) -> Option<&T> {
        (**self).arg(idx)
    }

    fn args_len(&self) -> usize {
        (**self).args_len()
    }

    fn args(&self) -> Cow<[T]> {
        (**self).args()
    }
}

/// An interface for setting shell and function arguments.
pub trait SetArgumentsEnvironment<'a, T: Clone> {
    /// Changes the environment's arguments to `new_args` and returns the old arguments.
    fn set_args<'b: 'a>(&mut self, new_args: Cow<'b, [T]>) -> Cow<'a, [T]>;
}

impl<'e, 'a: 'e, T, E: ?Sized> SetArgumentsEnvironment<'a, T> for &'e mut E
    where E: SetArgumentsEnvironment<'a, T>,
          T: Clone,
{
    fn set_args<'b: 'a>(&mut self, new_args: Cow<'b, [T]>) -> Cow<'a, [T]> {
        (**self).set_args(new_args)
    }
}

/// An `Environment` module for setting and getting shell and function arguments.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ArgsEnv<'a, T = Rc<String>> where T: 'a + Clone {
    /// The name of the shell.
    name: Cow<'a, T>,
    /// The positional arguments of the shell or function.
    args: Cow<'a, [T]>,
}

impl<'a, T: Clone> ArgsEnv<'a, T> {
    /// Constructs a new `ArgsEnv` and initializes it with the name of the
    /// current process as the shell name, and no arguments.
    pub fn new() -> Self where T: From<String> {
        let name = ::std::env::current_exe().ok().and_then(|path| {
            path.file_name().and_then(|os_str| os_str.to_str().map(|s| s.to_owned()))
        }).unwrap_or_default();

        Self::with_name(name.into())
    }

    /// Constructs a new `ArgsEnv` and initializes it with the
    /// provided name and no arguments.
    pub fn with_name(name: T) -> Self {
        ArgsEnv {
            name: Cow::Owned(name),
            args: Cow::Owned(Vec::new()),
        }
    }

    /// Constructs a new `ArgsEnv` and initializes it with the
    /// provided name and positional arguments.
    pub fn with_name_and_args<I: IntoIterator<Item = T>>(name: T, args: I) -> Self {
        ArgsEnv {
            name: Cow::Owned(name),
            args: Cow::Owned(args.into_iter().map(Into::into).collect()),
        }
    }
}

impl<'a, T: Clone + From<String>> Default for ArgsEnv<'a, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: Clone> SubEnvironment<'a> for ArgsEnv<'a, T> {
    fn sub_env(&'a self) -> Self {
        ArgsEnv {
            name: shallow_copy(&self.name),
            args: shallow_copy(&self.args),
        }
    }
}

impl<'a, T: Clone> ArgumentsEnvironment<T> for ArgsEnv<'a, T> {
    fn name(&self) -> &T {
        &self.name
    }

    fn arg(&self, idx: usize) -> Option<&T> {
        if idx == 0 {
            Some(self.name())
        } else {
            self.args.get(idx - 1)
        }
    }

    fn args_len(&self) -> usize {
        self.args.len()
    }

    fn args(&self) -> Cow<[T]> {
        Cow::Borrowed(&self.args)
    }
}

impl<'a, T: Clone> SetArgumentsEnvironment<'a, T> for ArgsEnv<'a, T> {
    fn set_args<'b: 'a>(&mut self, new_args: Cow<'b, [T]>) -> Cow<'a, [T]> {
        ::std::mem::replace(&mut self.args, new_args)
    }
}

#[cfg(test)]
mod tests {
    use runtime::env::SubEnvironment;
    use std::borrow::Cow;
    use super::*;

    #[test]
    fn test_name() {
        let name = "shell";
        let env = ArgsEnv::with_name(name.to_owned());
        assert_eq!(env.name(), name);
        assert_eq!(env.arg(0).unwrap(), name);

        // Name should not change in sub environments
        let env = env.sub_env();
        assert_eq!(env.name(), name);
        assert_eq!(env.arg(0).unwrap(), name);
    }

    #[test]
    fn test_sub_env_no_needless_clone() {
        let name = "shell";
        let args = vec!("one", "two", "three");
        let env = ArgsEnv::with_name_and_args(name, args.clone());

        let env = env.sub_env();
        assert_eq!(env.name, Cow::Borrowed(&name));
        assert_eq!(env.args, Cow::Borrowed(&*args));
    }

    #[test]
    fn test_args() {
        let name = "shell";
        let args = vec!("one", "two", "three");
        let env = ArgsEnv::with_name_and_args(name, args.clone());

        assert_eq!(env.args_len(), args.len());

        assert_eq!(env.arg(0), Some(&name));
        assert_eq!(env.arg(1), Some(&args[0]));
        assert_eq!(env.arg(2), Some(&args[1]));
        assert_eq!(env.arg(3), Some(&args[2]));
        assert_eq!(env.arg(4), None);

        assert_eq!(env.args(), args);
    }

    #[test]
    fn test_set_args() {
        let args_old = vec!("1", "2", "3");
        let mut env = ArgsEnv::with_name_and_args("shell", args_old.clone());

        {
            let args_new = vec!("4", "5", "6");
            assert_eq!(env.args(), args_old);
            let prev = env.set_args(Cow::Owned(args_new.clone()));
            assert_eq!(prev, args_old);
            assert_eq!(env.args(), args_new);

            env.set_args(prev);
        }

        assert_eq!(env.args(), args_old);
    }
}
