use runtime::env::SubEnvironment;
use runtime::ref_counted::RefCounted;

use std::borrow::Cow;
use std::rc::Rc;
use std::sync::Arc;

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
pub trait SetArgumentsEnvironment<T: Clone> {
    type Args;
    /// Changes the environment's arguments to `new_args` and returns the old arguments.
    fn set_args(&mut self, new_args: Self::Args) -> Self::Args;
}

impl<'a, T, E: ?Sized> SetArgumentsEnvironment<T> for &'a mut E
    where T: Clone,
          E: SetArgumentsEnvironment<T>,
{
    type Args = E::Args;

    fn set_args(&mut self, new_args: Self::Args) -> Self::Args {
        (**self).set_args(new_args)
    }
}

type Inner<T> = Vec<T>;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ArgsEnvImpl<T, U> {
    /// The name of the shell.
    name: T,
    /// The positional arguments of the shell or function.
    args: U,
}

impl<T, U> ArgumentsEnvironment<T> for ArgsEnvImpl<T, U>
    where T: Clone,
          U: RefCounted<Inner<T>>,
{
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

impl<T, U> SetArgumentsEnvironment<T> for ArgsEnvImpl<T, U>
    where T: Clone,
          U: RefCounted<Inner<T>>,
{
    type Args = U;

    fn set_args(&mut self, new_args: Self::Args) -> Self::Args {
        ::std::mem::replace(&mut self.args, new_args)
    }
}

/// An `Environment` module for setting and getting shell and function arguments.
///
/// Uses `Rc` internally. For a possible `Send` and `Sync` implementation,
/// see `AtomicArgsEnv`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgsEnv<T: Clone = Rc<String>>(ArgsEnvImpl<T, Rc<Inner<T>>>);

/// An `Environment` module for setting and getting shell and function arguments.
///
/// Uses `Arc` internally. If `Send` and `Sync` is not required of the implementation,
/// see `ArgsEnv` as a cheaper alternative.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicArgsEnv<T: Clone = Arc<String>>(ArgsEnvImpl<T, Arc<Inner<T>>>);

macro_rules! impl_methods {
    ($_Self:expr) => {
        /// Constructs a new environment and initializes it with the name of the
        /// current process as the shell name, and no arguments.
        pub fn new() -> Self where T: From<String> {
            let name = ::std::env::current_exe().ok().and_then(|path| {
                path.file_name().and_then(|os_str| os_str.to_str().map(|s| s.to_owned()))
            }).unwrap_or_default();

            Self::with_name(name.into())
        }

        /// Constructs a new environment and initializes it with the
        /// provided name and no arguments.
        pub fn with_name(name: T) -> Self {
            $_Self(ArgsEnvImpl {
                name: name.into(),
                args: Vec::new().into(),
            })
        }

        /// Constructs a new environment and initializes it with the
        /// provided name and positional arguments.
        pub fn with_name_and_args<I: IntoIterator<Item = T>>(name: T, args: I) -> Self {
            $_Self(ArgsEnvImpl {
                name: name.into(),
                args: args.into_iter().map(Into::into).collect::<Vec<_>>().into(),
            })
        }
    }
}

impl<T: Clone> ArgsEnv<T> {
    impl_methods!(ArgsEnv);
}

impl<T: Clone> AtomicArgsEnv<T> {
    impl_methods!(AtomicArgsEnv);
}

impl<T: Clone + From<String>> Default for ArgsEnv<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + From<String>> Default for AtomicArgsEnv<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> SubEnvironment for ArgsEnv<T> {
    fn sub_env(&self) -> Self {
        self.clone()
    }
}

impl<T: Clone> SubEnvironment for AtomicArgsEnv<T> {
    fn sub_env(&self) -> Self {
        self.clone()
    }
}

macro_rules! impl_arguments_environment_trait {
    () => {
        fn name(&self) -> &T {
            self.0.name()
        }

        fn arg(&self, idx: usize) -> Option<&T> {
            self.0.arg(idx)
        }

        fn args_len(&self) -> usize {
            self.0.args_len()
        }

        fn args(&self) -> Cow<[T]> {
            self.0.args()
        }
    };
}

macro_rules! impl_set_arguments_environment_trait {
    ($Args:ty) => {
        type Args = $Args;
        fn set_args(&mut self, new_args: Self::Args) -> Self::Args {
            self.0.set_args(new_args)
        }
    };
}

impl<T: Clone + Eq> ArgumentsEnvironment<T> for ArgsEnv<T> {
    impl_arguments_environment_trait!();
}

impl<T: Clone> SetArgumentsEnvironment<T> for ArgsEnv<T> {
    impl_set_arguments_environment_trait!(Rc<Vec<T>>);
}

impl<T: Clone + Eq> ArgumentsEnvironment<T> for AtomicArgsEnv<T> {
    impl_arguments_environment_trait!();
}

impl<T: Clone> SetArgumentsEnvironment<T> for AtomicArgsEnv<T> {
    impl_set_arguments_environment_trait!(Arc<Vec<T>>);
}

#[cfg(test)]
mod tests {
    use runtime::env::SubEnvironment;
    use runtime::ref_counted::RefCounted;
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
        let name = ::std::rc::Rc::new("shell");
        let args = vec!("one".into(), "two".into(), "three".into());
        let env = ArgsEnv::with_name_and_args(name, args.clone());

        let mut env = env.sub_env();
        assert!(env.0.name.get_mut().is_none());
        assert!(env.0.args.get_mut().is_none());
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
            let prev = env.set_args(args_new.clone().into());
            assert_eq!(*prev, args_old);
            assert_eq!(env.args(), args_new);

            env.set_args(prev);
        }

        assert_eq!(env.args(), args_old);
    }
}
