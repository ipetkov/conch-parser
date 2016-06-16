use runtime::env::SubEnvironment;

use std::borrow::Cow;
use std::rc::Rc;
use std::sync::Arc;

/// An interface for getting shell and function arguments.
pub trait ArgumentsEnvironment {
    /// The type of arguments this environment holds.
    type Arg: Clone;

    /// Get the name of the shell.
    fn name(&self) -> &Self::Arg;
    /// Get an argument at any index. Arguments are 1-indexed since the shell variable `$0`
    /// refers to the shell's name. Thus the first real argument starts at index 1.
    fn arg(&self, idx: usize) -> Option<&Self::Arg>;
    /// Get the number of current arguments, NOT including the shell name.
    fn args_len(&self) -> usize;
    /// Get all current arguments as a possibly owned slice.
    fn args(&self) -> Cow<[Self::Arg]>;
}

impl<'a, T: ?Sized + ArgumentsEnvironment> ArgumentsEnvironment for &'a T {
    type Arg = T::Arg;

    fn name(&self) -> &Self::Arg {
        (**self).name()
    }

    fn arg(&self, idx: usize) -> Option<&Self::Arg> {
        (**self).arg(idx)
    }

    fn args_len(&self) -> usize {
        (**self).args_len()
    }

    fn args(&self) -> Cow<[Self::Arg]> {
        (**self).args()
    }
}

/// An interface for setting shell and function arguments.
pub trait SetArgumentsEnvironment {
    /// A collection of arguments to set.
    type Args;
    /// Changes the environment's arguments to `new_args` and returns the old arguments.
    fn set_args(&mut self, new_args: Self::Args) -> Self::Args;
}

impl<'a, T: ?Sized + SetArgumentsEnvironment> SetArgumentsEnvironment for &'a mut T {
    type Args = T::Args;

    fn set_args(&mut self, new_args: Self::Args) -> Self::Args {
        (**self).set_args(new_args)
    }
}

macro_rules! impl_env {
    ($(#[$attr:meta])* pub struct $Env:ident, $Rc:ident) => {
        $(#[$attr])*
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct $Env<T: Clone = $Rc<String>> {
            name: $Rc<T>,
            args: $Rc<Vec<T>>,
        }

        impl<T: Clone> $Env<T> {
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
                $Env {
                    name: name.into(),
                    args: Vec::new().into(),
                }
            }

            /// Constructs a new environment and initializes it with the
            /// provided name and positional arguments.
            pub fn with_name_and_args<I: IntoIterator<Item = T>>(name: T, args: I) -> Self {
                $Env {
                    name: name.into(),
                    args: args.into_iter().map(Into::into).collect::<Vec<_>>().into(),
                }
            }
        }

        impl<T: Clone + From<String>> Default for $Env<T> {
            fn default() -> Self {
                Self::new()
            }
        }

        impl<T: Clone> SubEnvironment for $Env<T> {
            fn sub_env(&self) -> Self {
                self.clone()
            }
        }

        impl<T: Clone> ArgumentsEnvironment for $Env<T>
        {
            type Arg = T;

            fn name(&self) -> &Self::Arg {
                &self.name
            }

            fn arg(&self, idx: usize) -> Option<&Self::Arg> {
                if idx == 0 {
                    Some(self.name())
                } else {
                    self.args.get(idx - 1)
                }
            }

            fn args_len(&self) -> usize {
                self.args.len()
            }

            fn args(&self) -> Cow<[Self::Arg]> {
                Cow::Borrowed(&self.args)
            }
        }

        impl<T: Clone> SetArgumentsEnvironment for $Env<T>
        {
            type Args = $Rc<Vec<T>>;

            fn set_args(&mut self, new_args: Self::Args) -> Self::Args {
                ::std::mem::replace(&mut self.args, new_args)
            }
        }
    };
}

impl_env!(
    /// An `Environment` module for setting and getting shell and function arguments.
    ///
    /// Uses `Rc` internally. For a possible `Send` and `Sync` implementation,
    /// see `AtomicArgsEnv`.
    pub struct ArgsEnv,
    Rc
);

impl_env!(
    /// An `Environment` module for setting and getting shell and function arguments.
    ///
    /// Uses `Arc` internally. If `Send` and `Sync` is not required of the implementation,
    /// see `ArgsEnv` as a cheaper alternative.
    pub struct AtomicArgsEnv,
    Arc
);

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
        assert!(env.name.get_mut().is_none());
        assert!(env.args.get_mut().is_none());
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
