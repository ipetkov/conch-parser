use runtime::env::SubEnvironment;
use runtime::ref_counted::RefCounted;

use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Arc;

use syntax::ast::TopLevelCommand;

/// An interface for setting and getting shell functions.
pub trait FunctionEnvironment {
    /// The name to be associated with a function.
    type Name;
    /// The type of the function.
    type Fn;

    /// Get a particularly named function if it was registered.
    fn function(&self, name: &Self::Name) -> Option<&Self::Fn>;
    /// Register a shell function with a given name.
    fn set_function(&mut self, name: Self::Name, func: Self::Fn);

    /// Check if a particularly named function was registered.
    fn has_function(&self, name: &Self::Name) -> bool {
        self.function(name).is_some()
    }
}

impl<'a, T: ?Sized + FunctionEnvironment> FunctionEnvironment for &'a mut T {
    type Name = T::Name;
    type Fn = T::Fn;

    fn function(&self, name: &Self::Name) -> Option<&Self::Fn> {
        (**self).function(name)
    }

    fn set_function(&mut self, name: Self::Name, func: Self::Fn) {
        (**self).set_function(name, func);
    }

    fn has_function(&self, name: &Self::Name) -> bool {
        (**self).has_function(name)
    }
}

/// An interface for unsetting shell functions.
pub trait UnsetFunctionEnvironment: FunctionEnvironment {
    /// Removes the definition of a function if it was registered.
    fn unset_function(&mut self, name: &Self::Name);
}

impl<'a, T: ?Sized + UnsetFunctionEnvironment> UnsetFunctionEnvironment for &'a mut T {
    fn unset_function(&mut self, name: &Self::Name) {
        (**self).unset_function(name);
    }
}

macro_rules! impl_env {
    ($(#[$attr:meta])* pub struct $Env:ident, $Rc:ident) => {
        $(#[$attr])*
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct $Env<N = $Rc<String>, F = $Rc<TopLevelCommand>>
            where N: Hash + Eq,
        {
            functions: $Rc<HashMap<N, F>>,
        }

        impl<N: Hash + Eq, F> $Env<N, F> {
            /// Constructs a new `FnEnv` with no defined functions.
            pub fn new() -> Self {
                $Env {
                    functions: HashMap::new().into(),
                }
            }
        }

        impl<N: Hash + Eq, F> Default for $Env<N, F> {
            fn default() -> Self {
                Self::new()
            }
        }

        impl<N: Hash + Eq + Clone, F: Clone> SubEnvironment for $Env<N, F> {
            fn sub_env(&self) -> Self {
                self.clone()
            }
        }

        impl<N, F> FunctionEnvironment for $Env<N, F>
            where N: Clone + Hash + Eq,
                  F: Clone,
        {
            type Name = N;
            type Fn = F;

            fn function(&self, name: &Self::Name) -> Option<&Self::Fn> {
                self.functions.get(name)
            }

            fn set_function(&mut self, name: Self::Name, func: Self::Fn) {
                // FIXME: after specialization lands, don't insert if F: Eq and old == new
                self.functions.make_mut().insert(name, func);
            }
        }

        impl<N, F> UnsetFunctionEnvironment for $Env<N, F>
            where N: Clone + Hash + Eq,
                  F: Clone,
        {
            fn unset_function(&mut self, name: &Self::Name) {
                if self.has_function(name) {
                    self.functions.make_mut().remove(name);
                }
            }
        }
    };
}

impl_env!(
    /// An `Environment` module for setting and getting shell functions.
    ///
    /// Uses `Rc` internally. For a possible `Send` and `Sync` implementation,
    /// see `AtomicFnEnv`.
    pub struct FnEnv,
    Rc
);

impl_env!(
    /// An `Environment` module for setting and getting shell functions.
    ///
    /// Uses `Arc` internally. If `Send` and `Sync` is not required of the implementation,
    /// see `FnEnv` as a cheaper alternative.
    pub struct AtomicFnEnv,
    Arc
);

#[cfg(test)]
mod tests {
    use runtime::env::SubEnvironment;
    use runtime::ref_counted::RefCounted;
    use super::*;

    #[test]
    fn test_set_get_unset_function() {
        let name = "var";
        let func = "some func";
        let mut env = FnEnv::new();
        assert_eq!(env.function(&name), None);
        env.set_function(name, func);
        assert_eq!(env.function(&name), Some(&func));
        env.unset_function(&name);
        assert_eq!(env.function(&name), None);
    }

    #[test]
    fn test_sub_env_no_needless_clone() {
        let not_set = "not set";
        let name = "var";
        let func = "some function";
        let mut env = FnEnv::new();
        env.set_function(name, func);

        let mut env = env.sub_env();

        env.unset_function(&not_set);
        if let Some(_) = env.functions.get_mut() {
            panic!("needles clone!");
        }
    }

    #[test]
    fn test_set_function_in_parent_visible_in_child() {
        let fn_name = "foo";
        let func = 42;
        let mut parent = FnEnv::new();
        parent.set_function(fn_name, func);

        {
            let child = parent.sub_env();
            assert_eq!(child.has_function(&fn_name), true);
            assert_eq!(child.function(&fn_name), Some(&func));
        }
    }

    #[test]
    fn test_set_and_unset_function_in_child_should_not_affect_parent() {
        let fn_name_parent = "parent fn";
        let fn_name_child = "child fn";

        let fn_parent = 42;
        let fn_child = 5;

        let mut parent = FnEnv::new();
        parent.set_function(fn_name_parent, fn_parent);

        {
            let mut child = parent.sub_env();
            child.set_function(fn_name_parent, fn_child);
            child.set_function(fn_name_child, fn_child);

            assert_eq!(child.has_function(&fn_name_parent), true);
            assert_eq!(child.has_function(&fn_name_child), true);
            assert_eq!(child.function(&fn_name_parent), Some(&fn_child));
            assert_eq!(child.function(&fn_name_child), Some(&fn_child));
        }

        assert_eq!(parent.has_function(&fn_name_parent), true);
        assert_eq!(parent.has_function(&fn_name_child), false);
        assert_eq!(parent.function(&fn_name_parent), Some(&fn_parent));
        assert_eq!(parent.function(&fn_name_child), None);
    }
}
