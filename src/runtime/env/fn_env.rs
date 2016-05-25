use runtime::env::{SubEnvironment, shallow_copy};

use std::borrow::Cow;
use std::collections::HashMap;
use std::hash::Hash;

/// An interface for setting and getting shell functions.
pub trait FunctionEnvironment<K, F> {
    /// Get a particularly named function if it was registered.
    fn function(&self, name: &K) -> Option<&F>;
    /// Register a shell function with a given name.
    fn set_function(&mut self, name: K, func: F);

    /// Check if a particularly named function was registered.
    fn has_function(&self, name: &K) -> bool {
        self.function(name).is_some()
    }
}

impl<'a, K, F, E: ?Sized> FunctionEnvironment<K, F> for &'a mut E
    where E: FunctionEnvironment<K, F>
{
    fn function(&self, name: &K) -> Option<&F> {
        (**self).function(name)
    }

    fn set_function(&mut self, name: K, func: F) {
        (**self).set_function(name, func);
    }

    fn has_function(&self, name: &K) -> bool {
        (**self).has_function(name)
    }
}

/// An interface for unsetting shell functions.
pub trait UnsetFunctionEnvironment<K, F>: FunctionEnvironment<K, F> {
    /// Removes the definition of a function if it was registered.
    fn unset_function(&mut self, name: &K);
}

impl<'a, K, F, E: ?Sized> UnsetFunctionEnvironment<K, F> for &'a mut E
    where E: UnsetFunctionEnvironment<K, F>
{
    fn unset_function(&mut self, name: &K) {
        (**self).unset_function(name);
    }
}

/// An `Environment` module for setting and getting shell functions.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnEnv<'a, K, F>
    where K: 'a + Clone + Hash + Eq,
          F: 'a + Clone,
{
    /// A mapping of function names to their definitions.
    functions: Cow<'a, HashMap<K, F>>,
}

impl<'a, K, F> FnEnv<'a, K, F>
    where K: 'a + Clone + Hash + Eq,
          F: 'a + Clone
{
    /// Constructs a new `FnEnv` with no defined functions.
    pub fn new() -> Self {
        FnEnv {
            functions: Cow::Owned(HashMap::new()),
        }
    }
}

impl<'a, K, F> Default for FnEnv<'a, K, F>
    where K: 'a + Clone + Hash + Eq,
          F: 'a + Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, K, F> SubEnvironment<'a> for FnEnv<'a, K, F>
    where K: 'a + Clone + Hash + Eq,
          F: 'a + Clone,
{
    fn sub_env(&'a self) -> Self {
        FnEnv {
            functions: shallow_copy(&self.functions),
        }
    }
}

impl<'a, K, F> FunctionEnvironment<K, F> for FnEnv<'a, K, F>
    where K: 'a + Clone + Hash + Eq,
          F: 'a + Clone,
{
    fn function(&self, name: &K) -> Option<&F> {
        self.functions.get(name)
    }

    fn set_function(&mut self, name: K, func: F) {
        // FIXME: after specialization lands, don't insert if F: Eq and old == new
        self.functions.to_mut().insert(name, func);
    }
}

impl<'a, K, F> UnsetFunctionEnvironment<K, F> for FnEnv<'a, K, F>
    where K: 'a + Clone + Hash + Eq,
          F: 'a + Clone,
{
    fn unset_function(&mut self, name: &K) {
        if self.has_function(name) {
            self.functions.to_mut().remove(name);
        }
    }
}

#[cfg(test)]
mod tests {
    use runtime::env::SubEnvironment;
    use std::borrow::Cow;
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
        if let Cow::Owned(_) = env.functions {
            panic!("needles clone!");
        }
    }
}
