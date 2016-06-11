use runtime::env::SubEnvironment;
use runtime::ref_counted::RefCounted;

use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Arc;

use syntax::ast::TopLevelCommand;

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

/// A mapping of function names to their definitions.
type Inner<K, F> = HashMap<K, F>;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FnEnvImpl<U> {
    functions: U,
}

impl<K, F, U> FunctionEnvironment<K, F> for FnEnvImpl<U>
    where K: 'static + Clone + Hash + Eq,
          F: Clone,
          U: RefCounted<Inner<K, F>>,
{
    fn function(&self, name: &K) -> Option<&F> {
        self.functions.get(name)
    }

    fn set_function(&mut self, name: K, func: F) {
        // FIXME: after specialization lands, don't insert if F: Eq and old == new
        self.functions.make_mut().insert(name, func);
    }
}

impl<K, F, U> UnsetFunctionEnvironment<K, F> for FnEnvImpl<U>
    where K: 'static + Clone + Hash + Eq,
          F: Clone,
          U: RefCounted<Inner<K, F>>,
{
    fn unset_function(&mut self, name: &K) {
        if self.has_function(name) {
            self.functions.make_mut().remove(name);
        }
    }
}

/// An `Environment` module for setting and getting shell functions.
///
/// Uses `Rc` internally. For a possible `Send` and `Sync` implementation,
/// see `AtomicFnEnv`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnEnv<K = Rc<String>, F = Rc<TopLevelCommand>>(FnEnvImpl<Rc<Inner<K, F>>>)
    where K: Clone + Hash + Eq,
          F: Clone;

/// An `Environment` module for setting and getting shell functions.
///
/// Uses `Arc` internally. If `Send` and `Sync` is not required of the implementation,
/// see `FnEnv` as a cheaper alternative.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicFnEnv<K = Arc<String>, F = Arc<TopLevelCommand>>(FnEnvImpl<Arc<Inner<K, F>>>)
    where K: Clone + Hash + Eq,
          F: Clone;

macro_rules! impl_methods {
    ($_Self:expr) => {
        /// Constructs a new `FnEnv` with no defined functions.
        pub fn new() -> Self {
            $_Self(FnEnvImpl {
                functions: HashMap::new().into(),
            })
        }
    }
}

impl<K, F> FnEnv<K, F>
    where K: Clone + Hash + Eq,
          F: Clone
{
    impl_methods!(FnEnv);
}

impl<K, F> AtomicFnEnv<K, F>
    where K: Clone + Hash + Eq,
          F: Clone
{
    impl_methods!(AtomicFnEnv);
}

impl<K, F> Default for FnEnv<K, F>
    where K: Clone + Hash + Eq,
          F: Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, F> Default for AtomicFnEnv<K, F>
    where K: Clone + Hash + Eq,
          F: Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, F> SubEnvironment for FnEnv<K, F>
    where K: Clone + Hash + Eq,
          F: Clone,
{
    fn sub_env(&self) -> Self {
        self.clone()
    }
}

impl<K, F> SubEnvironment for AtomicFnEnv<K, F>
    where K: Clone + Hash + Eq,
          F: Clone,
{
    fn sub_env(&self) -> Self {
        self.clone()
    }
}

macro_rules! impl_function_environment_trait {
    () => {
        fn function(&self, name: &K) -> Option<&F> {
            self.0.function(name)
        }

        fn set_function(&mut self, name: K, func: F) {
            self.0.set_function(name, func)
        }
    }
}

macro_rules! impl_unset_function_environment_trait {
    () => {
        fn unset_function(&mut self, name: &K) {
            self.0.unset_function(name)
        }
    }
}

impl<K, F> FunctionEnvironment<K, F> for FnEnv<K, F>
    where K: 'static + Clone + Hash + Eq,
          F: Clone,
{
    impl_function_environment_trait!();
}

impl<K, F> UnsetFunctionEnvironment<K, F> for FnEnv<K, F>
    where K: 'static + Clone + Hash + Eq,
          F: Clone,
{
    impl_unset_function_environment_trait!();
}

impl<K, F> FunctionEnvironment<K, F> for AtomicFnEnv<K, F>
    where K: 'static + Clone + Hash + Eq,
          F: Clone,
{
    impl_function_environment_trait!();
}

impl<K, F> UnsetFunctionEnvironment<K, F> for AtomicFnEnv<K, F>
    where K: 'static + Clone + Hash + Eq,
          F: Clone,
{
    impl_unset_function_environment_trait!();
}

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
        if let Some(_) = env.0.functions.get_mut() {
            panic!("needles clone!");
        }
    }
}
