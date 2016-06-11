use runtime::env::SubEnvironment;
use runtime::ref_counted::RefCounted;

use std::borrow::Cow;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

/// An interface for setting and getting shell and environment variables.
pub trait VariableEnvironment<T: ?Sized> {
    /// Get the value of some variable. The values of both shell-only
    /// and environment variables will be looked up and returned.
    fn var(&self, name: &str) -> Option<&T>;
    /// Set the value of some variable, maintaining its status as an
    /// environment variable if previously set as such.
    fn set_var(&mut self, name: String, val: T);
    /// Unset the value of some variable (including environment variables).
    /// Get all current pairs of environment variables and their values.
    fn env_vars(&self) -> Cow<[(&str, &T)]>;
}

impl<'a, T, E: ?Sized> VariableEnvironment<T> for &'a mut E
    where E: VariableEnvironment<T>
{
    fn var(&self, name: &str) -> Option<&T> {
        (**self).var(name)
    }

    fn set_var(&mut self, name: String, val: T) {
        (**self).set_var(name, val);
    }

    fn env_vars(&self) -> Cow<[(&str, &T)]> {
        (**self).env_vars()
    }
}

/// An interface for unsetting shell and envrironment variables.
pub trait UnsetVariableEnvironment<T: ?Sized> {
    /// Unset the value of some variable (including environment variables).
    fn unset_var(&mut self, name: &str);
}

impl<'a, T, E: ?Sized> UnsetVariableEnvironment<T> for &'a mut E
    where E: UnsetVariableEnvironment<T>
{
    fn unset_var(&mut self, name: &str) {
        (**self).unset_var(name);
    }
}

/// A mapping of variable names to their values.
///
/// The tupled boolean indicates if a variable should be exported to other commands.
type Inner<T> = HashMap<String, (T, bool)>;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct VarEnvImpl<U> {
    vars: U,
}

impl<T, U> VariableEnvironment<T> for VarEnvImpl<U>
    where T: Clone + Eq, // FIXME: might not need to be clone?
          U: RefCounted<Inner<T>>,
{
    fn var(&self, name: &str) -> Option<&T> {
        self.vars.get(name).map(|&(ref val, _)| val)
    }

    fn set_var(&mut self, name: String, val: T) {
        let (needs_insert, exported) = match self.vars.get(&name) {
            Some(&(ref existing_val, exported)) => (&val != existing_val, exported),
            None => (true, false),
        };

        if needs_insert {
            self.vars.make_mut().insert(name, (val, exported));
        }
    }

    fn env_vars(&self) -> Cow<[(&str, &T)]> {
        let ret: Vec<_> = self.vars.iter()
            .filter_map(|(k, &(ref v, exported))| if exported {
                Some((&**k, v))
            } else {
                None
            })
            .collect();

        Cow::Owned(ret)
    }
}

impl<T, U> UnsetVariableEnvironment<T> for VarEnvImpl<U>
    where T: Clone + Eq,
          U: RefCounted<Inner<T>>,
{
    fn unset_var(&mut self, name: &str) {
        if self.vars.contains_key(name) {
            self.vars.make_mut().remove(name);
        }
    }
}

/// An `Environment` module for setting and getting shell variables.
///
/// Uses `Rc` internally. For a possible `Send` and `Sync` implementation,
/// see `AtomicVarEnv`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VarEnv<T: Clone = Rc<String>>(VarEnvImpl<Rc<Inner<T>>>);

/// An `Environment` module for setting and getting shell variables.
///
/// Uses `Arc` internally. If `Send` and `Sync` is not required of the implementation,
/// see `VarEnv` as a cheaper alternative.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicVarEnv<T: Clone = Arc<String>>(VarEnvImpl<Arc<Inner<T>>>);

macro_rules! impl_methods {
    ($_Self:expr) => {
        /// Constructs a new environment with no environment variables.
        pub fn new() -> Self {
            $_Self(VarEnvImpl {
                vars: HashMap::new().into(),
            })
        }

        /// Constructs a new environment and initializes it with the environment
        /// variables of the current process.
        pub fn with_process_env_vars() -> Self where T: From<String> {
            Self::with_env_vars(::std::env::vars().into_iter()
                                .map(|(k, v)| (k.into(), v.into())))
        }

        /// Constructs a new environment with a provided collection of `(key, value)`
        /// environment variable pairs. These variables (if any) will be inherited by
        /// all commands.
        pub fn with_env_vars<I: IntoIterator<Item = (String, T)>>(iter: I) -> Self {
            $_Self(VarEnvImpl {
                vars: iter.into_iter()
                    .map(|(k, v)| (k, (v, true)))
                    .collect::<HashMap<_, _>>()
                    .into(),
            })
        }
    }
}

impl<T: Clone> VarEnv<T> {
    impl_methods!(VarEnv);
}

impl<T: Clone> AtomicVarEnv<T> {
    impl_methods!(AtomicVarEnv);
}

impl<T: Clone> Default for VarEnv<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Default for AtomicVarEnv<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> SubEnvironment for VarEnv<T> {
    fn sub_env(&self) -> Self {
        self.clone()
    }
}

impl<T: Clone> SubEnvironment for AtomicVarEnv<T> {
    fn sub_env(&self) -> Self {
        self.clone()
    }
}

macro_rules! impl_variable_environment_trait {
    () => {
        fn var(&self, name: &str) -> Option<&T> {
            self.0.var(name)
        }

        fn set_var(&mut self, name: String, val: T) {
            self.0.set_var(name, val)
        }

        fn env_vars(&self) -> Cow<[(&str, &T)]> {
            self.0.env_vars()
        }
    };
}

macro_rules! impl_unset_variable_environment_trait {
    () => {
        fn unset_var(&mut self, name: &str) {
            self.0.unset_var(name)
        }
    }
}

impl<T: Clone + Eq> VariableEnvironment<T> for VarEnv<T> {
    impl_variable_environment_trait!();
}

impl<T: Clone + Eq> UnsetVariableEnvironment<T> for VarEnv<T> {
    impl_unset_variable_environment_trait!();
}

impl<T: Clone + Eq> VariableEnvironment<T> for AtomicVarEnv<T> {
    impl_variable_environment_trait!();
}

impl<T: Clone + Eq> UnsetVariableEnvironment<T> for AtomicVarEnv<T> {
    impl_unset_variable_environment_trait!();
}

#[cfg(test)]
mod tests {
    use runtime::env::SubEnvironment;
    use runtime::ref_counted::RefCounted;
    use super::*;

    #[test]
    fn test_set_get_unset_var() {
        let name = "var";
        let value = "value".to_owned();
        let mut env = VarEnv::new();
        assert_eq!(env.var(&name), None);
        env.set_var(name.to_owned(), value.clone());
        assert_eq!(env.var(&name), Some(&value));
        env.unset_var(name);
        assert_eq!(env.var(&name), None);
    }

    #[test]
    fn test_sub_env_no_needless_clone() {
        let not_set = "not set";
        let name = "var";
        let value = "value";
        let mut env = VarEnv::new();
        env.set_var(name.to_owned(), value.to_owned());

        let mut env = env.sub_env();
        env.set_var(name.to_owned(), value.to_owned());
        if let Some(_) = env.0.vars.get_mut() {
            panic!("needles clone!");
        }

        env.unset_var(not_set);
        if let Some(_) = env.0.vars.get_mut() {
            panic!("needles clone!");
        }
    }

    #[test]
    fn test_env_vars() {
        use std::collections::HashSet;
        use std::iter::FromIterator;

        let env_name1 = "env_name1";
        let env_name2 = "env_name2";
        let env_val1 = "env_val1".to_owned();
        let env_val2 = "env_val2".to_owned();
        let name = "name".to_owned();
        let val = "value".to_owned();

        let mut env = VarEnv::with_env_vars(vec!(
            (env_name1.to_owned(), env_val1.clone()),
            (env_name2.to_owned(), env_val2.clone()),
        ));
        env.set_var(name, val);

        let correct = vec!(
            (env_name1, &env_val1),
            (env_name2, &env_val2),
        );

        let vars: HashSet<(&str, &String)> = HashSet::from_iter(env.env_vars().into_owned());
        assert_eq!(vars, HashSet::from_iter(correct));
    }

    #[test]
    fn test_set_var_in_child_env_should_not_affect_parent() {
        let parent_name = "parent-var";
        let parent_value = "parent-value";
        let child_name = "child-var";
        let child_value = "child-value";

        let mut parent = VarEnv::new();
        parent.set_var(parent_name.to_owned(), parent_value);

        {
            let mut child = parent.sub_env();
            assert_eq!(child.var(parent_name), Some(&parent_value));

            child.set_var(parent_name.to_owned(), child_value);
            child.set_var(child_name.to_owned(), child_value);
            assert_eq!(child.var(parent_name), Some(&child_value));
            assert_eq!(child.var(child_name), Some(&child_value));

            assert_eq!(parent.var(parent_name), Some(&parent_value));
            assert_eq!(parent.var(child_name), None);
        }

        assert_eq!(parent.var(parent_name), Some(&parent_value));
        assert_eq!(parent.var(child_name), None);
    }

    #[test]
    fn test_get_env_vars_visible_in_parent_and_child() {
        use std::collections::HashSet;
        use std::iter::FromIterator;

        let name1 = "var1";
        let value1 = "value1".to_owned();
        let name2 = "var2";
        let value2 = "value2".to_owned();

        let env = VarEnv::with_env_vars(vec!(
            (name1.to_owned(), value1.clone()),
            (name2.to_owned(), value2.clone()),
        ));

        let env_vars = HashSet::from_iter(vec!(
            (name1, &value1),
            (name2, &value2),
        ));

        let vars: HashSet<(&str, &String)> = HashSet::from_iter(env.env_vars().into_owned());
        assert_eq!(vars, env_vars);

        let child = env.sub_env();
        let vars: HashSet<(&str, &String)> = HashSet::from_iter(child.env_vars().into_owned());
        assert_eq!(vars, env_vars);
    }
}
