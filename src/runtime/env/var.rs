use runtime::env::SubEnvironment;
use runtime::ref_counted::RefCounted;

use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

/// An interface for setting and getting shell and environment variables.
pub trait VariableEnvironment {
    /// The type of variables this environment holds.
    type Var;
    /// Get the value of some variable. The values of both shell-only
    /// and environment variables will be looked up and returned.
    fn var(&self, name: &str) -> Option<&Self::Var>;
    /// Set the value of some variable, maintaining its status as an
    /// environment variable if previously set as such.
    fn set_var(&mut self, name: String, val: Self::Var);
    /// Unset the value of some variable (including environment variables).
    /// Get all current pairs of environment variables and their values.
    fn env_vars(&self) -> Cow<[(&str, &Self::Var)]>;
}

impl<'a, T: ?Sized + VariableEnvironment> VariableEnvironment for &'a mut T {
    type Var = T::Var;

    fn var(&self, name: &str) -> Option<&Self::Var> {
        (**self).var(name)
    }

    fn set_var(&mut self, name: String, val: Self::Var) {
        (**self).set_var(name, val);
    }

    fn env_vars(&self) -> Cow<[(&str, &Self::Var)]> {
        (**self).env_vars()
    }
}

/// An interface for unsetting shell and envrironment variables.
pub trait UnsetVariableEnvironment {
    /// Unset the value of some variable (including environment variables).
    fn unset_var(&mut self, name: &str);
}

impl<'a, T: ?Sized + UnsetVariableEnvironment> UnsetVariableEnvironment for &'a mut T {
    fn unset_var(&mut self, name: &str) {
        (**self).unset_var(name);
    }
}

macro_rules! impl_env {
    ($(#[$attr:meta])* pub struct $Env:ident, $Rc:ident) => {
        $(#[$attr])*
        #[derive(PartialEq, Eq)]
        pub struct $Env<T = $Rc<String>> {
            /// A mapping of variable names to their values.
            ///
            /// The tupled boolean indicates if a variable should be exported to other commands.
            vars: $Rc<HashMap<String, (T, bool)>>,
        }

        impl<T> $Env<T> {
            /// Constructs a new environment with no environment variables.
            pub fn new() -> Self {
                $Env {
                    vars: HashMap::new().into(),
                }
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
                $Env {
                    vars: iter.into_iter()
                        .map(|(k, v)| (k, (v, true)))
                        .collect::<HashMap<_, _>>()
                        .into(),
                }
            }
        }

        impl<T: Clone + Eq> VariableEnvironment for $Env<T> {
            type Var = T;

            fn var(&self, name: &str) -> Option<&Self::Var> {
                self.vars.get(name).map(|&(ref val, _)| val)
            }

            fn set_var(&mut self, name: String, val: Self::Var) {
                let (needs_insert, exported) = match self.vars.get(&name) {
                    Some(&(ref existing_val, exported)) => (&val != existing_val, exported),
                    None => (true, false),
                };

                if needs_insert {
                    self.vars.make_mut().insert(name, (val, exported));
                }
            }

            fn env_vars(&self) -> Cow<[(&str, &Self::Var)]> {
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

        impl<T: Clone> UnsetVariableEnvironment for $Env<T> {
            fn unset_var(&mut self, name: &str) {
                if self.vars.contains_key(name) {
                    self.vars.make_mut().remove(name);
                }
            }
        }

        impl<T: fmt::Debug> fmt::Debug for $Env<T> {
            fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
                use std::collections::BTreeMap;

                let mut vars = BTreeMap::new();
                let mut env_vars = BTreeMap::new();

                for (name, &(ref val, is_env)) in &*self.vars {
                    if is_env {
                        env_vars.insert(name, val);
                    } else {
                        vars.insert(name, val);
                    }
                }

                fmt.debug_struct(stringify!($Env))
                    .field("env_vars", &env_vars)
                    .field("vars", &vars)
                    .finish()
            }
        }

        impl<T> Default for $Env<T> {
            fn default() -> Self {
                Self::new()
            }
        }

        impl<T> Clone for $Env<T> {
            fn clone(&self) -> Self {
                $Env {
                    vars: self.vars.clone(),
                }
            }
        }

        impl<T> SubEnvironment for $Env<T> {
            fn sub_env(&self) -> Self {
                self.clone()
            }
        }
    };
}

impl_env!(
    /// An `Environment` module for setting and getting shell variables.
    ///
    /// Uses `Rc` internally. For a possible `Send` and `Sync` implementation,
    /// see `AtomicVarEnv`.
    pub struct VarEnv,
    Rc
);

impl_env!(
    /// An `Environment` module for setting and getting shell variables.
    ///
    /// Uses `Arc` internally. If `Send` and `Sync` is not required of the implementation,
    /// see `VarEnv` as a cheaper alternative.
    pub struct AtomicVarEnv,
    Arc
);

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
        if let Some(_) = env.vars.get_mut() {
            panic!("needles clone!");
        }

        env.unset_var(not_set);
        if let Some(_) = env.vars.get_mut() {
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
