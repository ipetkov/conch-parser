use runtime::env::{SubEnvironment, shallow_copy};

use std::borrow::Cow;
use std::collections::HashMap;
use std::rc::Rc;

/// An interface for setting and getting shell and environment variables.
pub trait VariableEnvironment<T: ?Sized> {
    /// Get the value of some variable. The values of both shell-only
    /// and environment variables will be looked up and returned.
    fn var(&self, name: &str) -> Option<&T>;
    /// Set the value of some variable, maintaining its status as an
    /// environment variable if previously set as such.
    // FIXME: might be able to make name also T and not need an owned String
    fn set_var(&mut self, name: String, val: T);
    /// Unset the value of some variable (including environment variables).
    fn unset_var(&mut self, name: &str);
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

    fn unset_var(&mut self, name: &str) {
        (**self).unset_var(name);
    }

    fn env_vars(&self) -> Cow<[(&str, &T)]> {
        (**self).env_vars()
    }
}

/// An `Environment` module for setting and getting shell variables.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VarEnv<'a, T = Rc<String>> where T: 'a + Clone {
    /// A mapping of variable names to their values.
    ///
    /// The tupled boolean indicates if a variable should be exported to other commands.
    vars: Cow<'a, HashMap<String, (T, bool)>>,
}

impl<'a, T: Clone> VarEnv<'a, T> {
    /// Constructs a new `VarEnv` with no environment variables.
    pub fn new() -> Self {
        VarEnv {
            vars: Cow::Owned(HashMap::new()),
        }
    }

    /// Constructs a new `VarEnv` and initializes it with the environment
    /// variables of the current process.
    pub fn with_process_env_vars() -> Self where T: From<String> {
        Self::with_env_vars(::std::env::vars().into_iter()
                            .map(|(k, v)| (k.into(), v.into())))
    }

    /// Constructs a new `VarEnv` with a provided collection of `(key, value)`
    /// environment variable pairs. These variables (if any) will be inherited by
    /// all commands.
    pub fn with_env_vars<I: IntoIterator<Item = (String, T)>>(iter: I) -> Self {
        VarEnv {
            vars: Cow::Owned(iter.into_iter()
                             .map(|(k, v)| (k, (v, true)))
                             .collect()),
        }
    }
}

impl<'a, T: Clone> Default for VarEnv<'a, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: Clone> SubEnvironment<'a> for VarEnv<'a, T> {
    fn sub_env(&'a self) -> Self {
        VarEnv {
            vars: shallow_copy(&self.vars),
        }
    }
}

impl<'a, T> VariableEnvironment<T> for VarEnv<'a, T> where T: Clone + Eq {
    fn var(&self, name: &str) -> Option<&T> {
        self.vars.get(name).map(|&(ref val, _)| val)
    }

    fn set_var(&mut self, name: String, val: T) {
        let (needs_insert, exported) = match self.vars.get(&name) {
            Some(&(ref existing_val, exported)) => (&val != existing_val, exported),
            None => (true, false),
        };

        if needs_insert {
            self.vars.to_mut().insert(name, (val, exported));
        }
    }

    fn unset_var(&mut self, name: &str) {
        if self.vars.contains_key(name) {
            self.vars.to_mut().remove(name);
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

#[cfg(test)]
mod tests {
    use runtime::env::SubEnvironment;
    use std::borrow::Cow;
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
        if let Cow::Owned(_) = env.vars {
            panic!("needles clone!");
        }

        env.unset_var(not_set);
        if let Cow::Owned(_) = env.vars {
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
    fn test_env_vars_remain_exported_even_after_update() {
        let env_name = "env_name1";
        let env_val_old = "old value".to_owned();
        let env_val_new = "new value".to_owned();

        let mut env = VarEnv::with_env_vars(vec!((env_name.to_owned(), env_val_old)));
        env.set_var(env_name.to_owned(), env_val_new.clone());
        assert_eq!(env.env_vars(), vec!((env_name, &env_val_new)));
    }
}
