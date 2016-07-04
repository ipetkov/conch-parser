//! A module for evaluating arbitrary shell components such as words,
//! parameter subsitutions, redirections, and others.

mod arith;
mod parameter;
mod redirect;
mod word;

use glob;
use runtime::Result;
use runtime::env::{StringWrapper, VariableEnvironment};
use std::vec;

pub use self::parameter::*;
pub use self::redirect::*;
pub use self::word::*;

/// Represents the types of fields that may result from evaluating a word.
/// It is important to maintain such distinctions because evaluating parameters
/// such as `$@` and `$*` have different behaviors in different contexts.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Fields<T> {
    /// No fields, distinct from present-but-null fields.
    Zero,
    /// A single field.
    Single(T),
    /// Any number of fields resulting from evaluating the `$@` special parameter.
    At(Vec<T>),
    /// Any number of fields resulting from evaluating the `$*` special parameter.
    Star(Vec<T>),
    /// A non-zero number of fields resulting from splitting, and which do not have
    /// any special meaning.
    Split(Vec<T>),
}

impl<T: StringWrapper> Fields<T> {
    /// Indicates if a set of fields is considered null.
    ///
    /// A set of fields is null if every single string
    /// it holds is the empty string.
    pub fn is_null(&self) -> bool {
        match *self {
            Fields::Zero => true,

            Fields::Single(ref s) => s.as_str().is_empty(),

            Fields::At(ref v)   |
            Fields::Star(ref v) |
            Fields::Split(ref v) => v.iter().all(|s| s.as_str().is_empty()),
        }
    }

    /// Joins all fields using a space.
    ///
    /// Note: `Zero` is treated as a empty-but-present field for simplicity.
    pub fn join(self) -> T {
        match self {
            Fields::Zero => String::new().into(),
            Fields::Single(s) => s,
            Fields::At(v)   |
            Fields::Star(v) |
            Fields::Split(v) => v.iter()
                .map(StringWrapper::as_str)
                .filter_map(|s| if s.is_empty() { None } else { Some(s) })
                .collect::<Vec<&str>>()
                .join(" ")
                .into(),
        }
    }

    /// Joins any field unconditionally with the first character of `$IFS`.
    /// If `$IFS` is unset, fields are joined with a space, or concatenated
    /// if `$IFS` is empty.
    ///
    /// Note: `Zero` is treated as a empty-but-present field for simplicity.
    fn join_with_ifs<E: ?Sized>(self, env: &E) -> T
        where E: VariableEnvironment,
              E::Var: StringWrapper,
    {
        match self {
            Fields::Zero => String::new().into(),
            Fields::Single(s) => s,
            Fields::At(v)   |
            Fields::Star(v) |
            Fields::Split(v) => {
                let sep = env.var("IFS")
                    .map(StringWrapper::as_str)
                    .map_or(" ", |s| if s.is_empty() { "" } else { &s[0..1] });

                v.iter()
                    .map(StringWrapper::as_str)
                    .collect::<Vec<_>>()
                    .join(sep)
                    .into()
            },
        }
    }
}

// FIXME: with specialization can also implement From<IntoIterator<T>> but keep From<Vec<T>
impl<T> From<Vec<T>> for Fields<T> {
    fn from(mut fields: Vec<T>) -> Self {
        if fields.is_empty() {
            Fields::Zero
        } else if fields.len() == 1 {
            Fields::Single(fields.pop().unwrap())
        } else {
            Fields::Split(fields)
        }
    }
}

impl<T> From<T> for Fields<T> {
    fn from(t: T) -> Self {
        Fields::Single(t)
    }
}

impl<T> IntoIterator for Fields<T> {
    type Item = T;
    type IntoIter = vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        let vec = match self {
            Fields::Zero => vec!(),
            Fields::Single(s) => vec!(s),
            Fields::At(v)   |
            Fields::Star(v) |
            Fields::Split(v) => v,
        };

        vec.into_iter()
    }
}

/// An enum representing how tildes (`~`) are expanded.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum TildeExpansion {
    /// Tildes retain a literal value, no expansion is done.
    None,
    /// Tildes are expanded if they are at the beginning of a word.
    First,
    /// All tildes (either at start of word or after `:`) are expanded.
    All,
}

/// A config object for customizing `WordEval` evaluations.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct WordEvalConfig {
    /// Configure tilde expansion.
    pub tilde_expansion: TildeExpansion,
    /// Perform field splitting where appropriate or not.
    pub split_fields_further: bool,
}

/// A trait for evaluating shell words with various rules for expansion.
///
/// Generic over the representation of an evaluation type (e.g. String, Rc<String>),
/// and an environment/context type for evaluation.
pub trait WordEval<T, E: ?Sized> {
    /// Evaluates a word in a given environment and performs all expansions.
    ///
    /// Tilde, parameter, command substitution, and arithmetic expansions are
    /// performed first. All resulting fields are then further split based on
    /// the contents of the `IFS` variable (no splitting is performed if `IFS`
    /// is set to be the empty or null string). Next, pathname expansion
    /// is performed on each field which may yield a of file paths if
    /// the field contains a valid pattern. Finally, quotes and escaping
    /// backslashes are removed from the original word (unless they themselves
    /// have been quoted).
    fn eval(&self, env: &mut E) -> Result<Fields<T>> {
        self.eval_with_config(env, WordEvalConfig {
            tilde_expansion: TildeExpansion::First,
            split_fields_further: true,
        })
    }

    /// Evaluates a word in a given environment without doing field and pathname expansions.
    ///
    /// Tilde, parameter, command substitution, arithmetic expansions, and quote removals
    /// will be performed, however. In addition, if multiple fields arise as a result
    /// of evaluating `$@` or `$*`, the fields will be joined with a single space.
    fn eval_as_assignment(&self, env: &mut E) -> Result<T>
        where T: StringWrapper,
              E: VariableEnvironment,
              E::Var: StringWrapper,
    {
        let cfg = WordEvalConfig {
            tilde_expansion: TildeExpansion::All,
            split_fields_further: false,
        };

        match try!(self.eval_with_config(env, cfg)) {
            f@Fields::Zero      |
            f@Fields::Single(_) |
            f@Fields::At(_)     |
            f@Fields::Split(_) => Ok(f.join()),
            f@Fields::Star(_) => Ok(f.join_with_ifs(env)),
        }
    }

    /// Evaluates a word just like `eval`, but converts the result into a `glob::Pattern`.
    fn eval_as_pattern(&self, env: &mut E) -> Result<glob::Pattern>
        where T: StringWrapper,
    {
        let cfg = WordEvalConfig {
            tilde_expansion: TildeExpansion::First,
            split_fields_further: false,
        };

        // FIXME: actually compile the pattern here
        let pat = try!(self.eval_with_config(env, cfg)).join();
        Ok(glob::Pattern::new(&glob::Pattern::escape(pat.as_str())).unwrap())
    }

    /// Evaluate and take a provided config into account.
    ///
    /// Generally `$*` should always be joined by the first char of `$IFS` or have all
    /// fields concatenated if `$IFS` is null or `$*` is in double quotes.
    ///
    /// If `cfg.split_fields_further` is false then all empty fields will be kept.
    ///
    /// The caller is responsible for doing path expansions.
    fn eval_with_config(&self, env: &mut E, cfg: WordEvalConfig) -> Result<Fields<T>>;
}

#[cfg(test)]
mod tests {
    use runtime::Result;
    use runtime::env::Env;
    use super::*;

    #[test]
    fn test_fields_is_null() {
        let empty_strs = vec!(
            "".to_owned(),
            "".to_owned(),
            "".to_owned(),
        );

        let mostly_non_empty_strs = vec!(
            "foo".to_owned(),
            "".to_owned(),
            "bar".to_owned(),
        );

        assert_eq!(Fields::Zero::<String>.is_null(), true);
        assert_eq!(Fields::Single("".to_owned()).is_null(), true);
        assert_eq!(Fields::At(empty_strs.clone()).is_null(), true);
        assert_eq!(Fields::Star(empty_strs.clone()).is_null(), true);
        assert_eq!(Fields::Split(empty_strs.clone()).is_null(), true);

        assert_eq!(Fields::Single("foo".to_owned()).is_null(), false);
        assert_eq!(Fields::At(mostly_non_empty_strs.clone()).is_null(), false);
        assert_eq!(Fields::Star(mostly_non_empty_strs.clone()).is_null(), false);
        assert_eq!(Fields::Split(mostly_non_empty_strs.clone()).is_null(), false);
    }

    #[test]
    fn test_fields_join() {
        let strs = vec!(
            "foo".to_owned(),
            "".to_owned(),
            "bar".to_owned(),
        );

        assert_eq!(Fields::Zero::<String>.join(), "");
        assert_eq!(Fields::Single("foo".to_owned()).join(), "foo");
        assert_eq!(Fields::At(strs.clone()).join(), "foo bar");
        assert_eq!(Fields::Star(strs.clone()).join(), "foo bar");
        assert_eq!(Fields::Split(strs.clone()).join(), "foo bar");
    }

    #[test]
    fn test_fields_join_with_ifs() {
        use runtime::env::VariableEnvironment;

        let strs = vec!(
            "foo".to_owned(),
            "".to_owned(), // Empty strings should not be eliminated
            "bar".to_owned(),
        );

        let mut env = Env::new();

        env.set_var(String::from("IFS"), "!".to_owned());
        assert_eq!(Fields::Zero::<String>.join_with_ifs(&env), "");
        assert_eq!(Fields::Single("foo".to_owned()).join_with_ifs(&env), "foo");
        assert_eq!(Fields::At(strs.clone()).join_with_ifs(&env), "foo!!bar");
        assert_eq!(Fields::Star(strs.clone()).join_with_ifs(&env), "foo!!bar");
        assert_eq!(Fields::Split(strs.clone()).join_with_ifs(&env), "foo!!bar");

        // Blank IFS
        env.set_var(String::from("IFS"), "".to_owned());
        assert_eq!(Fields::Zero::<String>.join_with_ifs(&env), "");
        assert_eq!(Fields::Single("foo".to_owned()).join_with_ifs(&env), "foo");
        assert_eq!(Fields::At(strs.clone()).join_with_ifs(&env), "foobar");
        assert_eq!(Fields::Star(strs.clone()).join_with_ifs(&env), "foobar");
        assert_eq!(Fields::Split(strs.clone()).join_with_ifs(&env), "foobar");

        // FIXME: test with unset IFS
    }

    #[test]
    fn test_fields_from_vec() {
        let s = "foo".to_owned();
        let strs = vec!(
            s.clone(),
            "".to_owned(),
            "bar".to_owned(),
        );

        assert_eq!(Fields::Zero::<String>, Vec::<String>::new().into());
        assert_eq!(Fields::Single(s.clone()), vec!(s.clone()).into());
        assert_eq!(Fields::Split(strs.clone()), strs.clone().into());
    }

    #[test]
    fn test_fields_from_t() {
        let string = "foo".to_owned();
        assert_eq!(Fields::Single(string.clone()), string.into());
        // Empty string is NOT an empty field
        let string = "".to_owned();
        assert_eq!(Fields::Single(string.clone()), string.into());
    }

    #[test]
    fn test_fields_into_iter() {
        let s = "foo".to_owned();
        let strs = vec!(
            s.clone(),
            "".to_owned(),
            "bar".to_owned(),
        );

        let empty: Vec<String> = vec!();
        assert_eq!(empty, Fields::Zero::<String>.into_iter().collect::<Vec<_>>());
        assert_eq!(vec!(s.clone()), Fields::Single(s.clone()).into_iter().collect::<Vec<_>>());
        assert_eq!(strs.clone(), Fields::At(strs.clone()).into_iter().collect::<Vec<_>>());
        assert_eq!(strs.clone(), Fields::Star(strs.clone()).into_iter().collect::<Vec<_>>());
        assert_eq!(strs.clone(), Fields::Split(strs.clone()).into_iter().collect::<Vec<_>>());
    }

    #[test]
    fn test_eval_expands_first_tilde_and_splits_words() {
        struct MockWord;

        impl<E: ?Sized> WordEval<String, E> for MockWord {
            fn eval_with_config(&self, _: &mut E, cfg: WordEvalConfig) -> Result<Fields<String>> {
                assert_eq!(cfg, WordEvalConfig {
                    tilde_expansion: TildeExpansion::First,
                    split_fields_further: true,
                });
                Ok(Fields::Zero)
            }
        }

        MockWord.eval(&mut ()).unwrap();
    }

    #[test]
    fn test_eval_as_assignment_expands_all_tilde_and_does_not_split_words() {
        use runtime::env::VariableEnvironment;

        macro_rules! word_eval_impl {
            ($name:ident, $ret:expr) => {
                struct $name;

                impl<E: ?Sized> WordEval<String, E> for $name {
                    fn eval_with_config(&self, _: &mut E, cfg: WordEvalConfig)
                        -> Result<Fields<String>>
                    {
                        assert_eq!(cfg, WordEvalConfig {
                            tilde_expansion: TildeExpansion::All,
                            split_fields_further: false,
                        });
                        Ok($ret)
                    }
                }
            };
        }

        let mut env = Env::new();
        env.set_var("IFS".to_owned(), "!".to_owned());

        word_eval_impl!(MockWord1, Fields::Zero);
        assert_eq!(MockWord1.eval_as_assignment(&mut env), Ok("".to_owned()));

        word_eval_impl!(MockWord2, Fields::Single("foo".to_owned()));
        assert_eq!(MockWord2.eval_as_assignment(&mut env), Ok("foo".to_owned()));

        word_eval_impl!(MockWord3, Fields::At(vec!(
            "foo".to_owned(),
            "bar".to_owned(),
        )));
        assert_eq!(MockWord3.eval_as_assignment(&mut env), Ok("foo bar".to_owned()));

        word_eval_impl!(MockWord4, Fields::Split(vec!(
            "foo".to_owned(),
            "bar".to_owned(),
        )));
        assert_eq!(MockWord4.eval_as_assignment(&mut env), Ok("foo bar".to_owned()));

        word_eval_impl!(MockWord5, Fields::Star(vec!(
            "foo".to_owned(),
            "bar".to_owned(),
        )));
        assert_eq!(MockWord5.eval_as_assignment(&mut env), Ok("foo!bar".to_owned()));
    }

    #[test]
    fn test_eval_as_pattern_expands_first_tilde_and_does_not_split_words_and_joins_fields() {
        struct MockWord;

        impl<E: ?Sized> WordEval<String, E> for MockWord {
            fn eval_with_config(&self, _: &mut E, cfg: WordEvalConfig) -> Result<Fields<String>> {
                assert_eq!(cfg, WordEvalConfig {
                    tilde_expansion: TildeExpansion::First,
                    split_fields_further: false,
                });
                Ok(Fields::Split(vec!(
                    "foo".to_owned(),
                    "*?".to_owned(),
                    "bar".to_owned(),
                )))
            }
        }

        let pat = MockWord.eval_as_pattern(&mut ()).unwrap();
        assert_eq!(pat.as_str(), "foo [*][?] bar"); // FIXME: update once patterns implemented
        //assert_eq!(pat.as_str(), "foo *? bar");
    }
}
