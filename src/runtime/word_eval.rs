use glob;

use std::convert::{From, Into};
use std::iter::{IntoIterator, Iterator};
use std::rc::Rc;
use super::{Environment, Result};
use syntax::ast::{ComplexWord, SimpleWord, Word};

const IFS_DEFAULT: &'static str = " \t\n";

/// Represents the types of fields that may result from evaluating a word.
/// It is important to maintain such distinctions because evaluating parameters
/// such as `$@` and `$*` have different behaviors in different contexts.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Fields {
    /// No fields, distinct from present-but-null fields.
    Zero,
    /// A single field.
    Single(Rc<String>),
    /// Any number of fields resulting from evaluating the `$@` special parameter.
    At(Vec<Rc<String>>),
    /// Any number of fields resulting from evaluating the `$*` special parameter.
    Star(Vec<Rc<String>>),
    /// A non-zero number of fields that do not have any special meaning.
    Many(Vec<Rc<String>>),
}

impl Fields {
    /// Indicates if a set of fields is considered null.
    ///
    /// A set of fields is null if every single string
    /// it holds is the empty string.
    pub fn is_null(&self) -> bool {
        match *self {
            Fields::Zero => true,

            Fields::Single(ref s) => s.is_empty(),

            Fields::At(ref v)   |
            Fields::Star(ref v) |
            Fields::Many(ref v) => v.iter().all(|s| s.is_empty()),
        }
    }

    /// Joins all fields using a space.
    ///
    /// Note: `Zero` is treated as a empty-but-present field for simplicity.
    pub fn join(self) -> Rc<String> {
        match self {
            Fields::Zero => Rc::new(String::new()),
            Fields::Single(s) => s,
            Fields::At(v)   |
            Fields::Star(v) |
            Fields::Many(v) => Rc::new(v.iter().filter_map(|s| {
                if s.is_empty() {
                    None
                } else {
                    Some(&***s)
                }
            }).collect::<Vec<&str>>().join(" ")),
        }
    }

    /// Joins any field unconditionally with the first character of `$IFS`.
    /// If `$IFS` is unset, fields are joined with a space, or concatenated
    /// if `$IFS` is empty.
    ///
    /// Note: `Zero` is treated as a empty-but-present field for simplicity.
    fn join_with_ifs(self, env: &Environment) -> Rc<String> {
        match self {
            Fields::Zero => Rc::new(String::new()),
            Fields::Single(s) => s,
            Fields::At(v)   |
            Fields::Star(v) |
            Fields::Many(v) => {
                let sep = match env.var("IFS") {
                    Some(ref s) if s.is_empty() => "",
                    Some(s) => &s[0..1],
                    None => " ",
                };

                let v: Vec<_> = v.iter().map(|s| &***s).collect();
                Rc::new(v.join(sep))
            },
        }
    }
}

impl From<Vec<Rc<String>>> for Fields {
    fn from(mut fields: Vec<Rc<String>>) -> Self {
        if fields.is_empty() {
            Fields::Zero
        } else if fields.len() == 1 {
            Fields::Single(fields.pop().unwrap())
        } else {
            Fields::Many(fields)
        }
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
pub trait WordEval {
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
    fn eval(&self, env: &mut Environment) -> Result<Fields> {
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
    fn eval_as_assignment(&self, env: &mut Environment) -> Result<Rc<String>> {
        let cfg = WordEvalConfig {
            tilde_expansion: TildeExpansion::All,
            split_fields_further: false,
        };

        match try!(self.eval_with_config(env, cfg)) {
            f@Fields::Zero      |
            f@Fields::Single(_) |
            f@Fields::At(_)     |
            f@Fields::Many(_) => Ok(f.join()),
            f@Fields::Star(_) => Ok(f.join_with_ifs(env)),
        }
    }

    /// Evaluates a word just like `eval`, but converts the result into a `glob::Pattern`.
    fn eval_as_pattern(&self, env: &mut Environment) -> Result<glob::Pattern> {
        let cfg = WordEvalConfig {
            tilde_expansion: TildeExpansion::First,
            split_fields_further: false,
        };

        // FIXME: actually compile the pattern here
        let pat = try!(self.eval_with_config(env, cfg)).join();
        Ok(glob::Pattern::new(&glob::Pattern::escape(&pat)).unwrap())
    }

    /// Evaluate and take a provided config into account.
    ///
    /// Generally `$*` should always be joined by the first char of `$IFS` or have all
    /// fields concatenated if `$IFS` is null or `$*` is in double quotes.
    ///
    /// If `cfg.split_fields_further` is false then all empty fields will be kept.
    ///
    /// The caller is responsible for doing path expansions.
    fn eval_with_config(&self,
                        env: &mut Environment,
                        cfg: WordEvalConfig) -> Result<Fields>;
}

impl WordEval for SimpleWord {
    fn eval_with_config(&self,
                        env: &mut Environment,
                        cfg: WordEvalConfig) -> Result<Fields>
    {
        let maybe_split_fields = |fields, env: &mut Environment| {
            if cfg.split_fields_further {
                match fields {
                    Fields::Zero      => Fields::Zero,
                    Fields::Single(f) => split_fields(vec!(f), env).into(),
                    Fields::At(fs)    => Fields::At(split_fields(fs, env)),
                    Fields::Star(fs)  => Fields::Star(split_fields(fs, env)),
                    Fields::Many(fs)  => Fields::Many(split_fields(fs, env)),
                }
            } else {
                fields
            }
        };

        let ret = match *self {
            SimpleWord::Literal(ref s) |
            SimpleWord::Escaped(ref s) => Fields::Single(Rc::new(s.clone())),

            SimpleWord::Star        => Fields::Single(Rc::new(String::from("*"))),
            SimpleWord::Question    => Fields::Single(Rc::new(String::from("?"))),
            SimpleWord::SquareOpen  => Fields::Single(Rc::new(String::from("["))),
            SimpleWord::SquareClose => Fields::Single(Rc::new(String::from("]"))),
            SimpleWord::Colon       => Fields::Single(Rc::new(String::from(":"))),

            SimpleWord::Tilde => match cfg.tilde_expansion {
                TildeExpansion::None => Fields::Single(Rc::new(String::from("~"))),
                TildeExpansion::All |
                TildeExpansion::First => {
                    // Note: even though we are expanding the equivalent of `$HOME`, a tilde
                    // expansion is NOT considered a parameter expansion, and therefore
                    // should not be subjected to field splitting.
                    env.var("HOME").map_or(Fields::Zero, |f| Fields::Single(f.clone()))
                },
            },

            SimpleWord::Subst(ref s) => maybe_split_fields(try!(s.eval(env)), env),
            SimpleWord::Param(ref p) => maybe_split_fields(p.eval(env).unwrap_or(Fields::Zero), env),
        };

        Ok(ret)
    }
}

impl WordEval for Word {
    fn eval_with_config(&self,
                        env: &mut Environment,
                        cfg: WordEvalConfig) -> Result<Fields>
    {
        let ret = match *self {
            Word::Simple(ref s) => try!(s.eval_with_config(env, cfg)),
            Word::SingleQuoted(ref s) => Fields::Single(Rc::new(s.clone())),
            Word::DoubleQuoted(ref v) => {
                // Make sure we are NOT doing any tilde expanions for further field splitting
                let cfg = WordEvalConfig {
                    tilde_expansion: TildeExpansion::None,
                    split_fields_further: false,
                };

                let mut fields = Vec::new();
                let mut cur_field: Option<String> = None;

                macro_rules! append_to_cur_field {
                    ($rc:expr) => {
                        match cur_field {
                            Some(ref mut cur_field) => cur_field.push_str(&$rc),
                            None => cur_field = Some(Rc::try_unwrap($rc).unwrap_or_else(|rc| (&*rc).clone())),
                        }
                    }
                };

                for w in v.iter() {
                    match (try!(w.eval_with_config(env, cfg)), w) {
                        (Fields::Zero, _) => continue,
                        (Fields::Single(s), _) => append_to_cur_field!(s),
                        (f@Fields::Star(_), _) => append_to_cur_field!(f.join_with_ifs(env)),

                        // Any fields generated by $@ must be maintained, however, the first and last
                        // fields of $@ should be concatenated to whatever comes before/after them.
                        (Fields::At(v), _) => {
                            // According to the POSIX spec, if $@ is empty it should generate NO fields
                            // even when within double quotes.
                            if !v.is_empty() {
                                let mut iter = v.into_iter();
                                if let Some(first) = iter.next() {
                                    append_to_cur_field!(first);
                                }

                                cur_field.take().map(|s| fields.push(Rc::new(s)));

                                let mut last = None;
                                for next in iter {
                                    fields.extend(last.take());
                                    last = Some(next);
                                }

                                last.map(|rc| append_to_cur_field!(rc));
                            }
                        },

                        // Since we should have indicated we do NOT want field splitting,
                        // the following word variants should all yield `Single` fields (or at least
                        // a specific `Star` or `At` field type for parameter{s, substitutions}).
                        (Fields::Many(_), &SimpleWord::Literal(_))  |
                        (Fields::Many(_), &SimpleWord::Escaped(_))  |
                        (Fields::Many(_), &SimpleWord::Star)        |
                        (Fields::Many(_), &SimpleWord::Question)    |
                        (Fields::Many(_), &SimpleWord::SquareOpen)  |
                        (Fields::Many(_), &SimpleWord::SquareClose) |
                        (Fields::Many(_), &SimpleWord::Tilde)       |
                        (Fields::Many(_), &SimpleWord::Colon)       |
                        (Fields::Many(_), &SimpleWord::Subst(_))    |
                        (Fields::Many(_), &SimpleWord::Param(_))    => unreachable!(),
                    }
                }

                cur_field.map(|s| fields.push(Rc::new(s)));
                fields.into()
            }
        };

        Ok(ret)
    }
}

impl WordEval for ComplexWord {
    fn eval_with_config(&self,
                        env: &mut Environment,
                        cfg: WordEvalConfig) -> Result<Fields>
    {
        let ret = match *self {
            ComplexWord::Single(ref w) => try!(w.eval_with_config(env, cfg)),

            ComplexWord::Concat(ref v) => {
                let cfg = WordEvalConfig {
                    tilde_expansion: TildeExpansion::None,
                    split_fields_further: cfg.split_fields_further,
                };

                let mut fields: Vec<Rc<String>> = Vec::new();
                for w in v.iter() {
                    let mut iter = try!(w.eval_with_config(env, cfg)).into_iter();
                    match (fields.pop(), iter.next()) {
                       (Some(last), Some(next)) => {
                           let mut new = Rc::try_unwrap(last).unwrap_or_else(|rc| {
                               let mut new = String::with_capacity(rc.len() + next.len());
                               new.push_str(&rc);
                               new
                           });
                           new.push_str(&next);
                           fields.push(Rc::new(new));
                       },
                       (Some(last), None) => fields.push(last),
                       (None, Some(next)) => fields.push(next),
                       (None, None)       => continue,
                    }

                    fields.extend(iter);
                }

                fields.into()
            },
        };

        Ok(ret)
    }
}

/// Splits a vector of fields further based on the contents of the `IFS`
/// variable (i.e. as long as it is non-empty). Any empty fields, original
/// or otherwise created will be discarded.
fn split_fields(words: Vec<Rc<String>>, env: &Environment) -> Vec<Rc<String>> {
    // If IFS is set but null, there is nothing left to split
    let ifs = env.var("IFS").map_or(IFS_DEFAULT, |s| &s);
    if ifs.is_empty() {
        return words;
    }

    let whitespace: Vec<char> = ifs.chars().filter(|c| c.is_whitespace()).collect();

    let mut fields = Vec::with_capacity(words.len());
    'word: for word in words {
        if word.is_empty() {
            continue;
        }

        let mut iter = word.chars().enumerate();
        loop {
            let start;
            loop {
                match iter.next() {
                    // We are still skipping leading whitespace, if we hit the
                    // end of the word there are no fields to create, even empty ones.
                    None => continue 'word,
                    Some((idx, c)) => if !whitespace.contains(&c) {
                        start = idx;
                        break;
                    },
                }
            }

            let end;
            loop {
                match iter.next() {
                    None => {
                        end = None;
                        break;
                    },
                    Some((idx, c)) => if ifs.contains(c) {
                        end = Some(idx);
                        break;
                    },
                }
            }

            let field = match end {
                Some(end) => &word[start..end],
                None      => &word[start..],
            };

            fields.push(Rc::new(String::from(field)));
        }
    }

    fields.shrink_to_fit();
    fields
}


#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use runtime::{Env, Environment};
    use super::*;
    use syntax::ast::{Parameter, Word};
    use syntax::ast::ComplexWord::*;
    use syntax::ast::SimpleWord::*;
    use syntax::parse::test::{lit, escaped, single_quoted};

    #[test]
    fn test_eval_word_literal_evals_to_self() {
        let value = String::from("foobar");
        let mut env = Env::new().unwrap();
        assert_eq!(Single(lit(&value)).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_eval_word_special_literals_eval_to_self() {
        let cases = vec!(
            (Star,        "*"),
            (Question,    "?"),
            (SquareOpen,  "["),
            (SquareClose, "]"),
            (Colon,       ":"),
        );

        let mut env = Env::new().unwrap();

        for (word, correct) in cases {
            let word = Single(Word::Simple(Box::new(word)));
            assert_eq!(word.eval(&mut env), Ok(Fields::Single(Rc::new(String::from(correct)))));
        }
    }

    #[test]
    fn test_eval_word_lone_tilde_expansion() {
        let home_value = Rc::new(String::from("foobar"));
        let mut env = Env::new().unwrap();
        env.set_var(String::from("HOME"), home_value.clone());
        let word = Single(Word::Simple(Box::new(Tilde)));
        assert_eq!(word.eval(&mut env), Ok(Fields::Single(home_value)));
    }

    #[test]
    fn test_eval_word_tilde_in_middle_of_word_does_not_expand() {
        let mut env = Env::new().unwrap();
        assert_eq!(Concat(vec!(
            lit("foo"),
            lit("~"),
            lit("bar"),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foo~bar")))));
    }

    #[test]
    fn test_eval_word_tilde_in_middle_of_word_after_colon_does_not_expand() {
        let mut env = Env::new().unwrap();
        assert_eq!(Concat(vec!(
            lit("foo"),
            Word::Simple(Box::new(Colon)),
            lit("~"),
            lit("bar"),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foo:~bar")))));
    }

    #[test]
    fn test_eval_word_double_quoted_does_parameter_expansions_as_single_field() {
        let var = String::from("var");
        let mut env = Env::new().unwrap();
        env.set_var(var.clone(), Rc::new(String::from("hello world")));
        assert_eq!(Word::DoubleQuoted(vec!(
            Literal(String::from("foo")),
            Param(Parameter::Var(var)),
            Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foohello worldbar")))));
    }

    #[test]
    fn test_eval_word_double_quoted_does_not_expand_tilde() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Tilde,
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("~")))));

        assert_eq!(Word::DoubleQuoted(vec!(
            Tilde,
            Literal(String::from("root")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("~root")))));

        assert_eq!(Word::DoubleQuoted(vec!(
            Tilde,
            Literal(String::from("/root")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("~/root")))));
    }

    #[test]
    fn test_eval_word_double_quoted_param_at_unset_results_in_no_fields() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Param(Parameter::At),
        )).eval(&mut env), Ok(Fields::Zero))
    }

    #[test]
    fn test_eval_word_double_quoted_param_star_unset_results_in_no_fields() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Param(Parameter::Star),
        )).eval(&mut env), Ok(Fields::Zero))
    }

    #[test]
    fn test_eval_word_double_quoted_param_at_expands_when_args_set() {
        let mut env = Env::with_config(None, Some(vec!(
            String::from("one"),
            String::from("two"),
            String::from("three"),
        )), None, None).unwrap();

        assert_eq!(Word::DoubleQuoted(vec!(
            Param(Parameter::At),
        )).eval(&mut env), Ok(Fields::Many(vec!(
            Rc::new(String::from("one")),
            Rc::new(String::from("two")),
            Rc::new(String::from("three")),
        ))));
    }

    #[test]
    fn test_eval_word_double_quoted_param_at_expands_when_args_set_and_concats_with_rest() {
        let mut env = Env::with_config(None, Some(vec!(
            String::from("one"),
            String::from("two"),
            String::from("three"),
        )), None, None).unwrap();

        assert_eq!(Word::DoubleQuoted(vec!(
            Literal(String::from("foo")),
            Param(Parameter::At),
            Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Many(vec!(
            Rc::new(String::from("fooone")),
            Rc::new(String::from("two")),
            Rc::new(String::from("threebar")),
        ))));
    }

    #[test]
    fn test_eval_word_double_quoted_param_at_expands_to_nothing_when_args_not_set_and_concats_with_rest() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Literal(String::from("foo")),
            Param(Parameter::At),
            Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foobar")))));
    }

    #[test]
    fn test_eval_word_double_quoted_param_star_expands_but_joined_by_ifs() {
        let mut env = Env::with_config(None, Some(vec!(
            String::from("one"),
            String::from("two"),
            String::from("three"),
        )), None, None).unwrap();

        assert_eq!(Word::DoubleQuoted(vec!(
            Literal(String::from("foo")),
            Param(Parameter::Star),
            Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("fooone two threebar")))));

        env.set_var(String::from("IFS"), Rc::new(String::from("!")));
        assert_eq!(Word::DoubleQuoted(vec!(
            Literal(String::from("foo")),
            Param(Parameter::Star),
            Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("fooone!two!threebar")))));

        env.set_var(String::from("IFS"), Rc::new(String::new()));
        assert_eq!(Word::DoubleQuoted(vec!(
            Literal(String::from("foo")),
            Param(Parameter::Star),
            Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("fooonetwothreebar")))));
    }

    #[test]
    fn test_eval_word_concat_joins_all_inner_words() {
        let mut env = Env::new().unwrap();
        env.set_var(String::from("var"), Rc::new(String::from("foobar")));

        assert_eq!(Concat(vec!(
            lit("hello"),
            Word::Simple(Box::new(Param(Parameter::Var(String::from("var"))))),
            lit("world"),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("hellofoobarworld")))));
    }

    #[test]
    fn test_eval_word_concat_if_inner_word_expands_to_many_fields_they_are_joined_with_those_before_and_after()
    {
        let mut env = Env::new().unwrap();
        env.set_var(String::from("var"), Rc::new(String::from("foo bar baz")));

        assert_eq!(Concat(vec!(
            lit("hello"),
            Word::Simple(Box::new(Param(Parameter::Var(String::from("var"))))),
            lit("world"),
        )).eval(&mut env), Ok(Fields::Many(vec!(
            Rc::new(String::from("hellofoo")),
            Rc::new(String::from("bar")),
            Rc::new(String::from("bazworld")),
        ))));
    }

    #[test]
    fn test_eval_word_concat_should_not_expand_tilde_which_is_not_at_start() {
        let mut env = Env::new().unwrap();
        assert_eq!(Concat(vec!(
            lit("foo"),
            Word::Simple(Box::new(Tilde)),
            lit("bar"),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foo~bar")))));
        assert_eq!(Concat(vec!(
            lit("foo"),
            Word::Simple(Box::new(Tilde)),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foo~")))));
    }

    #[test]
    fn test_eval_word_concat_param_at_expands_when_args_set() {
        let mut env = Env::with_config(None, Some(vec!(
            String::from("one"),
            String::from("two"),
            String::from("three"),
        )), None, None).unwrap();

        assert_eq!(Concat(vec!(
            Word::Simple(Box::new(Param(Parameter::At))),
        )).eval(&mut env), Ok(Fields::Many(vec!(
            Rc::new(String::from("one")),
            Rc::new(String::from("two")),
            Rc::new(String::from("three")),
        ))));
    }

    #[test]
    fn test_eval_word_concat_param_at_expands_when_args_set_and_concats_with_rest() {
        let mut env = Env::with_config(None, Some(vec!(
            String::from("one"),
            String::from("two"),
            String::from("three"),
        )), None, None).unwrap();

        assert_eq!(Concat(vec!(
            lit("foo"),
            Word::Simple(Box::new(Param(Parameter::At))),
            lit("bar"),
        )).eval(&mut env), Ok(Fields::Many(vec!(
            Rc::new(String::from("fooone")),
            Rc::new(String::from("two")),
            Rc::new(String::from("threebar")),
        ))));
    }

    #[test]
    fn test_eval_word_concat_param_at_expands_to_nothing_when_args_not_set_and_concats_with_rest() {
        let mut env = Env::new().unwrap();
        assert_eq!(Concat(vec!(
            lit("foo"),
            Word::Simple(Box::new(Param(Parameter::At))),
            lit("bar"),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foobar")))));
    }

    #[test]
    fn test_eval_word_single_quoted_removes_quotes() {
        let value = String::from("hello world");
        let mut env = Env::new().unwrap();
        assert_eq!(single_quoted(&value).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_eval_word_double_quoted_removes_quotes() {
        let value = String::from("hello world");
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Literal(value.clone()),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_eval_word_escaped_quoted_removes_slash() {
        let value = String::from("&");
        let mut env = Env::new().unwrap();
        let word = Single(escaped(&value));
        assert_eq!(word.eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_eval_word_single_quoted_should_not_split_fields() {
        let value = String::from("hello world\nfoo\tbar");
        let mut env = Env::new().unwrap();
        assert_eq!(single_quoted(&value).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_eval_word_single_quoted_should_not_expand_anything() {
        let value = String::from("hello world\nfoo\tbar * baz ~");
        let mut env = Env::new().unwrap();
        assert_eq!(single_quoted(&value).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }
}
