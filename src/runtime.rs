//! This module defines a runtime envirnment capable of executing parsed shell commands.

use glob;
use libc;

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::convert::{From, Into};
use std::default::Default;
use std::error::Error;
use std::io::{self, Error as IoError, ErrorKind as IoErrorKind, Write};
use std::iter::{IntoIterator, Iterator};
use std::fmt;
use std::process::{self, Command, Stdio};
use std::rc::Rc;
use std::vec;

use void::Void;

// Apparently importing Redirect before Word causes an ICE, when linking
// to this crate, so this ordering is *very* crucial...
// 'assertion failed: bound_list_is_sorted(&bounds.projection_bounds)', ../src/librustc/middle/ty.rs:4028
use syntax::ast::{Arith, CompoundCommand, SimpleCommand, Parameter, ParameterSubstitution, Word, Redirect};
use syntax::ast::Command as AstCommand;

const EXIT_SUCCESS:            ExitStatus = ExitStatus::Code(0);
const EXIT_ERROR:              ExitStatus = ExitStatus::Code(1);
const EXIT_CMD_NOT_EXECUTABLE: ExitStatus = ExitStatus::Code(126);
const EXIT_CMD_NOT_FOUND:      ExitStatus = ExitStatus::Code(127);

const IFS_DEFAULT: &'static str = " \t\n";

/// A specialized `Result` type for shell runtime operations.
pub type Result<T> = ::std::result::Result<T, RuntimeError>;

/// An error which may arise while executing commands.
#[derive(Debug)]
pub enum RuntimeError {
    /// Any I/O error returned by the OS during execution.
    Io(IoError),
    /// Attempted to divide by zero in an arithmetic subsitution.
    DivideByZero,
    /// Attempted to raise to a negative power in an arithmetic subsitution.
    NegativeExponent,
    /// Attempted to assign a special parameter, e.g. `${!:-value}`.
    BadAssig(Parameter),
    /// Attempted to evaluate a null or unset parameter, i.e. `${var:?msg}`.
    EmptyParameter(Parameter, Rc<String>),
    /// Unable to find a command/function/builtin to execute.
    CommandNotFound(Rc<String>),
    /// Utility or script does not have executable permissions.
    CommandNotExecutable(Rc<String>),
    /// Runtime feature not currently supported.
    Unimplemented(&'static str),
}

impl Error for RuntimeError {
    fn description(&self) -> &str {
        match *self {
            RuntimeError::Io(ref e) => e.description(),
            RuntimeError::DivideByZero => "attempted to divide by zero",
            RuntimeError::NegativeExponent => "attempted to raise to a negative power",
            RuntimeError::BadAssig(_) => "attempted to assign a special parameter",
            RuntimeError::EmptyParameter(..) => "attempted to evaluate a null or unset parameter",
            RuntimeError::CommandNotFound(_) => "command not found",
            RuntimeError::CommandNotExecutable(_) => "command not executable",
            RuntimeError::Unimplemented(s) => s,
        }
    }

    fn cause(&self) -> Option<&Error> {
        match *self {
            RuntimeError::Io(ref e) => Some(e),

            RuntimeError::DivideByZero       |
            RuntimeError::NegativeExponent   |
            RuntimeError::BadAssig(_)        |
            RuntimeError::EmptyParameter(..) |
            RuntimeError::Unimplemented(_)   |
            RuntimeError::CommandNotFound(_) |
            RuntimeError::CommandNotExecutable(_) => None,
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RuntimeError::Io(ref e)        => write!(fmt, "{}", e),
            RuntimeError::Unimplemented(e) => write!(fmt, "{}", e),

            RuntimeError::DivideByZero     |
            RuntimeError::NegativeExponent => write!(fmt, "{}", self.description()),
            RuntimeError::CommandNotFound(ref c) => write!(fmt, "{}: command not found", c),
            RuntimeError::CommandNotExecutable(ref c) => write!(fmt, "{}: command not executable", c),
            RuntimeError::BadAssig(ref p) => write!(fmt, "{}: cannot assign in this way", p),
            RuntimeError::EmptyParameter(ref p, ref msg) => write!(fmt, "{}: {}", p, msg),
        }
    }
}

impl From<IoError> for RuntimeError {
    fn from(err: IoError) -> Self {
        RuntimeError::Io(err)
    }
}

/// Describes the result of a process after it has terminated.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum ExitStatus {
    /// Normal termination with an exit code.
    Code(i32),

    /// Termination by signal, with the signal number.
    ///
    /// Never generated on Windows.
    Signal(i32),
}

impl ExitStatus {
    /// Was termination successful? Signal termination not considered a success,
    /// and success is defined as a zero exit status.
    pub fn success(&self) -> bool { *self == EXIT_SUCCESS }
}

impl fmt::Display for ExitStatus {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ExitStatus::Code(code)   => write!(f, "exit code: {}", code),
            ExitStatus::Signal(code) => write!(f, "signal: {}", code),
        }
    }
}

impl From<process::ExitStatus> for ExitStatus {
    fn from(exit: process::ExitStatus) -> ExitStatus {
        #[cfg(unix)]
        fn get_signal(exit: process::ExitStatus) -> Option<i32> {
            ::std::os::unix::process::ExitStatusExt::signal(&exit)
        }

        #[cfg(windows)]
        fn get_signal(exit: process::ExitStatus) -> Option<i32> { None }

        match exit.code() {
            Some(code) => ExitStatus::Code(code),
            None => get_signal(exit).map_or(EXIT_ERROR, |s| ExitStatus::Signal(s)),
        }
    }
}

/// Represents the types of fields that may result from evaluating a `Word`.
/// It is important to maintain such distinctions because evaluating parameters
/// such as `$@` and `$*` have different behaviors in different contexts.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Fields {
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
            Fields::Single(ref s) => s.is_empty(),

            Fields::At(ref v)   |
            Fields::Star(ref v) |
            Fields::Many(ref v) => v.iter().all(|s| s.is_empty()),
        }
    }

    /// Joins all fields using a space.
    pub fn join(self) -> Rc<String> {
        match self {
            Fields::Single(s) => s,
            Fields::At(v)   |
            Fields::Star(v) |
            Fields::Many(v) => Rc::new(v.iter().map(|s| &***s).collect::<Vec<&str>>().join(" ")),
        }
    }
}

impl IntoIterator for Fields {
    type Item = Rc<String>;
    type IntoIter = vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Fields::Single(s) => vec!(s).into_iter(),
            Fields::At(v)   |
            Fields::Star(v) |
            Fields::Many(v) => v.into_iter(),
        }
    }
}

/// A shell environment containing any relevant variable, file descriptor, and other information.
pub struct Env<'a> {
    /// The current name of the shell/script/function executing.
    shell_name: Rc<String>,
    /// The current arguments of the shell/script/function.
    args: Vec<Rc<String>>,
    /// A mapping of all defined function names and executable bodies.
    /// The function bodies are stored as `Options` to properly distinguish functions
    /// that were explicitly unset and functions that are simply defined in a parent
    /// environment.
    functions: HashMap<String, Option<Rc<Box<Run>>>>,
    /// A mapping of variable names to their values.
    ///
    /// The values are stored as `Options` to properly distinguish variables that were
    /// explicitly unset and variables that are simply defined in a parent environment.
    /// The tupled boolean indicates if a variable should be exported to other commands.
    vars: HashMap<String, Option<(Rc<String>, bool)>>,
    /// The exit status of the last command that was executed.
    last_status: ExitStatus,
    /// A parent environment for looking up previously set values.
    parent_env: Option<&'a Env<'a>>,
}

impl<'a> Env<'a> {
    /// Creates a new default environment.
    /// See the docs for `Env::with_config` for more information.
    pub fn new() -> Self {
        Self::with_config(None, None, None)
    }

    /// Creates an environment using provided overrides, or data from the
    /// current process if the respective override is not provided.
    ///
    /// Unless otherwise specified, the environment's name will become
    /// the name of the current process (e.g. the 0th OS arg).
    ///
    /// Unless otherwise specified, all environment variables of the
    /// current process will be inherited as environment variables
    /// by any spawned commands.
    ///
    /// Note: Any data taken from the current process (e.g. environment
    /// variables) which is not valid Unicode will be ignored.
    pub fn with_config(name: Option<String>,
                       args: Option<Vec<String>>,
                       env: Option<Vec<(String, String)>>) -> Self
    {
        use ::std::env::{args_os, vars_os};

        let name = name.unwrap_or_else(|| {
            args_os().next().map(|s| s.to_str().unwrap_or("").to_string()).unwrap_or_default()
        });

        let args = args.map_or(Vec::new(), |args| args.into_iter().map(|s| Rc::new(s)).collect());

        let vars = env.map_or_else(|| {
            vars_os().map(|(k, v)| (k.into_string(), v.into_string()))
                .filter_map(|(k, v)| match (k,v) {
                    (Ok(k), Ok(v)) => Some((k, Some((Rc::new(v), true)))),
                    _ => None,
                }).collect()
        }, |pairs| pairs.into_iter().map(|(k,v)| (k, Some((Rc::new(v), true)))).collect());

        Env {
            shell_name: Rc::new(String::from(name)),
            args: args,
            functions: HashMap::new(),
            vars: vars,
            last_status: EXIT_SUCCESS,
            parent_env: None,
        }
    }

    /// Walks `self` and its entire chain of parent environments and evaluates a closure on each.
    ///
    /// If the closure evaluates a `Ok(Some(x))` value, then `Some(x)` is returned.
    /// If the closure evaluates a `Err(_)` value, then `None` is returned.
    /// If the closure evaluates a `Ok(None)` value, then the traversal continues.
    fn walk_parent_chain<'b, T, F>(&'b self, mut cond: F) -> Option<T>
        where F: FnMut(&'b Self) -> ::std::result::Result<Option<T>, ()>
    {
        let mut cur = self;
        loop {
            match cond(cur) {
                Err(()) => return None,
                Ok(Some(res)) => return Some(res),
                Ok(None) => match cur.parent_env {
                    Some(ref parent) => cur = *parent,
                    None => return None,
                },
            }
        }
    }
}

impl<'a> Default for Env<'a> {
    fn default() -> Self { Self::new() }
}

pub trait Environment {
    /// Create a new sub-environment using the current environment as its parent.
    ///
    /// Any changes which mutate the sub environment will only be reflected there,
    /// but any information not present in the sub-env will be looked up in the parent.
    fn sub_env<'a>(&'a self) -> Box<Environment + 'a>;
    /// Get the shell's current name.
    fn name(&self) -> Rc<String>;
    /// Get the value of some variable. The values of both shell-only
    /// variables will be looked up and returned.
    fn var(&self, name: &str) -> Option<Rc<String>>;
    /// Set the value of some variable (including environment variables).
    fn set_var(&mut self, name: String, val: Rc<String>);
    /// Indicates if a funciton is currently defined with a given name.
    fn has_function(&mut self, fn_name: &str) -> bool;
    /// Attempt to execute a function with a set of arguments if it has been defined.
    fn run_function(&mut self, fn_name: Rc<String>, args: Vec<Rc<String>>) -> Option<Result<ExitStatus>>;
    /// Define a function with some `Run`able body.
    fn set_function(&mut self, name: String, func: Box<Run>);
    /// Get the exit status of the previous command.
    fn last_status(&self) -> ExitStatus;
    /// Set the exit status of the previously run command.
    fn set_last_status(&mut self, status: ExitStatus);
    /// Get an argument at any index. Arguments are 1-indexed since the shell variable `$0`
    /// to the shell's name. Thus the first real argument starts at index 1.
    fn arg(&self, idx: usize) -> Option<Rc<String>>;
    /// Get the number of current arguments, NOT including the shell name.
    fn args_len(&self) -> usize;
    /// Get all current arguments as a vector.
    fn args(&self) -> &[Rc<String>];
    /// Get all current pairs of environment variables and their values.
    fn env(&self) -> Vec<(&str, &str)>;

    fn report_error(&mut self, err: RuntimeError) {
        write!(io::stderr(), "{}: {}", self.name(), err).ok();
    }
}

impl<'a> Environment for Env<'a> {
    fn sub_env<'b>(&'b self) -> Box<Environment + 'b> {
        Box::new(Env {
            shell_name: self.shell_name.clone(),
            args: self.args.clone(),

            functions: HashMap::new(),
            vars: HashMap::new(),
            last_status: self.last_status,
            parent_env: Some(self),
        })
    }

    fn name(&self) -> Rc<String> {
        self.shell_name.clone()
    }

    fn var(&self, name: &str) -> Option<Rc<String>> {
        self.walk_parent_chain(|cur| match cur.vars.get(name) {
            Some(&Some((ref s, _))) => Ok(Some(s.clone())), // found the var
            Some(&None) => Err(()), // var was unset, break the walk
            None => Ok(None), // neither set nor unset, keep walking
        })
    }

    fn set_var(&mut self, name: String, val: Rc<String>) {
        match self.vars.entry(name) {
            Entry::Vacant(entry) => {
                entry.insert(Some((val, false)));
            },
            Entry::Occupied(mut entry) => {
                let exported = entry.get().as_ref().map_or(false, |&(_, e)| e);
                entry.insert(Some((val, exported)));
            },
        }
    }

    fn has_function(&mut self, fn_name: &str) -> bool {
        self.walk_parent_chain(|cur| match cur.functions.get(fn_name) {
            Some(&Some(_)) => Ok(Some(())), // found the fn
            Some(&None) => Err(()), // fn was unset, break the walk
            None => Ok(None), // neither set nor unset, keep walking
        }).is_some()
    }

    fn run_function(&mut self, mut fn_name: Rc<String>, mut args: Vec<Rc<String>>)
        -> Option<Result<ExitStatus>>
    {
        use std::mem;

        let func = self.walk_parent_chain(|cur| match cur.functions.get(&*fn_name) {
            Some(&Some(ref body)) => Ok(Some(body.clone())), // found the fn
            Some(&None) => Err(()), // fn was unset, break the walk
            None => Ok(None), // neither set nor unset, keep walking
        });

        let func = match func {
            Some(f) => f,
            None => return None,
        };

        mem::swap(&mut self.shell_name, &mut fn_name);
        mem::swap(&mut self.args, &mut args);
        let ret = func.run(self);
        mem::swap(&mut self.args, &mut args);
        mem::swap(&mut self.shell_name, &mut fn_name);
        Some(ret)
    }

    fn set_function(&mut self, name: String, func: Box<Run>) {
        self.functions.insert(name, Some(Rc::new(func)));
    }

    fn last_status(&self) -> ExitStatus {
        self.last_status
    }

    fn set_last_status(&mut self, status: ExitStatus) {
        self.last_status = status;
    }

    fn arg(&self, idx: usize) -> Option<Rc<String>> {
        if idx == 0 {
            Some(self.name())
        } else {
            self.args.get(idx - 1).cloned()
        }
    }

    fn args_len(&self) -> usize {
        self.args.len()
    }

    fn args(&self) -> &[Rc<String>] {
        &self.args
    }

    fn env(&self) -> Vec<(&str, &str)> {
        let mut env = HashMap::new();
        self.walk_parent_chain(|cur| -> ::std::result::Result<Option<Void>, ()> {
            for (k,v) in cur.vars.iter().map(|(k,v)| (&**k, v)) {
                // Since we are traversing the parent chain "backwards" we
                // must be careful not to overwrite any variable with a
                // "previous" value from a parent environment.
                if !env.contains_key(k) { env.insert(k, v); }
            }
            Ok(None) // Force the traversal to walk the entire chain
        });

        env.into_iter().filter_map(|(k, v)| match v {
            &Some((ref v, true)) => Some((k, &***v)),
            &Some((_, false)) => None,
            &None => None,
        }).collect()
    }
}

impl Parameter {
    /// Evaluates a parameter in the context of some environment.
    ///
    /// Any fields as a result of evaluating `$@` or `$*` will not be
    /// split further. This is left for the caller to perform.
    pub fn eval(&self, env: &Environment) -> Option<Fields> {
        match *self {
            Parameter::At   => Some(Fields::At(  env.args().iter().cloned().collect())),
            Parameter::Star => Some(Fields::Star(env.args().iter().cloned().collect())),

            Parameter::Pound  => Some(Fields::Single(Rc::new(env.args_len().to_string()))),
            Parameter::Dollar => Some(Fields::Single(Rc::new(unsafe { libc::getpid() }.to_string()))),
            Parameter::Dash   => None,
            Parameter::Bang   => None, // FIXME: eventual job control would be nice

            Parameter::Question => Some(Fields::Single(Rc::new(match env.last_status() {
                ExitStatus::Code(c)   => c as u32,
                ExitStatus::Signal(c) => c as u32 + 128,
            }.to_string()))),

            Parameter::Positional(0) => Some(Fields::Single(env.name())),
            Parameter::Positional(p) => env.arg(p as usize).map(Fields::Single),
            Parameter::Var(ref var)  => env.var(var).map(Fields::Single),
        }
    }
}

impl ParameterSubstitution {
    /// Evaluates a parameter subsitution in the context of some environment.
    ///
    /// No field *splitting* will be performed, and is left for the caller to
    /// implement. However, multiple fields can occur if `$@` or $*` is evaluated.
    pub fn eval(&self, env: &mut Environment) -> Result<Fields> {
        use syntax::ast::ParameterSubstitution::*;

        let null_str   = Rc::new(String::new());
        let null_field = Fields::Single(null_str.clone());
        let match_opts = glob::MatchOptions {
            case_sensitive: true,
            require_literal_separator: false,
            require_literal_leading_dot: false,
        };

        fn remove_pattern<F>(param: &Parameter,
                             pat: &Option<Word>,
                             env: &mut Environment,
                             remove: F) -> Result<Option<Fields>>
            where F: Fn(Rc<String>, &glob::Pattern) -> Rc<String>
        {
            let map = |v: Vec<Rc<String>>, p| v.into_iter().map(|f| remove(f, &p)).collect();
            let param = param.eval(env);

            match *pat {
                None => Ok(param),
                Some(ref pat) => {
                    let pat = try!(pat.as_pattern(env));
                    Ok(param.map(|p| match p {
                        Fields::Single(s) => Fields::Single(remove(s, &pat)),

                        Fields::At(v)   => Fields::At(  map(v, pat)),
                        Fields::Star(v) => Fields::Star(map(v, pat)),
                        Fields::Many(v) => Fields::Many(map(v, pat)),
                    }))
                },
            }
        }

        // A macro that evaluates a parameter in some environment and immediately
        // returns the result as long as there is at least one non-empty field inside.
        // If all fields from the evaluated result are empty and the evaluation is
        // considered NON-strict, an empty vector is returned to the caller.
        macro_rules! check_param_subst {
            ($param:expr, $env:expr, $strict:expr) => {{
                if let Some(fields) = $param.eval($env) {
                    if !$strict && fields.is_null() {
                        return Ok(null_field);
                    } else {
                        return Ok(fields);
                    }
                }
            }}
        }

        let ret = match *self {
            Command(_) => unimplemented!(),

            Len(ref p) => Fields::Single(Rc::new(match p.eval(env) {
                None => String::from("0"),
                Some(Fields::Single(s)) => s.len().to_string(),

                Some(Fields::At(v))   |
                Some(Fields::Star(v)) => v.len().to_string(),

                // Evaluating a pure parameter should not be performing
                // field expansions, so this variant should never occur.
                Some(Fields::Many(_)) => unreachable!(),
            })),

            Arithmetic(ref a) => Fields::Single(Rc::new(match a {
                &Some(ref a) => try!(a.eval(env)).to_string(),
                &None => String::from("0"),
            })),

            Default(strict, ref p, ref default) => {
                check_param_subst!(p, env, strict);
                match *default {
                    Some(ref w) => try!(w.eval(env)),
                    None => null_field,
                }
            },

            Assign(strict, ref p, ref assig) => {
                check_param_subst!(p, env, strict);
                match p {
                    p@&Parameter::At       |
                    p@&Parameter::Star     |
                    p@&Parameter::Pound    |
                    p@&Parameter::Question |
                    p@&Parameter::Dash     |
                    p@&Parameter::Dollar   |
                    p@&Parameter::Bang     |
                    p@&Parameter::Positional(_) => return Err(RuntimeError::BadAssig(p.clone())),

                    &Parameter::Var(ref name) => {
                        let val = match *assig {
                            Some(ref w) => try!(w.eval(env)),
                            None => null_field,
                        };

                        env.set_var(name.clone(), val.clone().join());
                        val
                    },
                }
            },

            Error(strict, ref p, ref msg) => {
                check_param_subst!(p, env, strict);
                let msg = match *msg {
                    None => Rc::new(String::from("parameter null or not set")),
                    Some(ref w) => try!(w.eval(env)).join(),
                };

                return Err(RuntimeError::EmptyParameter(p.clone(), msg));
            },

            Alternative(strict, ref p, ref alt) => {
                let val = p.eval(env);
                if val.is_none() || (strict && val.unwrap().is_null()) {
                    return Ok(null_field);
                }

                match *alt {
                    Some(ref w) => try!(w.eval(env)),
                    None => null_field,
                }
            },

            RemoveSmallestSuffix(ref p, ref pat) => try!(remove_pattern(p, pat, env, |s, pat| {
                let len = s.len();
                for idx in 0..len {
                    let idx = len - idx - 1;
                    if pat.matches_with(&s[idx..], &match_opts) {
                        return Rc::new(String::from(&s[0..idx]));
                    }
                }
                s
            })).unwrap_or_else(|| null_field.clone()),

            RemoveLargestSuffix(ref p, ref pat) => try!(remove_pattern(p, pat, env, |s, pat| {
                let mut longest_start = None;
                let len = s.len();
                for idx in 0..len {
                    let idx = len - idx - 1;
                    if pat.matches_with(&s[idx..], &match_opts) {
                        longest_start = Some(idx);
                    }
                }

                match longest_start {
                    None => s,
                    Some(idx) => Rc::new(String::from(&s[0..idx])),
                }
            })).unwrap_or_else(|| null_field.clone()),

            RemoveSmallestPrefix(ref p, ref pat) => try!(remove_pattern(p, pat, env, |s, pat| {
                for idx in 0..s.len() {
                    if pat.matches_with(&s[0..idx], &match_opts) {
                        return Rc::new(String::from(&s[idx..]));
                    }
                }

                // Don't forget to check the entire string for a match
                if pat.matches_with(&s, &match_opts) {
                    null_str.clone()
                } else {
                    s
                }
            })).unwrap_or_else(|| null_field.clone()),

            RemoveLargestPrefix(ref p, ref pat) => try!(remove_pattern(p, pat, env, |s, pat| {
                if pat.matches_with(&s, &match_opts) {
                    return null_str.clone();
                }

                let mut longest_end = None;
                for idx in 0..s.len() {
                    if pat.matches_with(&s[0..idx], &match_opts) {
                        longest_end = Some(idx);
                    }
                }

                match longest_end {
                    None => s,
                    Some(idx) => Rc::new(String::from(&s[idx..])),
                }
            })).unwrap_or_else(|| null_field.clone()),
        };

        Ok(ret)
    }
}

impl Arith {
    /// Evaluates an arithmetic expression in the context of an environment.
    /// A mutable reference to the environment is needed since an arithmetic
    /// expression could mutate environment variables.
    pub fn eval(&self, env: &mut Environment) -> Result<isize> {
        use syntax::ast::Arith::*;

        let get_var = |env: &Environment, var| env.var(var).and_then(|s| s.parse().ok()).unwrap_or(0);

        let ret = match *self {
            Literal(lit) => lit,
            Var(ref var) => get_var(env, var),

            PostIncr(ref var) => {
                let val = get_var(env, var);
                env.set_var(var.clone(), Rc::new((val + 1).to_string()));
                val
            },

            PostDecr(ref var) => {
                let val = get_var(env, var);
                env.set_var(var.clone(), Rc::new((val - 1).to_string()));
                val
            },

            PreIncr(ref var) => {
                let val = get_var(env, var) + 1;
                env.set_var(var.clone(), Rc::new(val.to_string()));
                val
            },

            PreDecr(ref var) => {
                let val = get_var(env, var) - 1;
                env.set_var(var.clone(), Rc::new(val.to_string()));
                val
            },

            UnaryPlus(ref expr)  => try!(expr.eval(env)).abs(),
            UnaryMinus(ref expr) => -try!(expr.eval(env)),
            BitwiseNot(ref expr) => try!(expr.eval(env)) ^ !0,
            LogicalNot(ref expr) => if try!(expr.eval(env)) == 0 { 1 } else { 0 },

            Less(ref left, ref right)    => if try!(left.eval(env)) <  try!(right.eval(env)) { 1 } else { 0 },
            LessEq(ref left, ref right)  => if try!(left.eval(env)) <= try!(right.eval(env)) { 1 } else { 0 },
            Great(ref left, ref right)   => if try!(left.eval(env)) >  try!(right.eval(env)) { 1 } else { 0 },
            GreatEq(ref left, ref right) => if try!(left.eval(env)) >= try!(right.eval(env)) { 1 } else { 0 },
            Eq(ref left, ref right)      => if try!(left.eval(env)) == try!(right.eval(env)) { 1 } else { 0 },
            NotEq(ref left, ref right)   => if try!(left.eval(env)) != try!(right.eval(env)) { 1 } else { 0 },

            Pow(ref left, ref right) => {
                let right = try!(right.eval(env));
                if right.is_negative() {
                    env.set_last_status(EXIT_ERROR);
                    return Err(RuntimeError::NegativeExponent);
                } else {
                    try!(left.eval(env)).pow(right as u32)
                }
            },

            Div(ref left, ref right) => {
                let right = try!(right.eval(env));
                if right == 0 {
                    env.set_last_status(EXIT_ERROR);
                    return Err(RuntimeError::DivideByZero);
                } else {
                    try!(left.eval(env)) / right
                }
            },

            Modulo(ref left, ref right) => {
                let right = try!(right.eval(env));
                if right == 0 {
                    env.set_last_status(EXIT_ERROR);
                    return Err(RuntimeError::DivideByZero);
                } else {
                    try!(left.eval(env)) % right
                }
            },

            Mult(ref left, ref right)       => try!(left.eval(env)) *  try!(right.eval(env)),
            Add(ref left, ref right)        => try!(left.eval(env)) +  try!(right.eval(env)),
            Sub(ref left, ref right)        => try!(left.eval(env)) -  try!(right.eval(env)),
            ShiftLeft(ref left, ref right)  => try!(left.eval(env)) << try!(right.eval(env)),
            ShiftRight(ref left, ref right) => try!(left.eval(env)) >> try!(right.eval(env)),
            BitwiseAnd(ref left, ref right) => try!(left.eval(env)) &  try!(right.eval(env)),
            BitwiseXor(ref left, ref right) => try!(left.eval(env)) ^  try!(right.eval(env)),
            BitwiseOr(ref left, ref right)  => try!(left.eval(env)) |  try!(right.eval(env)),

            LogicalAnd(ref left, ref right) => if try!(left.eval(env)) != 0 {
                if try!(right.eval(env)) != 0 { 1 } else { 0 }
            } else {
                0
            },

            LogicalOr(ref left, ref right) => if try!(left.eval(env)) == 0 {
                if try!(right.eval(env)) != 0 { 1 } else { 0 }
            } else {
                1
            },

            Ternary(ref guard, ref thn, ref els) => if try!(guard.eval(env)) != 0 {
                try!(thn.eval(env))
            } else {
                try!(els.eval(env))
            },

            Assign(ref var, ref val) => {
                let val = try!(val.eval(env));
                env.set_var(var.clone(), Rc::new(val.to_string()));
                val
            },

            Sequence(ref exprs) => {
                let mut last = 0;
                for e in exprs.iter() {
                    last = try!(e.eval(env));
                }
                last
            },
        };

        Ok(ret)
    }
}

impl Word {
    /// Evaluates a word in a given environment and performs all expansions.
    ///
    /// Tilde, parameter, command substitution, and arithmetic expansions are
    /// performed first. All resulting fields are then further split based on
    /// the contents of the `IFS` variable (no splitting is performed if `IFS`
    /// is set to be the empty or null string). Finally, quotes and escaping
    /// backslashes are removed from the original word (unless they themselves
    /// have been quoted).
    pub fn eval(&self, env: &mut Environment) -> Result<Fields> {
        self.eval_with_config(env, true)
    }

    /// Evaluates a word in a given environment without doing field and pathname expansions.
    ///
    /// Tilde, parameter, command substitution, arithmetic expansions, and quote removals
    /// will be performed, however. In addition, if multiple fields arise as a result
    /// of evaluating `$@` or `$*`, the fields will be joined with a single space.
    pub fn eval_as_assignment(&self, env: &mut Environment) -> Result<Rc<String>> {
        match try!(self.eval_with_config(env, true, false)) {
            f@Fields::Single(_) |
            f@Fields::At(_)     |
            f@Fields::Many(_)   => Ok(f.join()),

            Fields::Star(v) => {
                let star = v.iter().map(|s| &***s).collect::<Vec<&str>>();
                let star = match env.var("IFS") {
                    Some(ref s) if s.is_empty() => star.concat(),
                    Some(s) => star.join(&s[0..1]),
                    None => star.join(" "),
                };
                Ok(Rc::new(star))
            },
        }
    }

    fn eval_with_config(&self,
                        env: &mut Environment,
                        expand_tilde: bool,
                        split_fields_further: bool) -> Result<Fields>
    {
        use syntax::ast::Word::*;

        /// Splits a vector of fields further based on the contents of the `IFS`
        /// variable (i.e. as long as it is non-empty). Any empty fields, original
        /// or otherwise created will be discarded.
        fn split_fields(words: Vec<Rc<String>>, env: &Environment) -> Vec<Rc<String>> {
            // If IFS is set but null, there is nothing left to split
            let ifs = env.var("IFS").unwrap_or_else(|| Rc::new(String::from(IFS_DEFAULT)));
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

        let maybe_split_fields = |fields, env: &mut Environment| {
            if !split_fields_further {
                return fields;
            }

            match fields {
                Fields::At(fs)   => Fields::At(split_fields(fs, env)),
                Fields::Star(fs) => Fields::Star(split_fields(fs, env)),
                Fields::Many(fs) => Fields::Many(split_fields(fs, env)),

                Fields::Single(f) => {
                    let mut fields = split_fields(vec!(f), env);
                    if fields.len() == 1 {
                        Fields::Single(fields.pop().unwrap())
                    } else {
                        Fields::Many(fields)
                    }
                },
            }
        };

        let null_field = Fields::Single(Rc::new(String::new()));

        let fields = match *self {
            Literal(ref s)      |
            SingleQuoted(ref s) |
            Escaped(ref s)      => Fields::Single(Rc::new(s.clone())),

            Star        => Fields::Single(Rc::new(String::from("*"))),
            Question    => Fields::Single(Rc::new(String::from("?"))),
            SquareOpen  => Fields::Single(Rc::new(String::from("]"))),
            SquareClose => Fields::Single(Rc::new(String::from("["))),

            Tilde => if expand_tilde {
                env.var("HOME").map_or(null_field, |f| Fields::Single(f))
            } else {
                Fields::Single(Rc::new(String::from("~")))
            },

            Subst(ref s) => maybe_split_fields(try!(s.eval(env)), env),
            Param(ref p) => maybe_split_fields(p.eval(env).unwrap_or(null_field), env),

            Concat(ref v) => {
                let mut fields: Vec<Rc<String>> = Vec::new();
                for w in v.iter() {
                    let mut iter = try!(w.eval_with_config(env, expand_tilde, split_fields_further)).into_iter();
                    match (fields.pop(), iter.next()) {
                       (Some(last), Some(next)) => {
                           let mut new = String::with_capacity(last.len() + next.len());
                           new.push_str(&last);
                           new.push_str(&next);
                           fields.push(Rc::new(new));
                       },
                       (Some(last), None) => fields.push(last),
                       (None, Some(next)) => fields.push(next),
                       (None, None)       => continue,
                    }

                    fields.extend(iter);
                }

                if fields.is_empty() {
                    null_field
                } else if fields.len() == 1 {
                    Fields::Single(fields.pop().unwrap())
                } else {
                    Fields::Many(fields)
                }
            },

            DoubleQuoted(ref v) => {
                let mut fields = Vec::new();
                let mut cur_field = String::new();

                for w in v.iter() {
                    // Make sure we are NOT doing any tilde expanions for further field splitting
                    match (try!(w.eval_with_config(env, false, false)), w) {
                        (Fields::Single(s), _) => cur_field.push_str(&s),

                        // Any fields generated by $@ must be maintained, however, the first and last
                        // fields of $@ should be concatenated to whatever comes before/after them.
                        //
                        // Although nested `DoubleQuoted` words aren't quite "well-formed", evaluating
                        // inner `DoubleQuoted` words should behave similar as if the inner wrapper
                        // wasn't there. Namely, any fields the inner `DoubleQuoted` generates should
                        // be preserved, similar to evaluating $@.
                        (Fields::Many(v), &Word::DoubleQuoted(_)) |
                        (Fields::At(v), _) => {
                            // According to the POSIX spec, if $@ is empty it should generate NO fields
                            // even when within double quotes.
                            if !v.is_empty() {
                                let mut iter = v.into_iter();
                                if let Some(first) = iter.next() {
                                    cur_field.push_str(&first);
                                }

                                fields.push(Rc::new(cur_field));

                                let mut last = None;
                                for next in iter {
                                    fields.extend(last.take());
                                    last = Some(next);
                                }
                                cur_field = last.map(|s| String::from(&**s)).unwrap_or_default();
                            }
                        },

                        (Fields::Star(v), _) => {
                            let star = v.iter().map(|s| &***s).collect::<Vec<&str>>();
                            let star = match env.var("IFS") {
                                Some(ref s) if s.is_empty() => star.concat(),
                                Some(s) => star.join(&s[0..1]),
                                None => star.join(" "),
                            };
                            cur_field.push_str(&star);
                        },

                        // Having a `Concat` word within a `DoubleQuoted` word isn't particularly
                        // "well-formed", but we will attempt to gracefully handle the situation.
                        // We'll leave it up to the caller to ensure well-formedness if they don't
                        // want inconsistent results
                        (Fields::Many(v), &Word::Concat(_)) => {
                            let concat = v.iter().map(|s| &***s).collect::<Vec<&str>>().concat();
                            cur_field.push_str(&concat);
                        },

                        // Since we should have indicated we do NOT want field splitting,
                        // the following word variants should all yield `Single` fields (or at least
                        // a specific `Star` or `At` field type for parameter{s, substitutions}).
                        (Fields::Many(_), &Word::Literal(_))      |
                        (Fields::Many(_), &Word::SingleQuoted(_)) |
                        (Fields::Many(_), &Word::Escaped(_))      |
                        (Fields::Many(_), &Word::Star)            |
                        (Fields::Many(_), &Word::Question)        |
                        (Fields::Many(_), &Word::SquareOpen)      |
                        (Fields::Many(_), &Word::SquareClose)     |
                        (Fields::Many(_), &Word::Tilde)           |
                        (Fields::Many(_), &Word::Subst(_))        |
                        (Fields::Many(_), &Word::Param(_))        => unreachable!(),
                    }
                }

                // The only way our current buffer can be empty is if the double quotes
                // were empty, OR the last field of a $@ expansion was an empty field too.
                // Either way, we should preserve the empty field, because we need to either
                // return something (if the double quotes body is empty), or we need to
                // preserve all fields generated by $@ (even empty).
                fields.push(Rc::new(cur_field));

                // Make sure we return before doing any pathname expansions.
                return Ok(if fields.is_empty() {
                    null_field
                } else if fields.len() == 1 {
                    Fields::Single(fields.pop().unwrap())
                } else {
                    Fields::Many(fields)
                });
            }
        };

        Ok(fields)
    }

    pub fn as_pattern(&self, env: &mut Environment) -> Result<glob::Pattern>
    {
        unimplemented!()
    }
}

/// An interface for anything that can be executed within an `Environment`.
pub trait Run {
    /// Executes `self` in the provided environment.
    fn run(&self, env: &mut Environment) -> Result<ExitStatus>;
}

impl<'a, T: Run + ?Sized> Run for &'a T {
    fn run(&self, env: &mut Environment) -> Result<ExitStatus> { (**self).run(env) }
}

impl Run for SimpleCommand {
    fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
        if self.cmd.is_none() {
            // Any redirects set for this command have already been touched
            for &(ref var, ref val) in self.vars.iter() {
                if let Some(val) = val.as_ref() {
                    let val = try!(val.eval_as_assignment(env));
                    env.set_var(var.clone(), val);
                }
            }
            let exit = EXIT_SUCCESS;
            env.set_last_status(exit);
            return Ok(exit);
        }

        let &(ref cmd, ref args) = self.cmd.as_ref().unwrap();

        // bash and zsh just grab first field of an expansion
        let cmd_name = try!(cmd.eval(env)).into_iter().next();
        let cmd_name = match cmd_name {
            Some(exe) => exe,
            None => {
                env.set_last_status(EXIT_CMD_NOT_FOUND);
                return Err(RuntimeError::CommandNotFound(Rc::new(String::new())));
            },
        };

        let cmd_args = {
            let mut cmd_args = Vec::new();
            for arg in args.iter() {
                cmd_args.extend(try!(arg.eval(env)))
            }
            cmd_args
        };

        if !cmd_name.contains('/') && env.has_function(&cmd_name) {
            match env.run_function(cmd_name.clone(), cmd_args) {
                Some(ret) => return ret,
                None => {
                    env.set_last_status(EXIT_CMD_NOT_FOUND);
                    return Err(RuntimeError::CommandNotFound(cmd_name));
                }
            }
        }

        let mut cmd = Command::new(&*cmd_name);
        for arg in cmd_args {
            cmd.arg(&*arg);
        }

        // FIXME: use appropriate redirects
        cmd.stdin(Stdio::inherit())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit());

        // First inherit all default ENV variables
        for (var, val) in env.env() {
            cmd.env(var, val);
        }

        // Then do any local insertions/overrides
        for &(ref var, ref val) in self.vars.iter() {
            if let &Some(ref w) = val {
                match try!(w.eval(env)) {
                    Fields::Single(s) => cmd.env(var, &*s),
                    f@Fields::At(_)   |
                    f@Fields::Star(_) |
                    f@Fields::Many(_) => cmd.env(var, &*f.join()),
                };
            }
        }

        match cmd.status() {
            Err(e) => {
                let (exit, err) = if IoErrorKind::NotFound == e.kind() {
                    (EXIT_CMD_NOT_FOUND, RuntimeError::CommandNotFound(cmd_name))
                } else if Some(libc::ENOEXEC) == e.raw_os_error() {
                    (EXIT_CMD_NOT_EXECUTABLE, RuntimeError::CommandNotExecutable(cmd_name))
                } else {
                    (EXIT_ERROR, e.into())
                };
                env.set_last_status(exit);
                return Err(err);
            },

            Ok(exit) => {
                let exit = exit.into();
                env.set_last_status(exit);
                Ok(exit)
            }
        }
    }
}

impl Run for AstCommand {
    fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
        let exit = match *self {
            AstCommand::And(ref first, ref second) => {
                let exit = try!(first.run(env));
                if exit.success() { try!(second.run(env)) } else { exit }
            },

            AstCommand::Or(ref first, ref second) => {
                let exit = try!(first.run(env));
                if exit.success() { exit } else { try!(second.run(env)) }
            },

            AstCommand::Pipe(bool, ref cmds) => unimplemented!(),

            AstCommand::Job(_) => {
                // FIXME: eventual job control would be nice
                env.set_last_status(EXIT_ERROR);
                return Err(RuntimeError::Unimplemented("job control is not currently supported"));
            },

            AstCommand::Function(ref name, ref cmd) => {
                env.set_function(name.clone(), cmd.clone());
                EXIT_SUCCESS
            },

            AstCommand::Compound(ref cmd, ref redirects) => {
                try!(cmd.run(env))
            },

            AstCommand::Simple(ref cmd) => try!(cmd.run(env)),
        };

        env.set_last_status(exit);
        Ok(exit)
    }
}

impl Run for CompoundCommand {
    fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
        use syntax::ast::CompoundCommand::*;

        let exit = match *self {
            Brace(ref cmds) => try!(cmds.run(env)),

            While(ref guard, ref body) => {
                let mut exit = EXIT_SUCCESS;
                while try!(guard.run(env)).success() {
                    exit = try!(body.run(env))
                }
                exit
            },

            Until(ref guard, ref body) => {
                let mut exit = EXIT_SUCCESS;
                while ! try!(guard.run(env)).success() {
                    exit = try!(body.run(env))
                }
                exit
            },

            If(ref branches, ref els) => if branches.is_empty() {
                // An `If` AST node without any branches (conditional guards)
                // isn't really a valid instantiation, but we'll just
                // pretend it was an unsuccessful command (which it sort of is).
                EXIT_ERROR
            } else {
                let mut exit = None;
                for &(ref guard, ref body) in branches.iter() {
                    if try!(guard.run(env)).success() {
                        exit = Some(try!(body.run(env)));
                        break;
                    }
                }

                let exit = match exit {
                    Some(e) => e,
                    None => try!(els.as_ref().map_or(Ok(EXIT_SUCCESS), |els| els.run(env))),
                };
                env.set_last_status(exit);
                exit
            },

            Subshell(ref body) => try!(body.run(&mut *env.sub_env())),

            For(ref var, ref in_words, ref body) => {
                let mut exit = EXIT_SUCCESS;
                let values = match *in_words {
                    Some(ref words) => {
                        let mut values = Vec::with_capacity(words.len());
                        for w in words {
                            values.extend(try!(w.eval(env)).into_iter());
                        }
                        values
                    },
                    None => env.args().iter().cloned().collect(),
                };

                for val in values {
                    env.set_var(var.clone(), val);
                    exit = try!(body.run(env));
                }
                exit
            },


            Case(ref word, ref arms) => {
                let match_opts = glob::MatchOptions {
                    case_sensitive: true,
                    require_literal_separator: false,
                    require_literal_leading_dot: false,
                };

                let word = try!(word.eval_with_config(env, true, false)).join();

                let mut exit = EXIT_SUCCESS;
                for &(ref pats, ref body) in arms.iter() {
                    for pat in pats {
                        if try!(pat.as_pattern(env)).matches_with(&word, &match_opts) {
                            exit = try!(body.run(env));
                            break;
                        }
                    }
                }
                exit
            },
        };

        env.set_last_status(exit);
        Ok(exit)
    }
}

impl Run for [AstCommand] {
    fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
        let mut exit = EXIT_SUCCESS;
        for c in self.iter() {
            exit = try!(c.run(env))
        }
        env.set_last_status(exit);
        Ok(exit)
    }
}
