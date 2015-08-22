//! This module defines a runtime envirnment capable of executing parsed shell commands.

use glob;
use libc;

use std::borrow::Cow;
use std::collections::HashMap;
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

const COW_STR_EMPTY: Cow<'static, str> = Cow::Borrowed("");
const NULL_FIELD: Fields<'static> = Fields::Single(COW_STR_EMPTY);
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
    EmptyParameter(Parameter, String),
    /// Unable to find a command/function/builtin to execute.
    CommandNotFound(String),
    /// Utility or script does not have executable permissions.
    CommandNotExecutable(String),
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
pub enum Fields<'a> {
    /// A single field.
    Single(Cow<'a, str>),
    /// Any number of fields resulting from evaluating the `$@` special parameter.
    At(Vec<Cow<'a, str>>),
    /// Any number of fields resulting from evaluating the `$*` special parameter.
    Star(Vec<Cow<'a, str>>),
    /// A non-zero number of fields that do not have any special meaning.
    Many(Vec<Cow<'a, str>>),
}

impl<'a> Fields<'a> {
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

    /// Converts all internal Cow strings into owned ones
    pub fn into_owned<'b>(self) -> Fields<'b> {
        let map = |v: Vec<Cow<str>>| v.into_iter().map(|s| s.into_owned().into()).collect();

        match self {
            Fields::Single(s) => Fields::Single(s.into_owned().into()),
            Fields::At(v)   => Fields::At(  map(v)),
            Fields::Star(v) => Fields::Star(map(v)),
            Fields::Many(v) => Fields::Many(map(v)),
        }
    }

    /// Joins all fields using a space.
    pub fn join(self) -> String {
        match self {
            Fields::Single(s) => s.into_owned(),
            Fields::At(v)   |
            Fields::Star(v) |
            Fields::Many(v) => v.join(" "),
        }
    }
}

impl<'a> IntoIterator for Fields<'a> {
    type Item = Cow<'a, str>;
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

/// A helper struct for selectively configuring the creation of a new `Env`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct EnvConfig<'a> {
    /// The name of the shell/script currently executing.
    pub name: Option<&'a str>,
    /// Any arguments the current environment was invoked with (e.g. script or function)
    pub args: Option<Vec<&'a str>>,
    /// Any environment variables the environment should start out with.
    pub env: Option<Vec<(String, String)>>,
}

impl<'a> Default for EnvConfig<'a> {
    fn default() -> Self {
        EnvConfig {
            name: None,
            args: None,
            env: None,
        }
    }
}

/// A shell environment containing any relevant variable, file descriptor, and other information.
pub struct Env<'a> {
    shell_name: Cow<'a, str>,
    args: Vec<Cow<'a, str>>,
    functions: HashMap<String, Rc<Box<Run>>>,
    env: HashMap<String, String>,
    vars: HashMap<String, String>,
    last_status: ExitStatus,
    parent_env: Option<&'a Env<'a>>,
}

impl<'a> Env<'a> {
    /// Creates a new default environment.
    /// See the docs for `Env::with_config` for more information.
    pub fn new() -> Self {
        Self::with_config(Default::default())
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
    pub fn with_config(cfg: EnvConfig<'a>) -> Self {
        use ::std::env::{args_os, vars_os};

        let name = cfg.name.map_or_else(
            || args_os().next().map_or(String::new(), |s| s.to_str().unwrap_or("").to_string()),
            |n| n.to_string()
        );

        let args = cfg.args.map(|args| args.into_iter().map(|s| s.into()).collect()).unwrap_or_default();

        let env = cfg.env.map_or_else(|| {
            vars_os().map(|(k, v)| (k.into_string(), v.into_string()))
                .filter_map(|(k, v)| match (k,v) {
                    (Ok(k), Ok(v)) => Some((k,v)),
                    _ => None,
                }).collect()
        }, |pairs| pairs.into_iter().collect());

        Env {
            shell_name: name.into(),
            args: args,
            env: env,
            functions: HashMap::new(),
            vars: HashMap::new(),
            last_status: EXIT_SUCCESS,
            parent_env: None,
        }
    }

    /// Walks `self` and its entire chain of parent environments and
    /// evaluates a closure on each. If the closure evaluates a `Some(_)`
    /// the traversal is terminated early.
    fn walk_parent_chain<'b, T, F>(&'b self, mut cond: F) -> Option<T>
        where F: FnMut(&'b Self) -> Option<T>
    {
        let mut cur = self;
        loop {
            match cond(cur) {
                Some(res) => return Some(res),
                None => match cur.parent_env {
                    Some(ref parent) => cur = *parent,
                    None => return None,
                }
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
    fn name(&self) -> &str;
    /// Get the value of some variable. The values of both shell-only
    /// variables will be looked up and returned.
    fn var(&self, name: &str) -> Option<&str>;
    /// Set the value of some variable (including environment variables).
    fn set_var(&mut self, name: String, val: String);
    /// Indicates if a funciton is currently defined with a given name.
    fn has_function(&mut self, fn_name: &str) -> bool;
    /// Attempt to execute a function with a set of arguments if it has been defined.
    fn run_function(&mut self, fn_name: &str, args: &[&str]) -> Option<Result<ExitStatus>>;
    /// Define a function with some `Run`able body.
    fn set_function(&mut self, name: String, func: Box<Run>);
    /// Get the exit status of the previous command.
    fn last_status(&self) -> ExitStatus;
    /// Set the exit status of the previously run command.
    fn set_last_status(&mut self, status: ExitStatus);
    /// Get an argument at any index. Arguments are 1-indexed since the shell variable `$0`
    /// to the shell's name. Thus the first real argument starts at index 1.
    fn arg(&self, idx: usize) -> Option<&str>;
    /// Get the number of current arguments, NOT including the shell name.
    fn args_len(&self) -> usize;
    /// Get all current arguments as a vector.
    fn args(&self) -> Vec<&str>;
    /// Get all current pairs of environment variables and their values.
    fn env(&self) -> Vec<(&str, &str)>;

    fn report_error(&mut self, err: RuntimeError) {
        write!(io::stderr(), "{}: {}", self.name(), err).ok();
    }
}

impl<'a> Environment for Env<'a> {
    fn sub_env<'b>(&'b self) -> Box<Environment + 'b> {
        Box::new(Env {
            shell_name: (&*self.shell_name).into(),
            args: self.args.iter().map(|s| (&**s).into()).collect(),

            env: HashMap::new(),
            functions: HashMap::new(),
            vars: HashMap::new(),
            last_status: self.last_status,
            parent_env: Some(self),
        })
    }

    fn name(&self) -> &str {
        &self.shell_name
    }

    fn var(&self, name: &str) -> Option<&str> {
        self.walk_parent_chain(|cur| {
            cur.env.get(name).or_else(|| cur.vars.get(name)).map(|s| &**s)
        })
    }

    fn set_var(&mut self, name: String, val: String) {
        if self.env.contains_key(&name) {
            self.env.insert(name, val);
        } else {
            self.vars.insert(name, val);
        }
    }

    fn has_function(&mut self, fn_name: &str) -> bool {
        self.walk_parent_chain(|cur| {
            if cur.functions.contains_key(fn_name) { Some(()) } else { None }
        }).is_some()
    }

    fn run_function(&mut self, fn_name: &str, args: &[&str]) -> Option<Result<ExitStatus>> {
        use std::mem;

        let func = match self.walk_parent_chain(|cur| cur.functions.get(fn_name).cloned()) {
            Some(f) => f,
            None => return None,
        };

        // Since functions run in the same environment as they are called in we
        // can't get away with creating a sub environment here, since any
        // changes the function body may make will be lost when that sub env
        // goes away. Thus we could try temporarily swapping our own args with
        // the new ones until the body executes and then swap them back.
        // Unfortunately the compiler won't let us do that because `self` and
        // `args` have different lifetimes, and we could theoretically forget
        // to swap them back and cause nasty memory bugs. But, since we know
        // better, we'll pretend their lifetimes at the same and get away with
        // our hack.
        //
        // Of course we can always take a performance hit and clone the provided
        // arguments, which the compiler will happily accept, but where is the
        // fun in that?
        let args: Vec<Cow<str>> = args.iter().map(|&s| s.into()).collect();
        unsafe {
            let mut fn_name: Cow<'a, str> = mem::transmute(Cow::Borrowed(fn_name));
            let mut args: Vec<Cow<'a, str>> = mem::transmute(args);
            mem::swap(&mut self.shell_name, &mut fn_name);
            mem::swap(&mut self.args, &mut args);
            let ret = func.run(self);
            mem::swap(&mut self.args, &mut args);
            mem::swap(&mut self.shell_name, &mut fn_name);
            Some(ret)
        }
    }

    fn set_function(&mut self, name: String, func: Box<Run>) {
        self.functions.insert(name, Rc::new(func));
    }

    fn last_status(&self) -> ExitStatus {
        self.last_status
    }

    fn set_last_status(&mut self, status: ExitStatus) {
        self.last_status = status;
    }

    fn arg(&self, idx: usize) -> Option<&str> {
        if idx == 0 {
            Some(self.name())
        } else {
            self.args.get(idx - 1).map(|s| &**s)
        }
    }

    fn args_len(&self) -> usize {
        self.args.len()
    }

    fn args(&self) -> Vec<&str> {
        self.args.iter().map(|s| &**s).collect()
    }

    fn env(&self) -> Vec<(&str, &str)> {
        let mut env = HashMap::new();
        self.walk_parent_chain(|cur| -> Option<Void> {
            for (k,v) in cur.env.iter().map(|(k,v)| (&**k, &**v)) {
                // Since we are traversing the parent chain "backwards" we
                // must be careful not to overwrite any variable with a
                // "previous" value from a parent environment.
                if !env.contains_key(k) { env.insert(k, v); }
            }
            None // Force the traversal to walk the entire chain
        });
        env.into_iter().collect()
    }
}

impl Parameter {
    /// Evaluates a parameter in the context of some environment.
    ///
    /// Any fields as a result of evaluating `$@` or `$*` will not be
    /// split further. This is left for the caller to perform.
    pub fn eval<'a>(&self, env: &'a Environment) -> Option<Fields<'a>> {
        match *self {
            Parameter::At   => Some(Fields::At(  env.args().into_iter().map(|s| s.into()).collect())),
            Parameter::Star => Some(Fields::Star(env.args().into_iter().map(|s| s.into()).collect())),

            Parameter::Pound  => Some(Fields::Single(env.args_len().to_string().into())),
            Parameter::Dollar => Some(Fields::Single(unsafe { libc::getpid() }.to_string().into())),
            Parameter::Dash   => None,
            Parameter::Bang   => None, // FIXME: eventual job control would be nice

            Parameter::Question => Some(Fields::Single(match env.last_status() {
                ExitStatus::Code(c)   => c as u32,
                ExitStatus::Signal(c) => c as u32 + 128,
            }.to_string().into())),

            Parameter::Positional(0) => Some(Fields::Single(env.name().into())),
            Parameter::Positional(p) => env.arg(p as usize).map(|s| Fields::Single(s.into())),
            Parameter::Var(ref var)  => env.var(var).map(|s| Fields::Single(s.into())),
        }
    }
}

impl ParameterSubstitution {
    /// Evaluates a parameter subsitution in the context of some environment.
    ///
    /// No field *splitting* will be performed, and is left for the caller to
    /// implement. However, multiple fields can occur if `$@` or $*` is evaluated.
    pub fn eval<'a>(&'a self, env: &'a mut Environment) -> Result<Fields<'a>> {
        use syntax::ast::ParameterSubstitution::*;

        let match_opts = glob::MatchOptions {
            case_sensitive: true,
            require_literal_separator: false,
            require_literal_leading_dot: false,
        };

        fn remove_pattern<'a, F>(param: &Parameter,
                                 pat: &Option<Word>,
                                 env: &'a mut Environment,
                                 remove: F) -> Result<Fields<'a>>
            where F: Fn(String, &glob::Pattern) -> String
        {
            let map = |vec: Vec<Cow<str>>, pat: &Word, env| -> Result<Vec<Cow<str>>> {
                // We are forced to clone the parameter's value here since evaluating
                // the pattern may mutate the environment.
                let pat = try!(pat.as_pattern(env));
                Ok(vec.into_iter().map(|field| remove(field.into_owned(), &pat).into()).collect())
            };

            let ret = match *pat {
                None => param.eval(env).unwrap_or(NULL_FIELD),
                Some(ref pat) => match param.eval(env).unwrap_or(NULL_FIELD).into_owned() {
                    Fields::Single(s) => Fields::Single(
                        remove(s.into_owned(), &try!(pat.as_pattern(env))).into()
                    ),

                    Fields::At(v)   => Fields::At(  try!(map(v, pat, env))),
                    Fields::Star(v) => Fields::Star(try!(map(v, pat, env))),
                    Fields::Many(v) => Fields::Many(try!(map(v, pat, env))),
                }
            };

            Ok(ret)
        }

        // A macro that evaluates a parameter in some environment and immediately
        // returns the result as long as there is at least one non-empty field inside.
        // If all fields from the evaluated result are empty and the evaluation is
        // considered NON-strict, an empty vector is returned to the caller.
        macro_rules! check_param_subst {
            ($param:expr, $env:expr, $strict:expr) => {{
                // FIXME: unfortunately I wasn't able to find a way to
                // make the borrow of `env` due to evaluating the parameter
                // NOT last the entire match arm (which makes it impossible
                // to evaluate the associated word since it requires &mut env).
                // Thus we're forced to clone the evaluated string to appease
                // the borrow checker. Hopefully the eventual non-lexical
                // borrows will fix the problem...

                let fields: Option<Fields> = $param.eval($env).map(|f| f.into_owned());
                if let Some(p) = fields {
                    if !$strict && p.is_null() {
                        return Ok(NULL_FIELD);
                    } else {
                        return Ok(p);
                    }
                }
            }}
        }

        let ret = match *self {
            Command(_) => unimplemented!(),

            Len(ref p) => Fields::Single(match p.eval(env) {
                None => "0".into(),
                Some(Fields::Single(s)) => s.len().to_string().into(),

                Some(Fields::At(v))   |
                Some(Fields::Star(v)) => v.len().to_string().into(),

                // Evaluating a pure parameter should not be performing
                // field expansions, so this variant should never occur.
                Some(Fields::Many(_)) => unreachable!(),
            }),

            Arithmetic(ref a) => Fields::Single(match a {
                &Some(ref a) => try!(a.eval(env)).to_string().into(),
                &None => "0".into(),
            }),

            Default(strict, ref p, ref default) => {
                check_param_subst!(p, env, strict);
                match *default {
                    Some(ref w) => try!(w.eval(env)),
                    None => NULL_FIELD,
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
                            Some(ref w) => try!(w.eval_as_assignment(env)),
                            None => String::new(),
                        };

                        env.set_var(name.clone(), val.clone());
                        Fields::Single(val.into())
                    },
                }
            },

            Error(strict, ref p, ref msg) => {
                check_param_subst!(p, env, strict);
                let msg = match *msg {
                    None => String::from("parameter null or not set"),
                    Some(ref w) => try!(w.eval(env)).join(),
                };

                return Err(RuntimeError::EmptyParameter(p.clone(), msg));
            },

            Alternative(strict, ref p, ref alt) => {
                {
                    let val = p.eval(env);
                    if val.is_none() || (strict && val.unwrap().is_null()) {
                        return Ok(NULL_FIELD);
                    }
                }

                match *alt {
                    Some(ref w) => try!(w.eval(env)),
                    None => NULL_FIELD,
                }
            },

            RemoveSmallestSuffix(ref p, ref pat) => try!(remove_pattern(p, pat, env, |s, pat| {
                let len = s.len();
                for idx in 0..len {
                    let idx = len - idx - 1;
                    if pat.matches_with(&s[idx..], &match_opts) {
                        return String::from(&s[0..idx]);
                    }
                }
                s
            })),

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
                    Some(idx) => String::from(&s[0..idx]),
                }
            })),

            RemoveSmallestPrefix(ref p, ref pat) => try!(remove_pattern(p, pat, env, |s, pat| {
                for idx in 0..s.len() {
                    if pat.matches_with(&s[0..idx], &match_opts) {
                        return String::from(&s[idx..]);
                    }
                }

                // Don't forget to check the entire string for a match
                if pat.matches_with(&s, &match_opts) {
                    String::new()
                } else {
                    s
                }
            })),

            RemoveLargestPrefix(ref p, ref pat) => try!(remove_pattern(p, pat, env, |s, pat| {
                if pat.matches_with(&s, &match_opts) {
                    return String::new();
                }

                let mut longest_end = None;
                for idx in 0..s.len() {
                    if pat.matches_with(&s[0..idx], &match_opts) {
                        longest_end = Some(idx);
                    }
                }

                match longest_end {
                    None => s,
                    Some(idx) => String::from(&s[idx..]),
                }
            })),
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

        let ret = match *self {
            Literal(lit) => lit,
            Var(ref var) => env.var(var).and_then(|s| s.parse().ok()).unwrap_or(0),

            PostIncr(ref var) => {
                let val = env.var(var).and_then(|s| s.parse().ok()).unwrap_or(0);
                env.set_var(var.clone(), (val + 1).to_string());
                val
            },

            PostDecr(ref var) => {
                let val = env.var(var).and_then(|s| s.parse().ok()).unwrap_or(0);
                env.set_var(var.clone(), (val - 1).to_string());
                val
            },

            PreIncr(ref var) => {
                let val = env.var(var).and_then(|s| s.parse().ok()).unwrap_or(0) + 1;
                env.set_var(var.clone(), val.to_string());
                val
            },

            PreDecr(ref var) => {
                let val = env.var(var).and_then(|s| s.parse().ok()).unwrap_or(0) - 1;
                env.set_var(var.clone(), val.to_string());
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
                env.set_var(var.clone(), val.to_string());
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
    pub fn eval<'a>(&'a self, env: &'a mut Environment) -> Result<Fields<'a>> {
        self.eval_with_config(env, true)
    }

    /// Evaluates a word in a given environment without doing field and pathname expansions.
    ///
    /// Tilde, parameter, command substitution, arithmetic expansions, and quote removals
    /// will be performed, however. In addition, if multiple fields arise as a result
    /// of evaluating `$@` or `$*`, the fields will be joined with a single space.
    pub fn eval_as_assignment<'a>(&'a self, env: &'a mut Environment) -> Result<String> {
        self.eval_with_config(env, false).map(|f| f.join())
    }

    fn eval_with_config<'a>(&'a self,
                            env: &'a mut Environment,
                            split_fields_further: bool)
        -> Result<Fields<'a>>
    {
        use syntax::ast::Word::*;

        /// Splits a vector of fields further based on the contents of the `IFS`
        /// variable (i.e. as long as it is non-empty). Any empty fields, original
        /// or otherwise newly created will be discarded.
        fn split_fields<'a>(ifs: &str, words: Vec<Cow<'a, str>>) -> Vec<Cow<'a, str>> {
            // If IFS is set but null, there is nothing left to split
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

                    // Since we are creating new fields which are always strictly substrings
                    // of the original words/fields, we can just borrow a bunch of strs within
                    // the lifetime of our other borrows without having to reallocate.
                    // However, we do have to be careful with any owned Strings created along
                    // the way, which aren't "anchored" to some living memory. Thus to make sure
                    // we can safely pass them up to our caller(s), we'll have to make copies here.
                    let field = match (&word, end) {
                        (&Cow::Borrowed(s), None)       => Cow::Borrowed(&s[start..]),
                        (&Cow::Borrowed(s), Some(end))  => Cow::Borrowed(&s[start..end]),
                        (&Cow::Owned(ref s), None)      => Cow::Owned(String::from(&s[start..])),
                        (&Cow::Owned(ref s), Some(end)) => Cow::Owned(String::from(&s[start..end])),
                    };

                    // Make sure we "delete" any empty fields we generate.
                    if !field.is_empty() {
                        fields.push(field);
                    }
                }
            }

            fields.shrink_to_fit();
            fields
        }

        fn get_ifs<'a>(env: &'a Environment) -> &'a str {
            env.var("IFS").unwrap_or(IFS_DEFAULT)
        }

        fn ifs_char<'a>(env: &'a Environment) -> &'a str {
            let ifs = get_ifs(env);
            if ifs.is_empty() { "" } else { &ifs[0..1] }
        }

        fn copy_ifs(env: &Environment) -> String {
            get_ifs(env).to_string()
        }

        fn maybe_split_fields<'a, F>(split: bool,
                              env: &'a mut Environment,
                              closure: F) -> Result<Fields>
            where F: FnOnce(&'a mut Environment) -> Result<Fields<'a>>
        {
            let ifs = if split { Some(copy_ifs(env)) } else { None };
            let fields = try!(closure(env));
            let fields = match ifs {
                None => fields,
                Some(ref ifs) => match fields {
                    Fields::At(fs)   => Fields::At(split_fields(ifs, fs)),
                    Fields::Star(fs) => Fields::Star(split_fields(ifs, fs)),
                    Fields::Many(fs) => Fields::Many(split_fields(ifs, fs)),

                    Fields::Single(f) => {
                        let mut fields = split_fields(ifs, vec!(f));
                        if fields.len() == 1 {
                            Fields::Single(fields.pop().unwrap())
                        } else {
                            Fields::Many(fields)
                        }
                    },
                },
            };
            Ok(fields)
        };


        let fields = match *self {
            Literal(ref s)      => Fields::Single((&**s).into()),
            SingleQuoted(ref s) => Fields::Single((&**s).into()),
            Escaped(ref s)      => Fields::Single((&**s).into()),
            Star                => Fields::Single("*".into()),
            Question            => Fields::Single("?".into()),
            SquareOpen          => Fields::Single("]".into()),
            SquareClose         => Fields::Single("[".into()),
            Tilde               => Fields::Single(env.var("HOME").map_or(COW_STR_EMPTY, |s| s.into())),

            Subst(ref s) => try!(maybe_split_fields(split_fields_further, env, |env| s.eval(env))),
            Param(ref p) => try!(maybe_split_fields(split_fields_further, env, |env| {
                Ok(p.eval(env).unwrap_or(NULL_FIELD))
            })),

            Concat(ref v) => unimplemented!(),
            DoubleQuoted(ref v) => unimplemented!(),
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
        let cmd_name = try!(cmd.eval(env)).into_iter().next().map(|exe| exe.into_owned());
        let cmd_name = match cmd_name {
            Some(exe) => exe,
            None => {
                env.set_last_status(EXIT_CMD_NOT_FOUND);
                return Err(RuntimeError::CommandNotFound(String::new()));
            },
        };

        if env.has_function(&cmd_name) {
            let mut fn_args = Vec::new();
            for arg in args.iter() {
                fn_args.extend(try!(arg.eval(env)).into_iter().map(|s| s.into_owned()));
            }

            let fn_args: Vec<&str> = fn_args.iter().map(|s| &**s).collect();
            match env.run_function(&cmd_name, &fn_args) {
                Some(ret) => return ret,
                None => {
                    env.set_last_status(EXIT_CMD_NOT_FOUND);
                    return Err(RuntimeError::CommandNotFound(cmd_name));
                }
            }
        }

        let mut cmd = Command::new(&cmd_name);

        for arg in args {
            for field in try!(arg.eval(env)) {
                cmd.arg(&*field);
            }
        }

        cmd.stdin(Stdio::inherit())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit());

        // First inherit all default ENV variables
        for (var, val) in env.env().into_iter() {
            cmd.env(var, val);
        }

        // Then do any local insertions/overrides
        for &(ref var, ref val) in self.vars.iter() {
            match try!(val.as_ref().map(|w| w.eval(env)).unwrap_or(Ok(NULL_FIELD))) {
                Fields::Single(s) => cmd.env(var, &*s),
                f@Fields::At(_)   |
                f@Fields::Star(_) |
                f@Fields::Many(_) => cmd.env(var, f.join()),
            };
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
                let run_with_val = |env: &Environment, val| {
                    let mut env = env.sub_env();
                    env.set_var(var.clone(), val);
                    body.run(&mut *env)
                };

                let mut exit = EXIT_SUCCESS;
                match *in_words {
                    Some(ref words) => for w in words {
                        let fields: Vec<String> = try!(w.eval(env)).into_iter()
                            .map(|s| s.into_owned()).collect();
                        for field in fields {
                            exit = try!(run_with_val(env, field));
                        }
                    },

                    None => for w in env.args() {
                        exit = try!(run_with_val(env, w.to_string()))
                    },
                }
                exit
            },


            Case(ref word, ref arms) => {
                let match_opts = glob::MatchOptions {
                    case_sensitive: true,
                    require_literal_separator: false,
                    require_literal_leading_dot: false,
                };

                let word = try!(word.eval_with_config(env, false)).join();

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
