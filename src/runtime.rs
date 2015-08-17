//! This module defines a runtime envirnment capable of executing parsed shell commands.

use glob;
use libc;

use std::borrow::Cow;
use std::collections::HashMap;
use std::convert::{From, Into};
use std::default::Default;
use std::error::Error;
use std::io::{self, Error as IoError, ErrorKind as IoErrorKind, Write};
use std::fmt;
use std::process::{self, Command, Stdio};
use std::rc::Rc;

use void::Void;

// Apparently importing Redirect before Word causes an ICE, when linking
// to this crate, so this ordering is *very* crucial...
// 'assertion failed: bound_list_is_sorted(&bounds.projection_bounds)', ../src/librustc/middle/ty.rs:4028
use syntax::ast::{Arith, CompoundCommand, SimpleCommand, Parameter, Word, Redirect};
use syntax::ast::Command as AstCommand;

const EXIT_SUCCESS:            ExitStatus = ExitStatus::Code(0);
const EXIT_ERROR:              ExitStatus = ExitStatus::Code(1);
const EXIT_CMD_NOT_EXECUTABLE: ExitStatus = ExitStatus::Code(126);
const EXIT_CMD_NOT_FOUND:      ExitStatus = ExitStatus::Code(127);

const COW_STR_EMPTY: Cow<'static, str> = Cow::Borrowed("");
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

impl<'a, T: Environment + ?Sized> Environment for &'a mut T {
    fn sub_env<'b>(&'b self) -> Box<Environment + 'b> { (**self).sub_env() }
    fn name(&self) -> &str { (**self).name() }
    fn var(&self, name: &str) -> Option<&str> { (**self).var(name) }
    fn set_var(&mut self, name: String, val: String) { (**self).set_var(name, val) }
    fn run_function(&mut self, fn_name: &str, args: &[&str]) -> Option<Result<ExitStatus>> {
        (**self).run_function(fn_name, args)
    }
    fn set_function(&mut self, name: String, func: Box<Run>) { (**self).set_function(name, func) }
    fn last_status(&self) -> ExitStatus { (**self).last_status() }
    fn set_last_status(&mut self, status: ExitStatus) { (**self).set_last_status(status) }
    fn arg(&self, idx: usize) -> Option<&str> { (**self).arg(idx) }
    fn args_len(&self) -> usize { (**self).args_len() }
    fn args(&self) -> Vec<&str> { (**self).args() }
    fn env(&self) -> Vec<(&str, &str)> { (**self).env() }
    fn report_error(&mut self, err: RuntimeError) { (**self).report_error(err) }
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
            let mut args: Vec<Cow<'a, str>> = mem::transmute(args);
            mem::swap(&mut self.args, &mut args);
            let ret = func.run(self);
            mem::swap(&mut self.args, &mut args);
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
    pub fn eval<'a>(&self, env: &'a Environment) -> Option<Cow<'a, str>> {
        match *self {
            Parameter::At => if env.args_len() == 0 { None } else { Some(env.args().join(" ").into()) },
            Parameter::Star => if env.args_len() == 0 {
                None
            } else {
                Some(match env.var("IFS").unwrap_or(IFS_DEFAULT).chars().next() {
                    None => env.args().concat().into(),
                    Some(c) => {
                        let mut sep = String::with_capacity(1);
                        sep.push(c);
                        env.args().join(&sep).into()
                    },
                })
            },

            Parameter::Pound  => Some(env.args_len().to_string().into()),
            Parameter::Dollar => Some(unsafe { libc::getpid().to_string().into() }),
            Parameter::Dash   => Some(COW_STR_EMPTY),
            Parameter::Bang   => Some(COW_STR_EMPTY), // FIXME: eventual job control would be nice

            Parameter::Question => Some(match env.last_status() {
                ExitStatus::Code(c) => (c as u32).to_string().into(),
                ExitStatus::Signal(c) => (c as u32 + 128).to_string().into(),
            }),

            Parameter::Positional(p) => if p == 0 {
                Some(env.name().into())
            } else {
                env.arg(p as usize).map(|s| s.into())
            },

            Parameter::Var(ref var) => env.var(var).map(|s| s.into()),
        }
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
    pub fn eval(&self, env: &mut Environment) -> Result<Vec<Cow<str>>> {
        let pat_str = try!(self.as_pattern_str(env));
        let match_opts = glob::MatchOptions {
            case_sensitive: true,
            require_literal_separator: true,
            require_literal_leading_dot: true,
        };

        if let Ok(globs) = glob::glob_with(&*pat_str, &match_opts) {
            let paths: Vec<Cow<str>> = globs.into_iter()
                .filter_map(|glob| glob.ok())
                .filter_map(|path| path.to_str().map(|s| s.to_string()))
                .map(|s| s.into())
                .collect();

            if !paths.is_empty() {
                return Ok(paths);
            }
        }

        Ok(vec!(try!(self.eval_as_literal(env))))
    }

    pub fn eval_as_literal(&self, env: &mut Environment) -> Result<Cow<str>> {
        use syntax::ast::Word::*;

        let ret = match *self {
            Literal(ref s)      => (&**s).into(),
            SingleQuoted(ref s) => (&**s).into(),
            Escaped(ref s)      => (&**s).into(),
            Star                => "*".into(),
            Question            => "?".into(),
            SquareOpen          => "]".into(),
            SquareClose         => "[".into(),
            Tilde               => "~".into(),

            Param(ref p) => p.eval(env).unwrap_or(COW_STR_EMPTY).into_owned().into(),
            Subst(..) => unimplemented!(), // FIXME:

            Concat(ref v)       |
            DoubleQuoted(ref v) => try!(v.iter()
                .map(|w| w.eval_as_literal(env))
                .collect::<Result<Vec<Cow<str>>>>())
                .concat()
                .into(),
        };

        Ok(ret)
    }

    /// Attempts to create a `glob::Pattern` from `self`, escaping any characters as appropriate.
    pub fn as_pattern(&self, env: &mut Environment) -> Result<Option<glob::Pattern>>
    {
        Ok(glob::Pattern::new(&*try!(self.as_pattern_str(env))).ok())
    }

    /// Wraps any literal/escaped words which could be (incorrectly)
    /// interpreted as part of a pattern.
    fn as_pattern_str(&self, env: &mut Environment) -> Result<Cow<str>> {
        let ret = match *self {
            Word::Star        |
            Word::Question    |
            Word::SquareOpen  |
            Word::SquareClose => try!(self.eval_as_literal(env)),

            Word::Tilde           |
            Word::Param(_)        |
            Word::Subst(_)        |
            Word::Literal(_)      |
            Word::Escaped(_)      |
            Word::SingleQuoted(_) |
            Word::DoubleQuoted(_) => glob::Pattern::escape(&*try!(self.eval_as_literal(env))).into(),

            Word::Concat(ref v) => try!(v.iter()
                .map(|w| w.as_pattern_str(env))
                .collect::<Result<Vec<Cow<str>>>>())
                .concat()
                .into(),
        };

        Ok(ret)
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
                    let val = try!(val.eval(env)).join(" ");
                    env.set_var(var.clone(), val);
                }
            }
            let exit = EXIT_SUCCESS;
            env.set_last_status(exit);
            return Ok(exit);
        }

        let &(ref cmd, ref args) = self.cmd.as_ref().unwrap();

        // bash and zsh just grab first field of an expansion
        let cmd_name_fields = try!(cmd.eval(env));
        let cmd_name = match cmd_name_fields.get(0) {
            Some(exe) => exe,
            None => {
                env.set_last_status(EXIT_CMD_NOT_FOUND);
                return Err(RuntimeError::CommandNotFound(String::new()));
            },
        };

        let args: Vec<Vec<Cow<str>>> = try!(args.iter().map(|arg| arg.eval(env)).collect());
        let args: Vec<&str> = args.iter().flat_map(|v| v.iter()).map(|s| &**s).collect();

        if let Some(res) = env.run_function(cmd_name, &args) {
            return res;
        }

        let mut cmd = Command::new(&**cmd_name);
        for arg in args {
            cmd.arg(arg);
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
            let fields = match val.as_ref().map(|w| w.eval(env)) {
                Some(Ok(f)) => f,
                Some(Err(err)) => return Err(err),
                None => Vec::new(),
            };

            if fields.len() == 1 {
                // Avoid an extra allocation if we have no fields to join
                cmd.env(var, &*fields[0]);
            } else {
                // FIXME: join with IFS?
                cmd.env(var, fields.join(" "));
            }
        }

        match cmd.status() {
            Err(e) => {
                let (exit, err) = if IoErrorKind::NotFound == e.kind() {
                    (EXIT_CMD_NOT_FOUND, RuntimeError::CommandNotFound(cmd_name.to_string()))
                } else if Some(libc::ENOEXEC) == e.raw_os_error() {
                    (EXIT_CMD_NOT_EXECUTABLE, RuntimeError::CommandNotExecutable(cmd_name.to_string()))
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
                let run_with_val = |env: &Environment, val: &str| {
                    let mut env = env.sub_env();
                    env.set_var(var.clone(), val.to_string());
                    body.run(&mut *env)
                };

                let mut exit = EXIT_SUCCESS;
                match *in_words {
                    Some(ref words) => for w in words {
                        for field in try!(w.eval(env)) {
                            exit = try!(run_with_val(env, &field));
                        }
                    },

                    None => for w in env.args() {
                        exit = try!(run_with_val(env, w))
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

                let word = try!(word.eval_as_literal(env));

                let mut exit = EXIT_SUCCESS;
                for &(ref pats, ref body) in arms.iter() {
                    for pat in pats {
                        if try!(pat.as_pattern(env))
                            .map_or(false, |p| p.matches_with(&word, &match_opts))
                        || word == try!(pat.eval_as_literal(env)) {
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
