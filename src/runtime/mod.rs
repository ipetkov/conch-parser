//! This module defines a runtime envirnment capable of executing parsed shell commands.

use glob;
use libc;

use std::borrow::{Borrow, Cow};
use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::convert::{From, Into};
use std::fmt;
use std::fs::OpenOptions;
use std::io::Error as IoError;
use std::io::ErrorKind as IoErrorKind;
use std::io::Result as IoResult;
use std::io::Write;
use std::iter::{IntoIterator, Iterator};
use std::process::{self, Stdio};
use std::rc::Rc;
use std::result;
use std::vec;

use syntax::ast::{Arith, Command, CompoundCommand, SimpleCommand, Parameter, ParameterSubstitution, Redirect, Word};
use runtime::io::dup_stdio;
use runtime::io::{FileDesc, Permissions};
use void::Void;

mod errors;

pub mod io;
pub use self::errors::*;

const EXIT_SUCCESS:            ExitStatus = ExitStatus::Code(0);
const EXIT_ERROR:              ExitStatus = ExitStatus::Code(1);
const EXIT_CMD_NOT_EXECUTABLE: ExitStatus = ExitStatus::Code(126);
const EXIT_CMD_NOT_FOUND:      ExitStatus = ExitStatus::Code(127);

const EXIT_SIGNAL_OFFSET: u32 = 128;

const IFS_DEFAULT: &'static str = " \t\n";

/// File descriptor for standard input.
pub const STDIN_FILENO: Fd = 0;
/// File descriptor for standard output.
pub const STDOUT_FILENO: Fd = 1;
/// File descriptor for standard error.
pub const STDERR_FILENO: Fd = 2;

/// A macro that accepts a `Result<ExitStatus, RuntimeError>` and attempts
/// to unwrap it much like `try!`. If the result is a "fatal" error the macro
/// immediately returns from the enclosing function. Otherwise, the error is
/// reported via `Environment::report_error`, and the environment's last status
/// is returned.
///
/// A `RuntimeError::Expansion` is considered fatal, since expansion errors should
/// result in the exit of a non-interactive shell according to the POSIX standard.
macro_rules! try_and_swallow_non_fatal {
    ($result:expr, $env:expr) => {{
        match $result {
            Ok(exit) => exit,
            Err(err) => match err {
                RuntimeError::Expansion(..) => return Err(err),

                RuntimeError::Io(..)            |
                RuntimeError::Redirection(..)   |
                RuntimeError::Command(..)       |
                RuntimeError::Unimplemented(..) => {
                    // Whoever returned the error should have been responsible
                    // enough to set the last status as appropriate.
                    $env.report_error(err);
                    let exit = $env.last_status();
                    debug_assert_eq!(exit.success(), false);
                    exit
                },
            },
        }
    }}
}

/// A specialized `Result` type for shell runtime operations.
pub type Result<T> = result::Result<T, RuntimeError>;

/// The type that represents a file descriptor within shell scripts.
pub type Fd = u16;

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
        fn get_signal(_exit: process::ExitStatus) -> Option<i32> { None }

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

                let sep_len = sep.len();
                let alloc_len = v.iter().fold(0, |accum, s| accum + s.len() + sep_len);

                let mut ret = String::with_capacity(alloc_len);
                let mut iter = v.into_iter();

                if let Some(first) = iter.next() {
                    ret.push_str(&**first);
                }

                for s in iter {
                    ret.push_str(sep);
                    ret.push_str(&**s);
                }

                Rc::new(ret)
            },
        }
    }
}

impl IntoIterator for Fields {
    type Item = Rc<String>;
    type IntoIter = vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Fields::Zero => vec!().into_iter(),
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
    /// The function bodies are stored as `Option`s to properly distinguish functions
    /// that were explicitly unset and functions that are simply defined in a parent
    /// environment.
    functions: HashMap<String, Option<Rc<Run>>>,
    /// A mapping of variable names to their values.
    ///
    /// The values are stored as `Option`s to properly distinguish variables that were
    /// explicitly unset and variables that are simply defined in a parent environment.
    /// The tupled boolean indicates if a variable should be exported to other commands.
    vars: HashMap<String, Option<(Rc<String>, bool)>>,
    /// A mapping of file descriptors and their OS handles.
    ///
    /// The values are stored as `Option`s to properly distinguish descriptors that
    /// were explicitly closed and descriptors that may have been opened in a parent
    /// environment. The tupled value also holds the permissions of the descriptor.
    fds: HashMap<Fd, Option<(Rc<FileDesc>, Permissions)>>,
    /// The exit status of the last command that was executed.
    last_status: ExitStatus,
    /// A parent environment for looking up previously set values.
    parent_env: Option<&'a Env<'a>>,
}

impl<'a> Env<'a> {
    /// Creates a new default environment.
    /// See the docs for `Env::with_config` for more information.
    pub fn new() -> IoResult<Self> {
        Self::with_config(None, None, None, None)
    }

    /// Creates an environment using provided overrides, or data from the
    /// current process if the respective override is not provided.
    ///
    /// Unless otherwise specified, the environment's name will become
    /// the basename of the current process (e.g. the 0th OS arg).
    ///
    /// Unless otherwise specified, all environment variables of the
    /// current process will be inherited as environment variables
    /// by any spawned commands. For exmaple, specifying `Some(vec!())`
    /// will result in an environment with NO environment variables, while
    /// specifying `None` will copy the environment variables of the current process.
    ///
    /// Unless otherwise specified, the new environment will copy the
    /// current std{in, out, err} descriptors/handles to be used by this
    /// environment. Otherwise the provided file descriptors will be used
    /// as given. For example, specifying `Some(vec!())` will result in an
    /// environment with NO file descriptors, while specifying `None` will
    /// copy the std{in, out, err} descriptors/handles of the current process.
    ///
    /// Note: Any data taken from the current process (e.g. environment
    /// variables) which is not valid Unicode will be ignored.
    pub fn with_config(name: Option<String>,
                       args: Option<Vec<String>>,
                       env: Option<Vec<(String, String)>>,
                       fds: Option<Vec<(Fd, Rc<FileDesc>, Permissions)>>) -> IoResult<Self>
    {
        use std::env;

        let name = name.unwrap_or_else(|| env::current_exe().ok().and_then(|path| {
            path.file_name().and_then(|os_str| os_str.to_str().map(|s| s.to_string()))
        }).unwrap_or_default());

        let args = args.map_or(Vec::new(), |args| args.into_iter().map(|s| Rc::new(s)).collect());

        let vars = env.map_or_else(
            || env::vars().map(|(k, v)| (k, Some((Rc::new(v), true)))).collect(),
            |pairs| pairs.into_iter().map(|(k,v)| (k, Some((Rc::new(v), true)))).collect()
        );

        let fds = match fds {
            Some(fds) => fds.into_iter().map(|(fd, fdes, perm)| (fd, Some((fdes, perm)))).collect(),
            None => {
                let (stdin, stdout, stderr) = try!(dup_stdio());

                let mut fds = HashMap::with_capacity(3);
                fds.insert(STDIN_FILENO,  Some((Rc::new(stdin),  Permissions::Read)));
                fds.insert(STDOUT_FILENO, Some((Rc::new(stdout), Permissions::Write)));
                fds.insert(STDERR_FILENO, Some((Rc::new(stderr), Permissions::Write)));
                fds
            },
        };

        Ok(Env {
            shell_name: Rc::new(String::from(name)),
            args: args,
            functions: HashMap::new(),
            vars: vars,
            fds: fds,
            last_status: EXIT_SUCCESS,
            parent_env: None,
        })
    }

    /// Walks `self` and its entire chain of parent environments and evaluates a closure on each.
    ///
    /// If the closure evaluates a `Ok(Some(x))` value, then `Some(x)` is returned.
    /// If the closure evaluates a `Err(_)` value, then `None` is returned.
    /// If the closure evaluates a `Ok(None)` value, then the traversal continues.
    fn walk_parent_chain<'b, T, F>(&'b self, mut cond: F) -> Option<T>
        where F: FnMut(&'b Self) -> result::Result<Option<T>, ()>
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

pub trait Environment {
    /// Create a new sub-environment using the current environment as its parent.
    ///
    /// Any changes which mutate the sub environment will only be reflected there,
    /// but any information not present in the sub-env will be looked up in the parent.
    fn sub_env<'a>(&'a self) -> Box<Environment + 'a>;
    /// Get the shell's current name.
    fn name(&self) -> &Rc<String>;
    /// Get the value of some variable. The values of both shell-only
    /// variables will be looked up and returned.
    fn var(&self, name: &str) -> Option<&Rc<String>>;
    /// Set the value of some variable (including environment variables).
    fn set_var(&mut self, name: String, val: Rc<String>);
    /// Indicates if a funciton is currently defined with a given name.
    fn has_function(&mut self, fn_name: &str) -> bool;
    /// Attempt to execute a function with a set of arguments if it has been defined.
    fn run_function(&mut self, fn_name: Rc<String>, args: Vec<Rc<String>>) -> Option<Result<ExitStatus>>;
    /// Define a function with some `Run`able body.
    fn set_function(&mut self, name: String, func: Rc<Run>);
    /// Get the exit status of the previous command.
    fn last_status(&self) -> ExitStatus;
    /// Set the exit status of the previously run command.
    fn set_last_status(&mut self, status: ExitStatus);
    /// Get an argument at any index. Arguments are 1-indexed since the shell variable `$0`
    /// to the shell's name. Thus the first real argument starts at index 1.
    fn arg(&self, idx: usize) -> Option<&Rc<String>>;
    /// Get the number of current arguments, NOT including the shell name.
    fn args_len(&self) -> usize;
    /// Get all current arguments as a vector.
    fn args(&self) -> Cow<[Rc<String>]>;
    /// Get all current pairs of environment variables and their values.
    fn env(&self) -> Vec<(&str, &str)>;
    /// Get the permissions and OS handle associated with an opened file descriptor.
    fn file_desc(&self, fd: Fd) -> Option<(&Rc<FileDesc>, Permissions)>;
    /// Associate a file descriptor with a given OS handle and permissions.
    fn set_file_desc(&mut self, fd: Fd, fdes: Rc<FileDesc>, perms: Permissions);
    /// Treat the specified file descriptor as closed for the current environment.
    fn close_file_desc(&mut self, fd: Fd);
    /// Consumes `RuntimeError`s and reports them as appropriate, e.g. print to stderr.
    fn report_error(&mut self, err: RuntimeError) {
        // We *could* duplicate the handle here and ensure that we are the only
        // owners of that *copy*, but it won't make much difference. On Unix
        // sytems file descriptor duplication is effectively just an alias, and
        // we really *do* want to write into whatever stderr is. Plus our error
        // description should safely fall well within the system's size for atomic
        // writes so we (hopefully) shouldn't observe any interleaving of data.
        //
        // Tl;dr: duplicating the handle won't offer us any extra safety, so we
        // can avoid the overhead.
        self.file_desc(STDERR_FILENO).map(|(fd, _)| unsafe {
            fd.unsafe_write().write_all(&format!("{}: {}", self.name(), err).into_bytes())
        });
    }
}

impl<'a> Environment for Env<'a> {
    fn sub_env<'b>(&'b self) -> Box<Environment + 'b> {
        Box::new(Env {
            shell_name: self.shell_name.clone(),
            args: self.args.clone(),

            functions: HashMap::new(),
            vars: HashMap::new(),
            fds: HashMap::new(),
            last_status: self.last_status,
            parent_env: Some(self),
        })
    }

    fn name(&self) -> &Rc<String> {
        &self.shell_name
    }

    fn var(&self, name: &str) -> Option<&Rc<String>> {
        self.walk_parent_chain(|cur| match cur.vars.get(name) {
            Some(&Some((ref s, _))) => Ok(Some(s)), // found the var
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

    fn set_function(&mut self, name: String, func: Rc<Run>) {
        self.functions.insert(name, Some(func));
    }

    fn last_status(&self) -> ExitStatus {
        self.last_status
    }

    fn set_last_status(&mut self, status: ExitStatus) {
        self.last_status = status;
    }

    fn arg(&self, idx: usize) -> Option<&Rc<String>> {
        if idx == 0 {
            Some(self.name())
        } else {
            self.args.get(idx - 1)
        }
    }

    fn args_len(&self) -> usize {
        self.args.len()
    }

    fn args(&self) -> Cow<[Rc<String>]> {
        Cow::Borrowed(&self.args)
    }

    fn env(&self) -> Vec<(&str, &str)> {
        let mut env = HashMap::new();
        self.walk_parent_chain(|cur| -> result::Result<Option<Void>, ()> {
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

    fn file_desc(&self, fd: Fd) -> Option<(&Rc<FileDesc>, Permissions)> {
        self.walk_parent_chain(|cur| match cur.fds.get(&fd) {
            Some(&Some((ref fdes, perm))) => Ok(Some((fdes, perm))), // found an open fd
            Some(&None) => Err(()), // fd already closed, break the walk
            None => Ok(None), // neither closed nor open, keep walking
        })
    }

    fn set_file_desc(&mut self, fd: Fd, fdes: Rc<FileDesc>, perms: Permissions) {
        self.fds.insert(fd, Some((fdes, perms)));
    }

    fn close_file_desc(&mut self, fd: Fd) {
        match self.parent_env {
            // If we have a parent environment the specified fd could
            // have been opened there, so to avoid clobbering it,
            // we'll just ensure the current env treats this fd as closed.
            Some(_) => self.fds.insert(fd, None),
            // Otherwise if we are a root env we are the only possible
            // source of the fd so we can actually remove it from the container.
            None => self.fds.remove(&fd),
        };
    }
}

impl Parameter {
    /// Evaluates a parameter in the context of some environment.
    ///
    /// Any fields as a result of evaluating `$@` or `$*` will not be
    /// split further. This is left for the caller to perform.
    ///
    /// A `None` value indicates that the parameter is unset.
    pub fn eval(&self, env: &Environment) -> Option<Fields> {
        let get_args = || {
            let args = env.args();
            if args.is_empty() {
                None
            } else {
                Some(args.iter().cloned().collect())
            }
        };

        match *self {
            Parameter::At   => Some(get_args().map_or(Fields::Zero, Fields::At)),
            Parameter::Star => Some(get_args().map_or(Fields::Zero, Fields::Star)),

            Parameter::Pound  => Some(Fields::Single(Rc::new(env.args_len().to_string()))),
            Parameter::Dollar => Some(Fields::Single(Rc::new(unsafe { libc::getpid() }.to_string()))),
            Parameter::Dash   => None,
            Parameter::Bang   => None, // FIXME: eventual job control would be nice

            Parameter::Question => Some(Fields::Single(Rc::new(match env.last_status() {
                ExitStatus::Code(c)   => c as u32,
                ExitStatus::Signal(c) => c as u32 + EXIT_SIGNAL_OFFSET,
            }.to_string()))),

            Parameter::Positional(0) => Some(Fields::Single(env.name().clone())),
            Parameter::Positional(p) => env.arg(p as usize).cloned().map(Fields::Single),
            Parameter::Var(ref var)  => env.var(var).cloned().map(Fields::Single),
        }
    }
}

impl ParameterSubstitution {
    /// Evaluates a parameter subsitution in the context of some environment.
    ///
    /// No field *splitting* will be performed, and is left for the caller to
    /// implement. However, multiple fields can occur if `$@` or `$*` is evaluated.
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
                        Fields::Zero      => Fields::Zero,
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
                    if !fields.is_null() {
                        return Ok(fields)
                    } else if !$strict {
                        return Ok(null_field)
                    }
                }
            }}
        }

        let ret = match *self {
            Command(_) => unimplemented!(),

            Len(ref p) => Fields::Single(Rc::new(match p.eval(env) {
                None |
                Some(Fields::Zero) => String::from("0"),

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
                    p@&Parameter::Positional(_) => {
                        env.set_last_status(EXIT_ERROR);
                        return Err(ExpansionError::BadAssig(p.clone()).into());
                    },

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

                env.set_last_status(EXIT_ERROR);
                return Err(ExpansionError::EmptyParameter(p.clone(), msg).into());
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
    pub fn eval(&self, env: &mut Environment) -> result::Result<isize, ExpansionError> {
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
                    return Err(ExpansionError::NegativeExponent);
                } else {
                    try!(left.eval(env)).pow(right as u32)
                }
            },

            Div(ref left, ref right) => {
                let right = try!(right.eval(env));
                if right == 0 {
                    env.set_last_status(EXIT_ERROR);
                    return Err(ExpansionError::DivideByZero);
                } else {
                    try!(left.eval(env)) / right
                }
            },

            Modulo(ref left, ref right) => {
                let right = try!(right.eval(env));
                if right == 0 {
                    env.set_last_status(EXIT_ERROR);
                    return Err(ExpansionError::DivideByZero);
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
        self.eval_with_config(env, true, true)
    }

    /// Evaluates a word in a given environment without doing field and pathname expansions.
    ///
    /// Tilde, parameter, command substitution, arithmetic expansions, and quote removals
    /// will be performed, however. In addition, if multiple fields arise as a result
    /// of evaluating `$@` or `$*`, the fields will be joined with a single space.
    pub fn eval_as_assignment(&self, env: &mut Environment) -> Result<Rc<String>> {
        match try!(self.eval_with_config(env, true, false)) {
            f@Fields::Zero      |
            f@Fields::Single(_) |
            f@Fields::At(_)     |
            f@Fields::Many(_) => Ok(f.join()),
            f@Fields::Star(_) => Ok(f.join_with_ifs(env)),
        }
    }

    fn eval_with_config(&self,
                        env: &mut Environment,
                        expand_tilde: bool,
                        split_fields_further: bool) -> Result<Fields>
    {
        use syntax::ast::Word::*;


        let maybe_split_fields = |fields, env: &mut Environment| {
            if !split_fields_further {
                return fields;
            }

            match fields {
                Fields::Zero     => Fields::Zero,
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

        let fields = match *self {
            Literal(ref s)      |
            SingleQuoted(ref s) |
            Escaped(ref s)      => Fields::Single(Rc::new(s.clone())),

            Star        => Fields::Single(Rc::new(String::from("*"))),
            Question    => Fields::Single(Rc::new(String::from("?"))),
            SquareOpen  => Fields::Single(Rc::new(String::from("]"))),
            SquareClose => Fields::Single(Rc::new(String::from("["))),

            Tilde => if expand_tilde {
                env.var("HOME").map_or(Fields::Zero, |f| Fields::Single(f.clone()))
            } else {
                Fields::Single(Rc::new(String::from("~")))
            },

            Colon => Fields::Single(Rc::new(String::from(":"))),

            Subst(ref s) => maybe_split_fields(try!(s.eval(env)), env),
            Param(ref p) => maybe_split_fields(p.eval(env).unwrap_or(Fields::Zero), env),

            Concat(ref v) => {
                let mut fields: Vec<Rc<String>> = Vec::new();
                for w in v.iter() {
                    let mut iter = try!(w.eval_with_config(env, false, split_fields_further)).into_iter();
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
                    Fields::Zero
                } else if fields.len() == 1 {
                    Fields::Single(fields.pop().unwrap())
                } else {
                    Fields::Many(fields)
                }
            },

            DoubleQuoted(ref v) => {
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
                    // Make sure we are NOT doing any tilde expanions for further field splitting
                    match (try!(w.eval_with_config(env, false, false)), w) {
                        (Fields::Zero, _) => continue,

                        (Fields::Single(s), _) => append_to_cur_field!(s),

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

                        (f@Fields::Star(_), _) => append_to_cur_field!(f.join_with_ifs(env)),

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
                        (Fields::Many(_), &Word::Colon)           |
                        (Fields::Many(_), &Word::Subst(_))        |
                        (Fields::Many(_), &Word::Param(_))        |
                        (Fields::Many(_), &Word::Concat(_))       => unreachable!(),
                    }
                }

                cur_field.map(|s| fields.push(Rc::new(s)));

                // Make sure we return before doing any pathname expansions.
                return Ok(if fields.is_empty() {
                    Fields::Zero
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

impl Redirect {
    /// Evaluates a redirection path and opens the appropriate redirect.
    ///
    /// Newly opened/closed/duplicated file descriptors are NOT updated
    /// in the environment, and thus it is up to the caller to update the
    /// environment as appropriate.
    ///
    /// On success the affected file descriptor (from the script's perspective)
    /// is returned, along with an Optional file handle and the respective
    /// permissions. A `Some` value indicates a newly opened or duplicated descriptor
    /// while a `None` indicates that that descriptor should be closed.
    pub fn eval(&self, env: &mut Environment) -> Result<(Fd, Option<(Rc<FileDesc>, Permissions)>)> {
        fn eval_path(path: &Word, env: &mut Environment) -> Result<Rc<String>> {
            match try!(path.eval_with_config(env, true, false)) {
                Fields::Single(path) => Ok(path),
                Fields::At(mut v) |
                Fields::Star(mut v) |
                Fields::Many(mut v) => if v.len() == 1 {
                    Ok(v.pop().unwrap())
                } else {
                    return Err(RedirectionError::Ambiguous(v).into())
                },
                Fields::Zero => return Err(RedirectionError::Ambiguous(Vec::new()).into()),
            }
        };

        fn dup_fd(dst_fd: Fd, src_fd: &Word, readable: bool, env: &mut Environment)
            -> Result<(Fd, Option<(Rc<FileDesc>, Permissions)>)>
        {
            let src_fd = try!(eval_path(src_fd, env));

            if *src_fd == "-" {
                return Ok((dst_fd, None));
            }

            let src_fdes = match Fd::from_str_radix(&src_fd, 10) {
                Ok(fd) => match env.file_desc(fd) {
                    Some((fdes, perms)) => {
                        if (readable && perms.readable()) || (!readable && perms.writable()) {
                            Ok(fdes.clone())
                        } else {
                            Err(RedirectionError::BadFdPerms(fd, perms).into())
                        }
                    },

                    None => Err(RedirectionError::BadFdSrc(src_fd).into()),
                },

                Err(_) => Err(RedirectionError::BadFdSrc(src_fd).into()),
            };

            let src_fdes = match src_fdes {
                Ok(fd) => fd,
                Err(e) => {
                    env.set_last_status(EXIT_ERROR);
                    return Err(e);
                },
            };

            let perms = if readable { Permissions::Read } else { Permissions::Write };
            Ok((dst_fd, Some((src_fdes, perms))))
        };

        let open_path_with_options = |path, env, fd, options: OpenOptions, permissions|
            -> Result<(Fd, Option<(Rc<FileDesc>, Permissions)>)>
        {
            let path = try!(eval_path(path, env));
            match options.open(&**path) {
                Ok(file) => Ok((fd, Some((Rc::new(file.into()), permissions)))),
                Err(io) => Err(RuntimeError::Io(io, path).into()),
            }
        };

        let open_path = |path, env, fd, permissions: Permissions|
            -> Result<(Fd, Option<(Rc<FileDesc>, Permissions)>)>
        {
            open_path_with_options(path, env, fd, permissions.into(), permissions)
        };

        let ret = match *self {
            Redirect::Read(fd, ref path) =>
                try!(open_path(path, env, fd.unwrap_or(STDIN_FILENO), Permissions::Read)),

            Redirect::ReadWrite(fd, ref path) =>
                try!(open_path(path, env, fd.unwrap_or(STDIN_FILENO), Permissions::ReadWrite)),

            Redirect::Write(fd, ref path) |
            Redirect::Clobber(fd, ref path) =>
                try!(open_path(path, env, fd.unwrap_or(STDOUT_FILENO), Permissions::Write)),

            Redirect::Append(fd, ref path) => {
                let perms = Permissions::Write;
                let mut options: OpenOptions = perms.into();
                options.append(true);
                try!(open_path_with_options(path, env, fd.unwrap_or(STDOUT_FILENO), options, perms))
            },

            Redirect::DupRead(fd, ref src)  => try!(dup_fd(fd.unwrap_or(STDIN_FILENO), src, true, env)),
            Redirect::DupWrite(fd, ref src) => try!(dup_fd(fd.unwrap_or(STDOUT_FILENO), src, false, env)),

            Redirect::Heredoc(fd, ref body) => unimplemented!(),
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
            for &(ref var, ref val) in self.vars.iter() {
                if let Some(val) = val.as_ref() {
                    let val = try!(val.eval_as_assignment(env));
                    env.set_var(var.clone(), val);
                }
            }

            // Make sure we "touch" any local redirections, as this
            // will have side effects (possibly desired by the script).
            try!(run_with_local_redirections(env, &self.io, |_| Ok(())));

            let exit = EXIT_SUCCESS;
            env.set_last_status(exit);
            return Ok(exit);
        }

        let &(ref cmd, ref args) = self.cmd.as_ref().unwrap();

        // FIXME: look up aliases
        // bash and zsh just grab first field of an expansion
        let cmd_name = try!(cmd.eval(env)).into_iter().next();
        let cmd_name = match cmd_name {
            Some(exe) => exe,
            None => {
                env.set_last_status(EXIT_CMD_NOT_FOUND);
                return Err(CommandError::NotFound(Rc::new(String::new())).into());
            },
        };

        let cmd_args = {
            let mut cmd_args = Vec::new();
            for arg in args.iter() {
                cmd_args.extend(try!(arg.eval(env)))
            }
            cmd_args
        };

        // According to POSIX functions preceed the listed utilities, but bash and zsh
        // treat functions with first priority, so we will follow this precendent.
        if env.has_function(&cmd_name) {
            return run_with_local_redirections(env, &self.io, |env| {
                match env.run_function(cmd_name.clone(), cmd_args, ) {
                    Some(ret) => ret,
                    None => {
                        env.set_last_status(EXIT_CMD_NOT_FOUND);
                        Err(CommandError::NotFound(cmd_name).into())
                    },
                }
            });
        }

        let mut cmd = process::Command::new(&*cmd_name);
        for arg in cmd_args {
            cmd.arg(&*arg);
        }

        // First inherit all default ENV variables
        for (var, val) in env.env() {
            cmd.env(var, val);
        }

        // Then do any local insertions/overrides
        for &(ref var, ref val) in self.vars.iter() {
            if let &Some(ref w) = val {
                match try!(w.eval(env)) {
                    Fields::Zero      => continue,
                    Fields::Single(s) => cmd.env(var, &*s),
                    f@Fields::At(_)   |
                    f@Fields::Star(_) |
                    f@Fields::Many(_) => cmd.env(var, &*f.join()),
                };
            }
        }

        let mut get_redirect = |handle: Option<Rc<FileDesc>>, fd_debug| -> Result<Stdio> {
            let unwrap_fdes = |fdes: Rc<FileDesc>| Rc::try_unwrap(fdes)
                .or_else(|rc| rc.duplicate())
                .map_err(|io| RuntimeError::Io(io, Rc::new(format!("file descriptor {}", fd_debug))));


            handle.map_or_else(|| Ok(Stdio::null()),
                               |fdes| unwrap_fdes(fdes).map(|fdes| fdes.into()))
        };

        // All local redirects here will only be used for spawning this specific command.
        // By capturing an Rc handle to the descriptors before local redirects are undone
        // (e.g. dropped from the environment) we can attempt to unwrap the Rc handle
        // without (needlessly) duplicating the underlying OS file handle.
        let (cmd_std_in, cmd_std_out, cmd_std_err) = try!(run_with_local_redirections(env,
                                                                                      &self.io,
                                                                                      |env| {
            let extract = |fd: Option<(&Rc<FileDesc>, _)>| fd.map(|(fdes, _)| fdes.clone());
            Ok((extract(env.file_desc(STDIN_FILENO)),
                extract(env.file_desc(STDOUT_FILENO)),
                extract(env.file_desc(STDERR_FILENO))))
        }));

        // FIXME: we should eventually inherit all fds in the environment (at least on UNIX)
        cmd.stdin(try!(get_redirect(cmd_std_in,   STDIN_FILENO)));
        cmd.stdout(try!(get_redirect(cmd_std_out, STDOUT_FILENO)));
        cmd.stderr(try!(get_redirect(cmd_std_err, STDERR_FILENO)));

        #[cfg(unix)]
        fn is_enoexec(err: &IoError) -> bool { Some(libc::ENOEXEC) == err.raw_os_error() }

        #[cfg(windows)]
        fn is_enoexec(_err: &IoError) -> bool { false }

        match cmd.status() {
            Err(e) => {
                let (exit, err) = if IoErrorKind::NotFound == e.kind() {
                    (EXIT_CMD_NOT_FOUND, CommandError::NotFound(cmd_name).into())
                } else if is_enoexec(&e) {
                    (EXIT_CMD_NOT_EXECUTABLE, CommandError::NotExecutable(cmd_name).into())
                } else {
                    (EXIT_ERROR, RuntimeError::Io(e, cmd_name.clone()))
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

impl Run for Command {
    fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
        let exit = match *self {
            Command::And(ref first, ref second) => {
                let exit = try_and_swallow_non_fatal!(first.run(env), env);
                if exit.success() { try!(second.run(env)) } else { exit }
            },

            Command::Or(ref first, ref second) => {
                let exit = try_and_swallow_non_fatal!(first.run(env), env);
                if exit.success() { exit } else { try!(second.run(env)) }
            },

            Command::Pipe(bool, ref cmds) => unimplemented!(),

            Command::Job(_) => {
                // FIXME: eventual job control would be nice
                env.set_last_status(EXIT_ERROR);
                return Err(RuntimeError::Unimplemented("job control is not currently supported"));
            },

            Command::Function(ref name, ref cmd) => {
                env.set_function(name.clone(), cmd.clone());
                EXIT_SUCCESS
            },

            Command::Compound(ref cmd, ref redirects) =>
                try!(run_with_local_redirections(env, redirects, |env| cmd.run(env))),

            Command::Simple(ref cmd) => try!(cmd.run(env)),
        };

        env.set_last_status(exit);
        Ok(exit)
    }
}

impl Run for CompoundCommand {
    fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
        use syntax::ast::CompoundCommand::*;

        let exit = match *self {
            // Brace commands are just command groupings no different than as if we had
            // sequential commands. Thus, any error that results should be passed up
            // for the caller to decide how to handle.
            Brace(ref cmds) => try!(cmds.run(env)),

            While(ref guard, ref body) |
            Until(ref guard, ref body) => {
                let invert_guard_status = if let Until(..) = *self { true } else { false };
                let mut exit = EXIT_SUCCESS;

                // Should the loop continue?
                //
                //      invert_guard_status (i.e. is `Until` loop)
                //         +---+---+---+
                //         | ^ | 0 | 1 |
                // --------+---+---+---+
                // exit is | 0 | 0 | 1 |
                // success +---+---+---+
                //         | 1 | 1 | 0 |
                // --------+---+---+---+
                //
                // bash and zsh appear to break loops if a "fatal" error occurs,
                // so we'll emulate the same behavior in case it is expected
                while try_and_swallow_non_fatal!(guard.run(env), env).success() ^ invert_guard_status {
                    exit = try_and_swallow_non_fatal!(body.run(env), env);
                }
                exit
            },

            If(ref branches, ref els) => if branches.is_empty() {
                // An `If` AST node without any branches (conditional guards)
                // isn't really a valid instantiation, but we'll just
                // pretend it was an unsuccessful command (which it sort of is).
                let exit = EXIT_ERROR;
                env.set_last_status(exit);
                exit
            } else {
                let mut exit = None;
                for &(ref guard, ref body) in branches.iter() {
                    if try_and_swallow_non_fatal!(guard.run(env), env).success() {
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

            // Subshells should swallow (but report) errors since they are considered a separate shell.
            // Thus, errors that occur within here should NOT be propagated upward.
            Subshell(ref body) => {
                let env = &mut *env.sub_env();
                match body.run(env) {
                    Ok(exit) => exit,
                    Err(err) => {
                        env.report_error(err);
                        let exit = env.last_status();
                        debug_assert_eq!(exit.success(), false);
                        exit
                    },
                }
            }

            // bash and zsh appear to break loops if a "fatal" error occurs,
            // so we'll emulate the same behavior in case it is expected
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
                    exit = try_and_swallow_non_fatal!(body.run(env), env);
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

impl<T: Borrow<Command>> Run for [T] {
    fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
        run(self.iter().map(|c| c.borrow()), env)
    }
}

/// A function for running any iterator of items from which an `ast::Command`
/// can be borrowed from. This is useful for lazily streaming commands to run.
pub fn run<I, Item>(iter: I, env: &mut Environment) -> Result<ExitStatus>
    where I: Iterator<Item = Item>,
          Item: Borrow<Command>
{
    let mut exit = EXIT_SUCCESS;
    for c in iter {
        exit = try_and_swallow_non_fatal!(c.borrow().run(env), env)
    }
    env.set_last_status(exit);
    Ok(exit)
}

/// Adds a number of local redirects to the specified environment, runs the provided closure,
/// then removes the local redirects and restores the previous file descriptors before returning.
fn run_with_local_redirections<'a, I, F, T>(env: &mut Environment, redirects: I, closure: F)
    -> Result<T>
    where I: IntoIterator<Item = &'a Redirect>,
          F: FnOnce(&mut Environment) -> Result<T>,
{
    // We'll swap the descriptors here temporarily
    // and hope the environment implementation doesn't mind
    // our shenanigans before we return them.
    let redirects = redirects.into_iter();
    let num_redirects = redirects.size_hint().0;
    // Old fds that will be locally overridden, but must be restored
    // once the compound command has finished executing.
    let mut fdes_backup = HashMap::with_capacity(num_redirects);
    // Locally overriden/newly opened fds only for this compound command. They must all
    // be removed from the environement when the compound command finishes.
    let mut overriden_fds = HashSet::with_capacity(num_redirects);

    let mut io_err = None;
    for io in redirects {
        match io.eval(env) {
            // Make sure we cleanup and restore the environment
            // before propagating any errors to the caller.
            Err(e) => {
                io_err = Some(e);
                break;
            },

            Ok((fd, fdes_and_perms)) => {
                // Only backup any descriptor which has NOT already been LOCALLY
                // overriden, e.g. if `2>err` was already in the environment, but
                // `2>foo 2>bar` are specified as local overrides, only `2>err`
                // should be backed up.
                if !overriden_fds.contains(&fd) {
                    if let Some((old_fdes, old_perms)) = env.file_desc(fd) {
                        let old_backup = fdes_backup.insert(fd, (old_fdes.clone(), old_perms));
                        // Sanity check that we aren't somehow "doubly-backing up" descriptors
                        // which would be an indication of us doing something wrong...
                        debug_assert!(old_backup.is_none());
                    }
                }

                env.close_file_desc(fd);
                overriden_fds.insert(fd);

                fdes_and_perms.map(|(fdes, perms)| env.set_file_desc(fd, fdes, perms));
            },
        }
    }

    let ret = match io_err {
        Some(err) => Err(err),
        None => closure(env),
    };

    // We have to make sure we actually close all newly inserted
    // fds before returning, restoring the old ones won't be enough.
    for fd in overriden_fds {
        env.close_file_desc(fd);
    }

    // Restore any descriptors we override for any reason before the compound command
    for (fd, (fdes, perms)) in fdes_backup {
        env.set_file_desc(fd, fdes, perms);
    }

    ret
}

#[cfg(test)]
mod tests {
    extern crate tempdir;

    use libc;

    use self::tempdir::TempDir;
    use std::cell::RefCell;
    use std::fs::OpenOptions;
    use std::io::{Read, Write};
    use std::path::PathBuf;
    use std::rc::Rc;
    use std::thread;
    use super::{EXIT_CMD_NOT_FOUND, EXIT_ERROR, EXIT_SUCCESS};
    use super::io::{FileDesc, Permissions};
    use super::*;
    use syntax::ast::{Arith, Command, CompoundCommand, SimpleCommand, Parameter, ParameterSubstitution, Redirect, Word};

    macro_rules! mktmp {
        () => {
            TempDir::new(concat!("test-", module_path!(), "-", line!(), "-", column!())).unwrap()
        }
    }

    struct MockFn<F: FnMut(&mut Environment) -> Result<ExitStatus>> {
        callback: RefCell<F>,
    }

    impl<F: FnMut(&mut Environment) -> Result<ExitStatus>> MockFn<F> {
        fn new(f: F) -> Rc<Self> {
            Rc::new(MockFn { callback: RefCell::new(f) })
        }
    }

    impl<F: FnMut(&mut Environment) -> Result<ExitStatus>> Run for MockFn<F> {
        fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
            (&mut *self.callback.borrow_mut())(env)
        }
    }

    struct MockFnRecursive<F: Fn(&mut Environment) -> Result<ExitStatus>> {
        callback: F,
    }

    impl<F: Fn(&mut Environment) -> Result<ExitStatus>> MockFnRecursive<F> {
        fn new(f: F) -> Rc<Self> {
            Rc::new(MockFnRecursive { callback: f })
        }
    }

    impl<F: Fn(&mut Environment) -> Result<ExitStatus>> Run for MockFnRecursive<F> {
        fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
            (self.callback)(env)
        }
    }

    fn file_desc() -> FileDesc {
        let path = if cfg!(windows) { "NUL" } else { "/dev/null" };
        OpenOptions::new().read(true).write(true).open(path).unwrap().into()
    }

    macro_rules! cmd_unboxed {
        ($cmd:expr)                  => { cmd_unboxed!($cmd,) };
        ($cmd:expr, $($arg:expr),*,) => { cmd_unboxed!($cmd, $($arg),*) };
        ($cmd:expr, $($arg:expr),* ) => {
            Command::Simple(Box::new(SimpleCommand {
                cmd: Some((Word::Literal(String::from($cmd)), vec!($($arg),*))),
                vars: vec!(),
                io: vec!(),
            }))
        };
    }

    macro_rules! cmd {
        ($cmd:expr)                  => { cmd!($cmd,) };
        ($cmd:expr, $($arg:expr),*,) => { cmd!($cmd, $($arg),*) };
        ($cmd:expr, $($arg:expr),* ) => { Box::new(cmd_unboxed!($cmd, $($arg),*)) }
    }

    fn exit(status: u8) -> Box<Command> {
        cmd!("sh", Word::Literal(String::from("-c")), Word::SingleQuoted(format!("exit {}", status)))
    }

    fn true_cmd() -> Box<Command> { exit(0) }
    fn false_cmd() -> Box<Command> { exit(1) }

    #[test]
    fn test_fields_is_null_single_empty_string() {
        assert_eq!(Fields::Single(Rc::new(String::from(""))).is_null(), true);
    }

    #[test]
    fn test_fields_is_null_single_non_empty_string() {
        assert_eq!(Fields::Single(Rc::new(String::from("foo"))).is_null(), false);
    }

    #[test]
    fn test_fields_is_null_many_one_empty_string() {
        let strs = vec!(
            Rc::new(String::from("foo")),
            Rc::new(String::from("")),
            Rc::new(String::from("bar")),
        );
        let fields = vec!(
            Fields::At(strs.clone()),
            Fields::Star(strs.clone()),
            Fields::Many(strs.clone()),
        );

        for f in fields {
            assert_eq!(f.is_null(), false);
        }
    }

    #[test]
    fn test_fields_is_null_many_empty_string() {
        let empty = Rc::new(String::from(""));
        let strs = vec!(
            empty.clone(),
            empty.clone(),
            empty.clone(),
        );

        let fields = vec!(
            Fields::At(strs.clone()),
            Fields::Star(strs.clone()),
            Fields::Many(strs.clone()),
        );

        for f in fields {
            assert_eq!(f.is_null(), true);
        }
    }

    #[test]
    fn test_fields_join_single() {
        let s = Rc::new(String::from("foo"));
        assert_eq!(Fields::Single(s.clone()).join(), s);
    }

    #[test]
    fn test_fields_join_multiple_only_keeps_non_empty_strings_before_joining_with_space() {
        let strs = vec!(
            Rc::new(String::from("foo")),
            Rc::new(String::from("")),
            Rc::new(String::from("bar")),
        );

        let fields = vec!(
            Fields::At(strs.clone()),
            Fields::Star(strs.clone()),
            Fields::Many(strs.clone()),
        );

        for f in fields {
            assert_eq!(&*f.join(), "foo bar");
        }
    }

    #[test]
    fn test_env_name() {
        let name = "shell";
        let env = Env::with_config(Some(String::from(name)), None, None, None).unwrap();
        assert_eq!(&**env.name(), name);
        assert_eq!(&**env.arg(0).unwrap(), name);
    }

    #[test]
    fn test_env_name_should_be_same_in_child_environment() {
        let name = "shell";
        let env = Env::with_config(Some(String::from(name)), None, None, None).unwrap();
        let child = env.sub_env();
        assert_eq!(&**child.name(), name);
        assert_eq!(&**child.arg(0).unwrap(), name);
    }

    #[test]
    fn test_env_set_and_get_var() {
        let name = "var";
        let value = "value";
        let mut env = Env::new().unwrap();
        assert_eq!(env.var(name), None);
        env.set_var(String::from(name), Rc::new(String::from(value)));
        assert_eq!(&**env.var(name).unwrap(), value);
    }

    #[test]
    fn test_env_set_var_in_parent_visible_in_child() {
        let name = "var";
        let value = "value";
        let mut parent = Env::new().unwrap();
        parent.set_var(String::from(name), Rc::new(String::from(value)));
        assert_eq!(&**parent.sub_env().var(name).unwrap(), value);
    }

    #[test]
    fn test_env_set_var_in_child_should_not_affect_parent() {
        let parent_name = "parent-var";
        let parent_value = "parent-value";
        let child_name = "child-var";
        let child_value = "child-value";

        let mut parent = Env::new().unwrap();
        parent.set_var(String::from(parent_name), Rc::new(String::from(parent_value)));

        {
            let mut child = parent.sub_env();
            child.set_var(String::from(parent_name), Rc::new(String::from(child_value)));
            child.set_var(String::from(child_name), Rc::new(String::from(child_value)));
            assert_eq!(&**child.var(parent_name).unwrap(), child_value);
            assert_eq!(&**child.var(child_name).unwrap(), child_value);

            assert_eq!(&**parent.var(parent_name).unwrap(), parent_value);
            assert_eq!(parent.var(child_name), None);
        }

        assert_eq!(&**parent.var(parent_name).unwrap(), parent_value);
        assert_eq!(parent.var(child_name), None);
    }

    #[test]
    fn test_env_set_and_get_last_status() {
        let exit = ExitStatus::Signal(9);
        let mut env = Env::new().unwrap();
        env.set_last_status(exit);
        assert_eq!(env.last_status(), exit);
    }

    #[test]
    fn test_env_set_last_status_in_parent_visible_in_child() {
        let exit = ExitStatus::Signal(9);
        let mut parent = Env::new().unwrap();
        parent.set_last_status(exit);
        assert_eq!(parent.sub_env().last_status(), exit);
    }

    #[test]
    fn test_env_set_last_status_in_child_should_not_affect_parent() {
        let parent_exit = ExitStatus::Signal(9);
        let mut parent = Env::new().unwrap();
        parent.set_last_status(parent_exit);

        {
            let child_exit = EXIT_ERROR;
            let mut child = parent.sub_env();
            assert_eq!(child.last_status(), parent_exit);

            child.set_last_status(child_exit);
            assert_eq!(child.last_status(), child_exit);

            assert_eq!(parent.last_status(), parent_exit);
        }

        assert_eq!(parent.last_status(), parent_exit);
    }

    #[test]
    fn test_env_set_and_run_function() {
        let fn_name_owned = String::from("foo");
        let fn_name = Rc::new(fn_name_owned.clone());

        let exit = EXIT_ERROR;
        let mut env = Env::new().unwrap();
        assert_eq!(env.has_function(&*fn_name), false);
        assert!(env.run_function(fn_name.clone(), vec!()).is_none());

        env.set_function(fn_name_owned, MockFn::new(move |_| Ok(exit)));
        assert_eq!(env.has_function(&*fn_name), true);
        assert_eq!(env.run_function(fn_name, vec!()), Some(Ok(exit)));
    }

    #[test]
    fn test_env_set_function_in_parent_visible_in_child() {
        let fn_name_owned = String::from("foo");
        let fn_name = Rc::new(fn_name_owned.clone());

        let exit = EXIT_ERROR;
        let mut parent = Env::new().unwrap();
        parent.set_function(fn_name_owned, MockFn::new(move |_| Ok(exit)));

        {
            let mut child = parent.sub_env();
            assert_eq!(child.has_function(&*fn_name), true);
            assert_eq!(child.run_function(fn_name, vec!()), Some(Ok(exit)));
        }
    }

    #[test]
    fn test_env_set_function_in_child_should_not_affect_parent() {
        let fn_name_owned = String::from("foo");
        let fn_name = Rc::new(fn_name_owned.clone());

        let exit = EXIT_ERROR;
        let mut parent = Env::new().unwrap();

        {
            let mut child = parent.sub_env();
            child.set_function(fn_name_owned, MockFn::new(move |_| Ok(exit)));
            assert_eq!(child.has_function(&*fn_name), true);
            assert_eq!(child.run_function(fn_name.clone(), vec!()), Some(Ok(exit)));
        }

        assert_eq!(parent.has_function(&*fn_name), false);
        assert!(parent.run_function(fn_name, vec!()).is_none());
    }

    #[test]
    fn test_env_run_function_should_affect_arguments_and_name_within_function() {
        let shell_name_owned = String::from("shell");
        let shell_name = Rc::new(shell_name_owned.clone());
        let parent_args = vec!(
            String::from("parent arg1"),
            String::from("parent arg2"),
            String::from("parent arg3"),
        );

        let mut env = Env::with_config(Some(shell_name_owned), Some(parent_args.clone()), None, None).unwrap();

        let fn_name_owned = String::from("fn name");
        let fn_name = Rc::new(fn_name_owned.clone());
        let args = vec!(
            Rc::new(String::from("child arg1")),
            Rc::new(String::from("child arg2")),
            Rc::new(String::from("child arg3")),
        );

        {
            let args = args.clone();
            let fn_name = fn_name.clone();
            env.set_function(fn_name_owned, MockFn::new(move |env| {
                assert_eq!(env.args(), &*args);
                assert_eq!(env.args_len(), args.len());
                assert_eq!(env.name(), &fn_name);
                assert_eq!(env.arg(0), Some(&fn_name));

                let mut env_args = Vec::with_capacity(args.len());
                for idx in 0..args.len() {
                    env_args.push(env.arg(idx+1).unwrap());
                }

                let args: Vec<&Rc<String>> = args.iter().collect();
                assert_eq!(env_args, args);
                assert_eq!(env.arg(args.len()+1), None);
                Ok(EXIT_SUCCESS)
            }));
        }

        env.run_function(fn_name, args.clone());

        let parent_args: Vec<Rc<String>> = parent_args.into_iter().map(Rc::new).collect();
        assert_eq!(env.args(), &*parent_args);
        assert_eq!(env.args_len(), parent_args.len());
        assert_eq!(env.name(), &shell_name);
        assert_eq!(env.arg(0), Some(&shell_name));

        let mut env_parent_args = Vec::with_capacity(parent_args.len());
        for idx in 0..parent_args.len() {
            env_parent_args.push(env.arg(idx+1).unwrap());
        }

        assert_eq!(env_parent_args, parent_args.iter().collect::<Vec<&Rc<String>>>());
        assert_eq!(env.arg(parent_args.len()+1), None);
    }

    #[test]
    fn test_env_run_function_can_be_recursive() {
        let fn_name_owned = String::from("fn name");
        let fn_name = Rc::new(fn_name_owned.clone());

        let mut env = Env::new().unwrap();
        {
            let fn_name = fn_name.clone();
            let num_calls = 3usize;
            let depth = ::std::cell::Cell::new(num_calls);

            env.set_function(fn_name_owned, MockFnRecursive::new(move |env| {
                let num_calls = depth.get().saturating_sub(1);
                env.set_var(format!("var{}", num_calls), Rc::new(num_calls.to_string()));

                if num_calls != 0 {
                    depth.set(num_calls);
                    env.run_function(fn_name.clone(), vec!()).unwrap()
                } else {
                    Ok(EXIT_SUCCESS)
                }
            }));
        }

        assert_eq!(env.var("var0"), None);
        assert_eq!(env.var("var1"), None);
        assert_eq!(env.var("var2"), None);

        assert!(env.run_function(fn_name.clone(), vec!()).unwrap().unwrap().success());

        assert_eq!(&**env.var("var0").unwrap(), "0");
        assert_eq!(&**env.var("var1").unwrap(), "1");
        assert_eq!(&**env.var("var2").unwrap(), "2");
    }

    #[test]
    fn test_env_run_function_nested_calls_do_not_destroy_upper_args() {
        let fn_name_owned = String::from("fn name");
        let fn_name = Rc::new(fn_name_owned.clone());

        let mut env = Env::new().unwrap();
        {
            let fn_name = fn_name.clone();
            let num_calls = 3usize;
            let depth = ::std::cell::Cell::new(num_calls);

            env.set_function(fn_name_owned, MockFnRecursive::new(move |env| {
                let num_calls = depth.get().saturating_sub(1);

                if num_calls != 0 {
                    depth.set(num_calls);
                    let cur_args: Vec<_> = env.args().iter().cloned().collect();

                    let mut next_args = cur_args.clone();
                    next_args.reverse();
                    next_args.push(Rc::new(format!("arg{}", num_calls)));

                    let ret = env.run_function(fn_name.clone(), next_args).unwrap();
                    assert_eq!(&*cur_args, &*env.args());
                    ret
                } else {
                    Ok(EXIT_SUCCESS)
                }
            }));
        }

        assert!(env.run_function(fn_name.clone(), vec!(
            Rc::new(String::from("first")),
            Rc::new(String::from("second")),
            Rc::new(String::from("third")),
        )).unwrap().unwrap().success());
    }

    #[test]
    fn test_env_run_function_redirections_should_work() {
        let fn_name = String::from("fn name");
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push(String::from("out"));

        let mut env = Env::new().unwrap();

        let fn_cmd = Command::Function(fn_name.clone(), Rc::new(
            *cmd!("echo", Word::Param(Parameter::At))
        ));

        let cmd = SimpleCommand {
            cmd: Some((Word::Literal(String::from(fn_name)), vec!(Word::Literal(String::from("foobar"))))),
            vars: vec!(),
            io: vec!(Redirect::Write(None, Word::Literal(file_path.display().to_string()))),
        };

        assert_eq!(fn_cmd.run(&mut env), Ok(EXIT_SUCCESS));
        assert_eq!(cmd.run(&mut env), Ok(EXIT_SUCCESS));

        let mut read = String::new();
        Permissions::Read.open(&file_path).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "foobar\n");
    }

    #[test]
    fn test_env_inherit_env_vars_if_not_overridden() {
        let env = Env::new().unwrap();

        let mut vars: Vec<(String, String)> = ::std::env::vars().collect();
        vars.sort();
        let vars: Vec<(&str, &str)> = vars.iter().map(|&(ref k, ref v)| (&**k, &**v)).collect();
        let mut env_vars = env.env();
        env_vars.sort();
        assert_eq!(vars, env_vars);
    }

    #[test]
    fn test_env_get_env_var_visible_in_parent_and_child() {
        let name1 = "var1";
        let value1 = "value1";
        let name2 = "var2";
        let value2 = "value2";

        let env_vars = {
            let mut env_vars = vec!(
                (name1, value1),
                (name2, value2),
            );

            env_vars.sort();
            env_vars
        };

        let owned_vars = env_vars.iter().map(|&(k, v)| (String::from(k), String::from(v))).collect();
        let env = Env::with_config(None, None, Some(owned_vars), None).unwrap();
        let mut vars = env.env();
        vars.sort();
        assert_eq!(vars, env_vars);
        let child = env.sub_env();
        let mut vars = child.env();
        vars.sort();
        assert_eq!(vars, env_vars);
    }

    #[test]
    fn test_env_set_get_and_close_file_desc() {
        let fd = STDIN_FILENO;
        let perms = Permissions::ReadWrite;
        let file_desc = Rc::new(file_desc());

        let mut env = Env::new().unwrap();
        env.close_file_desc(fd);
        assert!(env.file_desc(fd).is_none());
        env.set_file_desc(fd, file_desc.clone(), perms);
        {
            let (got_file_desc, got_perms) = env.file_desc(fd).unwrap();
            assert_eq!(got_perms, perms);
            assert_eq!(&**got_file_desc as *const _, &*file_desc as *const _);
        }
        env.close_file_desc(fd);
        assert!(env.file_desc(fd).is_none());
    }

    #[test]
    fn test_env_set_file_desc_in_parent_visible_in_child() {
        let fd = STDIN_FILENO;
        let perms = Permissions::ReadWrite;
        let file_desc = Rc::new(file_desc());

        let mut env = Env::new().unwrap();
        env.set_file_desc(fd, file_desc.clone(), perms);
        let child = env.sub_env();
        let (got_file_desc, got_perms) = child.file_desc(fd).unwrap();
        assert_eq!(got_perms, perms);
        assert_eq!(&**got_file_desc as *const _, &*file_desc as *const _);
    }

    #[test]
    fn test_env_set_file_desc_in_child_should_not_affect_parent() {
        let fd = STDIN_FILENO;

        let mut parent = Env::new().unwrap();
        parent.close_file_desc(fd);
        assert!(parent.file_desc(fd).is_none());
        {
            let perms = Permissions::ReadWrite;
            let file_desc = Rc::new(file_desc());
            let mut child = parent.sub_env();
            child.set_file_desc(fd, file_desc.clone(), perms);
            let (got_file_desc, got_perms) = child.file_desc(fd).unwrap();
            assert_eq!(got_perms, perms);
            assert_eq!(&**got_file_desc as *const _, &*file_desc as *const _);
        }
        assert!(parent.file_desc(fd).is_none());
    }

    #[test]
    fn test_env_close_file_desc_in_child_should_not_affect_parent() {
        let fd = STDIN_FILENO;
        let perms = Permissions::ReadWrite;
        let file_desc = Rc::new(file_desc());

        let mut parent = Env::new().unwrap();
        parent.set_file_desc(fd, file_desc.clone(), perms);
        {
            let mut child = parent.sub_env();
            assert!(child.file_desc(fd).is_some());
            child.close_file_desc(fd);
            assert!(child.file_desc(fd).is_none());
        }
        let (got_file_desc, got_perms) = parent.file_desc(fd).unwrap();
        assert_eq!(got_perms, perms);
        assert_eq!(&**got_file_desc as *const _, &*file_desc as *const _);
    }

    #[test]
    fn test_env_report_error() {
        let io::Pipe { mut reader, writer } = io::Pipe::new().unwrap();

        let guard = thread::spawn(move || {
            let mut env = Env::new().unwrap();
            let writer = Rc::new(writer);
            env.set_file_desc(STDERR_FILENO, writer.clone(), Permissions::Write);
            env.report_error(RuntimeError::Expansion(ExpansionError::DivideByZero));
            env.close_file_desc(STDERR_FILENO);
            let mut writer = Rc::try_unwrap(writer).unwrap();
            writer.flush().unwrap();
            drop(writer);
        });

        let mut msg = String::new();
        reader.read_to_string(&mut msg).unwrap();
        guard.join().unwrap();
        assert!(msg.contains(&format!("{}", RuntimeError::Expansion(ExpansionError::DivideByZero))));
    }

    #[test]
    fn test_eval_parameter_with_set_vars() {
        let var1 = Rc::new(String::from("var1_value"));
        let var2 = Rc::new(String::from("var2_value"));
        let var3 = Rc::new(String::from("")); // var3 is set to the empty string

        let arg1 = String::from("arg1_value");
        let arg2 = String::from("arg2_value");
        let arg3 = String::from("arg3_value");

        let args = vec!(
            arg1.clone(),
            arg2.clone(),
            arg3.clone(),
        );

        let mut env = Env::with_config(None, Some(args.clone()), None, None).unwrap();
        env.set_var(String::from("var1"), var1.clone());
        env.set_var(String::from("var2"), var2.clone());
        env.set_var(String::from("var3"), var3.clone());

        let args: Vec<Rc<String>> = args.into_iter().map(Rc::new).collect();
        assert_eq!(Parameter::At.eval(&mut env), Some(Fields::At(args.clone())));
        assert_eq!(Parameter::Star.eval(&mut env), Some(Fields::Star(args.clone())));

        assert_eq!(Parameter::Dollar.eval(&mut env), Some(Fields::Single(Rc::new(unsafe {
            ::libc::getpid().to_string()
        }))));

        // FIXME: test these
        //assert_eq!(Parameter::Dash.eval(&mut env), ...);
        //assert_eq!(Parameter::Bang.eval(&mut env), ...);

        // Before anything is run it should be considered a success
        assert_eq!(Parameter::Question.eval(&mut env), Some(Fields::Single(Rc::new(String::from("0")))));
        env.set_last_status(ExitStatus::Code(3));
        assert_eq!(Parameter::Question.eval(&mut env), Some(Fields::Single(Rc::new(String::from("3")))));
        // Signals should have 128 added to them
        env.set_last_status(ExitStatus::Signal(5));
        assert_eq!(Parameter::Question.eval(&mut env), Some(Fields::Single(Rc::new(String::from("133")))));

        assert_eq!(Parameter::Positional(0).eval(&mut env), Some(Fields::Single(env.name().clone())));
        assert_eq!(Parameter::Positional(1).eval(&mut env), Some(Fields::Single(Rc::new(arg1))));
        assert_eq!(Parameter::Positional(2).eval(&mut env), Some(Fields::Single(Rc::new(arg2))));
        assert_eq!(Parameter::Positional(3).eval(&mut env), Some(Fields::Single(Rc::new(arg3))));

        assert_eq!(Parameter::Var(String::from("var1")).eval(&mut env), Some(Fields::Single(var1.clone())));
        assert_eq!(Parameter::Var(String::from("var2")).eval(&mut env), Some(Fields::Single(var2.clone())));
        assert_eq!(Parameter::Var(String::from("var3")).eval(&mut env), Some(Fields::Single(var3.clone())));

        assert_eq!(Parameter::Pound.eval(&mut env), Some(Fields::Single(Rc::new(String::from("3")))));
    }

    #[test]
    fn test_eval_parameter_with_unset_vars() {
        let mut env = Env::with_config(None, Some(vec!()), None, None).unwrap();

        assert_eq!(Parameter::At.eval(&mut env), Some(Fields::Zero));
        assert_eq!(Parameter::Star.eval(&mut env), Some(Fields::Zero));

        assert_eq!(Parameter::Positional(0).eval(&mut env), Some(Fields::Single(env.name().clone())));
        assert_eq!(Parameter::Positional(1).eval(&mut env), None);
        assert_eq!(Parameter::Positional(2).eval(&mut env), None);

        assert_eq!(Parameter::Var(String::from("var1")).eval(&mut env), None);
        assert_eq!(Parameter::Var(String::from("var2")).eval(&mut env), None);

        assert_eq!(Parameter::Pound.eval(&mut env), Some(Fields::Single(Rc::new(String::from("0")))));
    }

    #[test]
    fn test_eval_arith() {
        use ::std::isize::MAX;

        macro_rules! lit {
            ($lit:expr) => { Box::new(Arith::Literal($lit)) }
        }

        let mut env = Env::new().unwrap();
        let env = &mut env;
        let var = String::from("var name");
        let var_value = 10;
        let var_string = String::from("var string");
        let var_string_value = "asdf";

        env.set_var(var.clone(),        Rc::new(String::from(var_value.to_string())));
        env.set_var(var_string.clone(), Rc::new(String::from(var_string_value.to_string())));

        assert_eq!(Arith::Literal(5).eval(env), Ok(5));

        assert_eq!(Arith::Var(var.clone()).eval(env), Ok(var_value));
        assert_eq!(Arith::Var(var_string.clone()).eval(env), Ok(0));
        assert_eq!(Arith::Var(String::from("missing var")).eval(env), Ok(0));

        assert_eq!(Arith::PostIncr(var.clone()).eval(env), Ok(var_value));
        assert_eq!(&**env.var(&var).unwrap(), &*(var_value + 1).to_string());
        assert_eq!(Arith::PostDecr(var.clone()).eval(env), Ok(var_value + 1));
        assert_eq!(&**env.var(&var).unwrap(), &*var_value.to_string());

        assert_eq!(Arith::PreIncr(var.clone()).eval(env), Ok(var_value + 1));
        assert_eq!(&**env.var(&var).unwrap(), &*(var_value + 1).to_string());
        assert_eq!(Arith::PreDecr(var.clone()).eval(env), Ok(var_value));
        assert_eq!(&**env.var(&var).unwrap(), &*var_value.to_string());

        assert_eq!(Arith::UnaryPlus(lit!(5)).eval(env), Ok(5));
        assert_eq!(Arith::UnaryPlus(lit!(-5)).eval(env), Ok(5));

        assert_eq!(Arith::UnaryMinus(lit!(5)).eval(env), Ok(-5));
        assert_eq!(Arith::UnaryMinus(lit!(-5)).eval(env), Ok(5));

        assert_eq!(Arith::BitwiseNot(lit!(5)).eval(env), Ok(!5));
        assert_eq!(Arith::BitwiseNot(lit!(0)).eval(env), Ok(!0));

        assert_eq!(Arith::LogicalNot(lit!(5)).eval(env), Ok(0));
        assert_eq!(Arith::LogicalNot(lit!(0)).eval(env), Ok(1));

        assert_eq!(Arith::Less(lit!(1), lit!(1)).eval(env), Ok(0));
        assert_eq!(Arith::Less(lit!(1), lit!(0)).eval(env), Ok(0));
        assert_eq!(Arith::Less(lit!(0), lit!(1)).eval(env), Ok(1));

        assert_eq!(Arith::LessEq(lit!(1), lit!(1)).eval(env), Ok(1));
        assert_eq!(Arith::LessEq(lit!(1), lit!(0)).eval(env), Ok(0));
        assert_eq!(Arith::LessEq(lit!(0), lit!(1)).eval(env), Ok(1));

        assert_eq!(Arith::Great(lit!(1), lit!(1)).eval(env), Ok(0));
        assert_eq!(Arith::Great(lit!(1), lit!(0)).eval(env), Ok(1));
        assert_eq!(Arith::Great(lit!(0), lit!(1)).eval(env), Ok(0));

        assert_eq!(Arith::GreatEq(lit!(1), lit!(1)).eval(env), Ok(1));
        assert_eq!(Arith::GreatEq(lit!(1), lit!(0)).eval(env), Ok(1));
        assert_eq!(Arith::GreatEq(lit!(0), lit!(1)).eval(env), Ok(0));

        assert_eq!(Arith::Eq(lit!(0), lit!(1)).eval(env), Ok(0));
        assert_eq!(Arith::Eq(lit!(1), lit!(1)).eval(env), Ok(1));

        assert_eq!(Arith::NotEq(lit!(0), lit!(1)).eval(env), Ok(1));
        assert_eq!(Arith::NotEq(lit!(1), lit!(1)).eval(env), Ok(0));

        assert_eq!(Arith::Pow(lit!(4), lit!(3)).eval(env), Ok(64));
        assert_eq!(Arith::Pow(lit!(4), lit!(0)).eval(env), Ok(1));
        assert_eq!(Arith::Pow(lit!(4), lit!(-2)).eval(env), Err(ExpansionError::NegativeExponent));
        assert_eq!(env.last_status(), EXIT_ERROR);
        env.set_last_status(EXIT_SUCCESS);

        assert_eq!(Arith::Div(lit!(6), lit!(2)).eval(env), Ok(3));
        assert_eq!(Arith::Div(lit!(1), lit!(0)).eval(env), Err(ExpansionError::DivideByZero));
        assert_eq!(env.last_status(), EXIT_ERROR);
        env.set_last_status(EXIT_SUCCESS);

        assert_eq!(Arith::Modulo(lit!(6), lit!(5)).eval(env), Ok(1));
        assert_eq!(Arith::Modulo(lit!(1), lit!(0)).eval(env), Err(ExpansionError::DivideByZero));
        assert_eq!(env.last_status(), EXIT_ERROR);
        env.set_last_status(EXIT_SUCCESS);

        assert_eq!(Arith::Mult(lit!(3), lit!(2)).eval(env), Ok(6));
        assert_eq!(Arith::Mult(lit!(1), lit!(0)).eval(env), Ok(0));

        assert_eq!(Arith::Add(lit!(3), lit!(2)).eval(env), Ok(5));
        assert_eq!(Arith::Add(lit!(1), lit!(0)).eval(env), Ok(1));

        assert_eq!(Arith::Sub(lit!(3), lit!(2)).eval(env), Ok(1));
        assert_eq!(Arith::Sub(lit!(0), lit!(1)).eval(env), Ok(-1));

        assert_eq!(Arith::ShiftLeft(lit!(4), lit!(3)).eval(env), Ok(32));

        assert_eq!(Arith::ShiftRight(lit!(32), lit!(2)).eval(env), Ok(8));

        assert_eq!(Arith::BitwiseAnd(lit!(135), lit!(97)).eval(env), Ok(1));
        assert_eq!(Arith::BitwiseAnd(lit!(135), lit!(0)).eval(env), Ok(0));
        assert_eq!(Arith::BitwiseAnd(lit!(135), lit!(MAX)).eval(env), Ok(135));

        assert_eq!(Arith::BitwiseXor(lit!(135), lit!(150)).eval(env), Ok(17));
        assert_eq!(Arith::BitwiseXor(lit!(135), lit!(0)).eval(env), Ok(135));
        assert_eq!(Arith::BitwiseXor(lit!(135), lit!(MAX)).eval(env), Ok(135 ^ MAX));

        assert_eq!(Arith::BitwiseOr(lit!(135), lit!(97)).eval(env), Ok(231));
        assert_eq!(Arith::BitwiseOr(lit!(135), lit!(0)).eval(env), Ok(135));
        assert_eq!(Arith::BitwiseOr(lit!(135), lit!(MAX)).eval(env), Ok(MAX));

        assert_eq!(Arith::LogicalAnd(lit!(135), lit!(97)).eval(env), Ok(1));
        assert_eq!(Arith::LogicalAnd(lit!(135), lit!(0)).eval(env), Ok(0));
        assert_eq!(Arith::LogicalAnd(lit!(0), lit!(0)).eval(env), Ok(0));

        assert_eq!(Arith::LogicalOr(lit!(135), lit!(97)).eval(env), Ok(1));
        assert_eq!(Arith::LogicalOr(lit!(135), lit!(0)).eval(env), Ok(1));
        assert_eq!(Arith::LogicalOr(lit!(0), lit!(0)).eval(env), Ok(0));

        assert_eq!(Arith::Ternary(lit!(2), lit!(4), lit!(5)).eval(env), Ok(4));
        assert_eq!(Arith::Ternary(lit!(0), lit!(4), lit!(5)).eval(env), Ok(5));

        assert_eq!(&**env.var(&var).unwrap(), &*(var_value).to_string());
        assert_eq!(Arith::Assign(var.clone(), lit!(42)).eval(env), Ok(42));
        assert_eq!(&**env.var(&var).unwrap(), "42");

        assert_eq!(Arith::Sequence(vec!(
            Arith::Assign(String::from("x"), lit!(5)),
            Arith::Assign(String::from("y"), lit!(10)),
            Arith::Add(
                Box::new(Arith::PreIncr(String::from("x"))),
                Box::new(Arith::PostDecr(String::from("y")))
            ),
        )).eval(env), Ok(16));

        assert_eq!(&**env.var("x").unwrap(), "6");
        assert_eq!(&**env.var("y").unwrap(), "9");
    }

    #[test]
    fn test_eval_parameter_substitution_len() {
        use syntax::ast::ParameterSubstitution::Len;

        let name  = String::from("shell name");
        let var   = String::from("var");
        let value = String::from("foo bar");
        let mut env = Env::with_config(Some(name.clone()), Some(vec!(
            String::from("one"),
            String::from("two"),
            String::from("three"),
        )), None, None).unwrap();

        env.set_var(var.clone(), Rc::new(value.clone()));

        let cases = vec!(
            (Parameter::At,     3),
            (Parameter::Star,   3),
            (Parameter::Pound,  1),
            (Parameter::Dollar, unsafe { libc::getpid().to_string().len() }),

            // FIXME: test these as well
            //Parameter::Dash,
            //Parameter::Bang,

            (Parameter::Positional(0),                name.len()),
            (Parameter::Positional(3),                5),
            (Parameter::Positional(5),                0),
            (Parameter::Var(var),                     value.len()),
            (Parameter::Var(String::from("missing")), 0),
        );

        for (param, result) in cases {
            assert_eq!(Len(param).eval(&mut env), Ok(Fields::Single(Rc::new(result.to_string()))));
        }

        env.set_last_status(EXIT_SUCCESS);
        assert_eq!(Len(Parameter::Question).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("1")))));
        env.set_last_status(ExitStatus::Signal(5));
        assert_eq!(Len(Parameter::Question).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("3")))));
    }

    #[test]
    fn test_eval_parameter_substitution_arith() {
        use syntax::ast::ParameterSubstitution::Arithmetic;

        let mut env = Env::new().unwrap();
        assert_eq!(Arithmetic(None).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("0")))));
        assert_eq!(Arithmetic(Some(Arith::Literal(5))).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("5")))));
        assert!(Arithmetic(Some(
            Arith::Div(Box::new(Arith::Literal(1)), Box::new(Arith::Literal(0)))
        )).eval(&mut env).is_err());
        assert_eq!(env.last_status(), EXIT_ERROR);
    }

    #[test]
    fn test_eval_parameter_substitution_default() {
        use syntax::ast::ParameterSubstitution::Default;

        let var       = String::from("non_empty_var");
        let var_value = String::from("foobar");
        let var_null  = String::from("var with empty value");
        let null      = String::new();
        let var_unset = String::from("var_not_set_in_env");

        let default_value = String::from("some default value");
        let default = Word::Literal(default_value.clone());

        let mut env = Env::new().unwrap();
        env.set_var(var.clone(),      Rc::new(var_value.clone()));
        env.set_var(var_null.clone(), Rc::new(null.clone()));

        let default_value = Fields::Single(Rc::new(default_value));
        let var_value     = Fields::Single(Rc::new(var_value));
        let null          = Fields::Single(Rc::new(null));

        // Strict with default
        let subst = Default(true, Parameter::Var(var.clone()), Some(default.clone()));
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));
        let subst = Default(true, Parameter::Var(var_null.clone()), Some(default.clone()));
        assert_eq!(subst.eval(&mut env), Ok(default_value.clone()));
        let subst = Default(true, Parameter::Var(var_unset.clone()), Some(default.clone()));
        assert_eq!(subst.eval(&mut env), Ok(default_value.clone()));

        // Strict without default
        let subst = Default(true, Parameter::Var(var.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));
        let subst = Default(true, Parameter::Var(var_null.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        let subst = Default(true, Parameter::Var(var_unset.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));


        // Non-strict with default
        let subst = Default(false, Parameter::Var(var.clone()), Some(default.clone()));
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));
        let subst = Default(false, Parameter::Var(var_null.clone()), Some(default.clone()));
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        let subst = Default(false, Parameter::Var(var_unset.clone()), Some(default.clone()));
        assert_eq!(subst.eval(&mut env), Ok(default_value.clone()));

        // Non-strict without default
        let subst = Default(false, Parameter::Var(var.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));
        let subst = Default(false, Parameter::Var(var_null.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        let subst = Default(false, Parameter::Var(var_unset.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));

        // Args have one non-null argument
        {
            let args = vec!(
                String::from(""),
                String::from("foo"),
                String::from(""),
                String::from(""),
            );

            let args_value = args.iter().cloned().map(Rc::new).collect::<Vec<_>>();
            let mut env = Env::with_config(None, Some(args), None, None).unwrap();

            let subst = Default(true, Parameter::At, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(Fields::At(args_value.clone())));
            let subst = Default(true, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(Fields::At(args_value.clone())));
            let subst = Default(true, Parameter::Star, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(Fields::Star(args_value.clone())));
            let subst = Default(true, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(Fields::Star(args_value.clone())));

            let subst = Default(false, Parameter::At, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(Fields::At(args_value.clone())));
            let subst = Default(false, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(Fields::At(args_value.clone())));
            let subst = Default(false, Parameter::Star, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(Fields::Star(args_value.clone())));
            let subst = Default(false, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(Fields::Star(args_value.clone())));
        }

        // Args all null
        {
            let mut env = Env::with_config(None, Some(vec!(
                String::from(""),
                String::from(""),
                String::from(""),
            )), None, None).unwrap();

            let subst = Default(true, Parameter::At, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(default_value.clone()));
            let subst = Default(true, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Default(true, Parameter::Star, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(default_value.clone()));
            let subst = Default(true, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));

            let subst = Default(false, Parameter::At, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Default(false, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Default(false, Parameter::Star, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Default(false, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        }

        // Args not set
        {
            let mut env = Env::new().unwrap();

            let subst = Default(true, Parameter::At, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(default_value.clone()));
            let subst = Default(true, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Default(true, Parameter::Star, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(default_value.clone()));
            let subst = Default(true, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));

            let subst = Default(false, Parameter::At, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Default(false, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Default(false, Parameter::Star, Some(default.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Default(false, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        }
    }

    #[test]
    fn test_eval_parameter_substitution_assign() {
        use syntax::ast::ParameterSubstitution::Assign;

        let var         = String::from("non_empty_var");
        let var_value   = String::from("foobar");
        let var_null    = String::from("var with empty value");
        let var_unset   = String::from("var_not_set_in_env");
        let assig_value = String::from("assigned value");

        let assig = Word::Literal(assig_value.clone());
        let null = Rc::new(String::new());

        let mut env = Env::new().unwrap();
        env.set_var(var.clone(), Rc::new(var_value.clone()));

        let assig_var_value = Rc::new(assig_value);
        let var_value       = Fields::Single(Rc::new(var_value));
        let assig_value     = Fields::Single(assig_var_value.clone());
        let null_value      = Fields::Single(null.clone());

        // Variable set and non-null
        let subst = Assign(true, Parameter::Var(var.clone()), Some(assig.clone()));
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));
        let subst = Assign(true, Parameter::Var(var.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));
        let subst = Assign(false, Parameter::Var(var.clone()), Some(assig.clone()));
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));
        let subst = Assign(false, Parameter::Var(var.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));


        // Variable set but null
        env.set_var(var_null.clone(), null.clone());
        let subst = Assign(true, Parameter::Var(var_null.clone()), Some(assig.clone()));
        assert_eq!(subst.eval(&mut env), Ok(assig_value.clone()));
        assert_eq!(env.var(&var_null), Some(&assig_var_value));

        env.set_var(var_null.clone(), null.clone());
        let subst = Assign(true, Parameter::Var(var_null.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null_value.clone()));
        assert_eq!(env.var(&var_null), Some(&null));

        env.set_var(var_null.clone(), null.clone());
        let subst = Assign(false, Parameter::Var(var_null.clone()), Some(assig.clone()));
        assert_eq!(subst.eval(&mut env), Ok(null_value.clone()));
        assert_eq!(env.var(&var_null), Some(&null));

        env.set_var(var_null.clone(), null.clone());
        let subst = Assign(false, Parameter::Var(var_null.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null_value.clone()));
        assert_eq!(env.var(&var_null), Some(&null));


        // Variable unset
        {
            let mut env = env.sub_env();
            let subst = Assign(true, Parameter::Var(var_unset.clone()), Some(assig.clone()));
            assert_eq!(subst.eval(&mut *env), Ok(assig_value.clone()));
            assert_eq!(env.var(&var_unset), Some(&assig_var_value));
        }

        {
            let mut env = env.sub_env();
            let subst = Assign(true, Parameter::Var(var_unset.clone()), None);
            assert_eq!(subst.eval(&mut *env), Ok(null_value.clone()));
            assert_eq!(env.var(&var_unset), Some(&null));
        }

        {
            let mut env = env.sub_env();
            let subst = Assign(false, Parameter::Var(var_unset.clone()), Some(assig.clone()));
            assert_eq!(subst.eval(&mut *env), Ok(assig_value.clone()));
            assert_eq!(env.var(&var_unset), Some(&assig_var_value));
        }

        {
            let mut env = env.sub_env();
            let subst = Assign(false, Parameter::Var(var_unset.clone()), None);
            assert_eq!(subst.eval(&mut *env), Ok(null_value.clone()));
            assert_eq!(env.var(&var_unset), Some(&null));
        }

        let unassignable_params = vec!(
            Parameter::At,
            Parameter::Star,
            Parameter::Dash,
            Parameter::Bang,

            // These parameters can't ever really be null or undefined,
            // so we won't test for them.
            //Parameter::Pound,
            //Parameter::Question,
            //Parameter::Dollar,
        );

        for param in unassignable_params {
            let err = ExpansionError::BadAssig(param.clone());
            let subst = Assign(true, param.clone(), Some(assig.clone()));
            assert_eq!(subst.eval(&mut env), Err(RuntimeError::Expansion(err.clone())));
            assert_eq!(env.last_status(), EXIT_ERROR);
        }
    }

    #[test]
    fn test_eval_parameter_substitution_error() {
        use syntax::ast::ParameterSubstitution::Error;

        let var       = String::from("non_empty_var");
        let var_value = String::from("foobar");
        let var_null  = String::from("var with empty value");
        let null      = String::new();
        let var_unset = String::from("var_not_set_in_env");
        let err_msg   = String::from("this variable is not set!");

        let mut env = Env::new().unwrap();
        env.set_var(var.clone(),      Rc::new(var_value.clone()));
        env.set_var(var_null.clone(), Rc::new(null.clone()));

        let var_value = Fields::Single(Rc::new(var_value));
        let null      = Fields::Single(Rc::new(null));

        let err_null  = RuntimeError::Expansion(
            ExpansionError::EmptyParameter(Parameter::Var(var_null.clone()),  Rc::new(err_msg.clone())));
        let err_unset = RuntimeError::Expansion(
            ExpansionError::EmptyParameter(Parameter::Var(var_unset.clone()), Rc::new(err_msg.clone())));
        let err_at    = RuntimeError::Expansion(
            ExpansionError::EmptyParameter(Parameter::At,                     Rc::new(err_msg.clone())));
        let err_star  = RuntimeError::Expansion(
            ExpansionError::EmptyParameter(Parameter::Star,                   Rc::new(err_msg.clone())));

        let err_msg = Word::Literal(err_msg);

        // Strict with error message
        let subst = Error(true, Parameter::Var(var.clone()), Some(err_msg.clone()));
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));

        env.set_last_status(EXIT_SUCCESS);
        let subst = Error(true, Parameter::Var(var_null.clone()), Some(err_msg.clone()));
        assert_eq!(subst.eval(&mut env).as_ref(), Err(&err_null));
        assert_eq!(env.last_status(), EXIT_ERROR);

        env.set_last_status(EXIT_SUCCESS);
        let subst = Error(true, Parameter::Var(var_unset.clone()), Some(err_msg.clone()));
        assert_eq!(subst.eval(&mut env).as_ref(), Err(&err_unset));
        assert_eq!(env.last_status(), EXIT_ERROR);


        // Strict without error message
        let subst = Error(true, Parameter::Var(var.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));

        env.set_last_status(EXIT_SUCCESS);
        let eval = Error(true, Parameter::Var(var_null.clone()), None).eval(&mut env);
        if let Err(RuntimeError::Expansion(ExpansionError::EmptyParameter(param, _))) = eval {
            assert_eq!(param, Parameter::Var(var_null.clone()));
            assert_eq!(env.last_status(), EXIT_ERROR);
        } else {
            panic!("Unexpected evaluation: {:?}", eval);
        }

        env.set_last_status(EXIT_SUCCESS);
        let eval = Error(true, Parameter::Var(var_unset.clone()), None).eval(&mut env);
        if let Err(RuntimeError::Expansion(ExpansionError::EmptyParameter(param, _))) = eval {
            assert_eq!(param, Parameter::Var(var_unset.clone()));
            assert_eq!(env.last_status(), EXIT_ERROR);
        } else {
            panic!("Unexpected evaluation: {:?}", eval);
        }


        // Non-strict with error message
        let subst = Error(false, Parameter::Var(var.clone()), Some(err_msg.clone()));
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));

        let subst = Error(false, Parameter::Var(var_null.clone()), Some(err_msg.clone()));
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));

        env.set_last_status(EXIT_SUCCESS);
        let subst = Error(false, Parameter::Var(var_unset.clone()), Some(err_msg.clone()));
        assert_eq!(subst.eval(&mut env).as_ref(), Err(&err_unset));
        assert_eq!(env.last_status(), EXIT_ERROR);


        // Non-strict without error message
        let subst = Error(false, Parameter::Var(var.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(var_value.clone()));

        let subst = Error(false, Parameter::Var(var_null.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));

        env.set_last_status(EXIT_SUCCESS);
        let eval = Error(false, Parameter::Var(var_unset.clone()), None).eval(&mut env);
        if let Err(RuntimeError::Expansion(ExpansionError::EmptyParameter(param, _))) = eval {
            assert_eq!(param, Parameter::Var(var_unset.clone()));
            assert_eq!(env.last_status(), EXIT_ERROR);
        } else {
            panic!("Unexpected evaluation: {:?}", eval);
        }


        // Args have one non-null argument
        {
            let args = vec!(
                String::from(""),
                String::from("foo"),
                String::from(""),
                String::from(""),
            );

            let args_value = args.iter().cloned().map(Rc::new).collect::<Vec<_>>();
            let mut env = Env::with_config(None, Some(args), None, None).unwrap();

            let subst = Error(true, Parameter::At, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env), Ok(Fields::At(args_value.clone())));
            let subst = Error(true, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(Fields::At(args_value.clone())));
            let subst = Error(true, Parameter::Star, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env), Ok(Fields::Star(args_value.clone())));
            let subst = Error(true, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(Fields::Star(args_value.clone())));

            let subst = Error(false, Parameter::At, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env), Ok(Fields::At(args_value.clone())));
            let subst = Error(false, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(Fields::At(args_value.clone())));
            let subst = Error(false, Parameter::Star, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env), Ok(Fields::Star(args_value.clone())));
            let subst = Error(false, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(Fields::Star(args_value.clone())));
        }

        // Args all null
        {
            let mut env = Env::with_config(None, Some(vec!(
                String::from(""),
                String::from(""),
                String::from(""),
            )), None, None).unwrap();

            env.set_last_status(EXIT_SUCCESS);
            let subst = Error(true, Parameter::At, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env).as_ref(), Err(&err_at));
            assert_eq!(env.last_status(), EXIT_ERROR);

            env.set_last_status(EXIT_SUCCESS);
            let eval = Error(true, Parameter::At, None).eval(&mut env);
            if let Err(RuntimeError::Expansion(ExpansionError::EmptyParameter(Parameter::At, _))) = eval {
                assert_eq!(env.last_status(), EXIT_ERROR);
            } else {
                panic!("Unexpected evaluation: {:?}", eval);
            }

            env.set_last_status(EXIT_SUCCESS);
            let subst = Error(true, Parameter::Star, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env).as_ref(), Err(&err_star));
            assert_eq!(env.last_status(), EXIT_ERROR);

            env.set_last_status(EXIT_SUCCESS);
            let eval = Error(true, Parameter::Star, None).eval(&mut env);
            if let Err(RuntimeError::Expansion(ExpansionError::EmptyParameter(Parameter::Star, _))) = eval {
                assert_eq!(env.last_status(), EXIT_ERROR);
            } else {
                panic!("Unexpected evaluation: {:?}", eval);
            }


            let subst = Error(false, Parameter::At, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Error(false, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Error(false, Parameter::Star, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Error(false, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        }

        // Args not set
        {
            let mut env = Env::new().unwrap();

            env.set_last_status(EXIT_SUCCESS);
            let subst = Error(true, Parameter::At, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env).as_ref(), Err(&err_at));
            assert_eq!(env.last_status(), EXIT_ERROR);

            env.set_last_status(EXIT_SUCCESS);
            let eval = Error(true, Parameter::At, None).eval(&mut env);
            if let Err(RuntimeError::Expansion(ExpansionError::EmptyParameter(Parameter::At, _))) = eval {
                assert_eq!(env.last_status(), EXIT_ERROR);
            } else {
                panic!("Unexpected evaluation: {:?}", eval);
            }

            env.set_last_status(EXIT_SUCCESS);
            let subst = Error(true, Parameter::Star, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env).as_ref(), Err(&err_star));
            assert_eq!(env.last_status(), EXIT_ERROR);

            env.set_last_status(EXIT_SUCCESS);
            let eval = Error(true, Parameter::Star, None).eval(&mut env);
            if let Err(RuntimeError::Expansion(ExpansionError::EmptyParameter(Parameter::Star, _))) = eval {
                assert_eq!(env.last_status(), EXIT_ERROR);
            } else {
                panic!("Unexpected evaluation: {:?}", eval);
            }

            let subst = Error(false, Parameter::At, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Error(false, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Error(false, Parameter::Star, Some(err_msg.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Error(false, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        }
    }

    #[test]
    fn test_eval_parameter_substitution_alternative() {
        use syntax::ast::ParameterSubstitution::Alternative;

        let var       = String::from("non_empty_var");
        let var_value = String::from("foobar");
        let var_null  = String::from("var with empty value");
        let null      = String::new();
        let var_unset = String::from("var_not_set_in_env");

        let alt_value = String::from("some alternative value");
        let alternative = Word::Literal(alt_value.clone());

        let mut env = Env::new().unwrap();
        env.set_var(var.clone(),      Rc::new(var_value.clone()));
        env.set_var(var_null.clone(), Rc::new(null.clone()));

        let alt_value = Fields::Single(Rc::new(alt_value));
        let null      = Fields::Single(Rc::new(null));

        // Strict with alternative
        let subst = Alternative(true, Parameter::Var(var.clone()), Some(alternative.clone()));
        assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
        let subst = Alternative(true, Parameter::Var(var_null.clone()), Some(alternative.clone()));
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        let subst = Alternative(true, Parameter::Var(var_unset.clone()), Some(alternative.clone()));
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));

        // Strict without alternative
        let subst = Alternative(true, Parameter::Var(var.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        let subst = Alternative(true, Parameter::Var(var_null.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        let subst = Alternative(true, Parameter::Var(var_unset.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));


        // Non-strict with alternative
        let subst = Alternative(false, Parameter::Var(var.clone()), Some(alternative.clone()));
        assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
        let subst = Alternative(false, Parameter::Var(var_null.clone()), Some(alternative.clone()));
        assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
        let subst = Alternative(false, Parameter::Var(var_unset.clone()), Some(alternative.clone()));
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));

        // Non-strict without alternative
        let subst = Alternative(false, Parameter::Var(var.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        let subst = Alternative(false, Parameter::Var(var_null.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        let subst = Alternative(false, Parameter::Var(var_unset.clone()), None);
        assert_eq!(subst.eval(&mut env), Ok(null.clone()));


        // Args have one non-null argument
        {
            let args = vec!(
                String::from(""),
                String::from("foo"),
                String::from(""),
                String::from(""),
            );

            let mut env = Env::with_config(None, Some(args), None, None).unwrap();

            let subst = Alternative(true, Parameter::At, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
            let subst = Alternative(true, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Alternative(true, Parameter::Star, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
            let subst = Alternative(true, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));

            let subst = Alternative(false, Parameter::At, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
            let subst = Alternative(false, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Alternative(false, Parameter::Star, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
            let subst = Alternative(false, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        }

        // Args all null
        {
            let mut env = Env::with_config(None, Some(vec!(
                String::from(""),
                String::from(""),
                String::from(""),
            )), None, None).unwrap();

            let subst = Alternative(true, Parameter::At, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Alternative(true, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Alternative(true, Parameter::Star, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Alternative(true, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));

            let subst = Alternative(false, Parameter::At, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
            let subst = Alternative(false, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Alternative(false, Parameter::Star, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
            let subst = Alternative(false, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        }

        // Args not set
        {
            let mut env = Env::new().unwrap();

            let subst = Alternative(true, Parameter::At, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Alternative(true, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Alternative(true, Parameter::Star, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Alternative(true, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));

            let subst = Alternative(false, Parameter::At, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
            let subst = Alternative(false, Parameter::At, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
            let subst = Alternative(false, Parameter::Star, Some(alternative.clone()));
            assert_eq!(subst.eval(&mut env), Ok(alt_value.clone()));
            let subst = Alternative(false, Parameter::Star, None);
            assert_eq!(subst.eval(&mut env), Ok(null.clone()));
        }
    }

    #[test]
    fn test_eval_word_literal_evals_to_self() {
        let value = String::from("foobar");
        let mut env = Env::new().unwrap();
        assert_eq!(Word::Literal(value.clone()).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_eval_word_colon_evals_to_self() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::Colon.eval(&mut env), Ok(Fields::Single(Rc::new(String::from(":")))));
    }

    #[test]
    fn test_eval_word_lone_tilde_expansion() {
        let home_value = Rc::new(String::from("foobar"));
        let mut env = Env::new().unwrap();
        env.set_var(String::from("HOME"), home_value.clone());
        assert_eq!(Word::Tilde.eval(&mut env), Ok(Fields::Single(home_value)));
    }

    #[test]
    fn test_eval_word_tilde_in_middle_of_word_does_not_expand() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::Concat(vec!(
            Word::Literal(String::from("foo")),
            Word::Literal(String::from("~")),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foo~bar")))));
    }

    #[test]
    fn test_eval_word_tilde_in_middle_of_word_after_colon_does_not_expand() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::Concat(vec!(
            Word::Literal(String::from("foo")),
            Word::Colon,
            Word::Literal(String::from("~")),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foo:~bar")))));
    }

    #[test]
    fn test_eval_word_double_quoted_does_parameter_expansions_as_single_field() {
        let var = String::from("var");
        let mut env = Env::new().unwrap();
        env.set_var(var.clone(), Rc::new(String::from("hello world")));
        assert_eq!(Word::DoubleQuoted(vec!(
            Word::Literal(String::from("foo")),
            Word::Param(Parameter::Var(var)),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foohello worldbar")))));
    }


    #[test]
    fn test_eval_word_double_quoted_within_double_quoted_same_as_if_inner_was_not_there() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Word::DoubleQuoted(vec!(Word::Literal(String::from("foo")))),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foobar")))));
    }

    #[test]
    fn test_eval_word_double_quoted_does_not_expand_tilde() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Word::Tilde,
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("~")))));
    }

    #[test]
    fn test_eval_word_double_quoted_param_at_unset_results_in_no_fields() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Word::Param(Parameter::At),
        )).eval(&mut env), Ok(Fields::Zero))
    }

    #[test]
    fn test_eval_word_double_quoted_param_star_unset_results_in_no_fields() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Word::Param(Parameter::Star),
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
            Word::Param(Parameter::At),
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
            Word::Literal(String::from("foo")),
            Word::Param(Parameter::At),
            Word::Literal(String::from("bar")),
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
            Word::Literal(String::from("foo")),
            Word::Param(Parameter::At),
            Word::Literal(String::from("bar")),
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
            Word::Literal(String::from("foo")),
            Word::Param(Parameter::Star),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("fooone two threebar")))));

        env.set_var(String::from("IFS"), Rc::new(String::from("!")));
        assert_eq!(Word::DoubleQuoted(vec!(
            Word::Literal(String::from("foo")),
            Word::Param(Parameter::Star),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("fooone!two!threebar")))));

        env.set_var(String::from("IFS"), Rc::new(String::new()));
        assert_eq!(Word::DoubleQuoted(vec!(
            Word::Literal(String::from("foo")),
            Word::Param(Parameter::Star),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("fooonetwothreebar")))));
    }

    #[test]
    fn test_eval_word_concat_joins_all_inner_words() {
        let mut env = Env::new().unwrap();
        env.set_var(String::from("var"), Rc::new(String::from("foobar")));

        assert_eq!(Word::Concat(vec!(
            Word::Literal(String::from("hello")),
            Word::Param(Parameter::Var(String::from("var"))),
            Word::Literal(String::from("world")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("hellofoobarworld")))));
    }

    #[test]
    fn test_eval_word_concat_if_inner_word_expands_to_many_fields_they_are_joined_with_those_before_and_after()
    {
        let mut env = Env::new().unwrap();
        env.set_var(String::from("var"), Rc::new(String::from("foo bar baz")));

        assert_eq!(Word::Concat(vec!(
            Word::Literal(String::from("hello")),
            Word::Param(Parameter::Var(String::from("var"))),
            Word::Literal(String::from("world")),
        )).eval(&mut env), Ok(Fields::Many(vec!(
            Rc::new(String::from("hellofoo")),
            Rc::new(String::from("bar")),
            Rc::new(String::from("bazworld")),
        ))));
    }

    #[test]
    fn test_eval_word_concat_should_not_expand_tilde_which_is_not_at_start() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::Concat(vec!(
            Word::Literal(String::from("foo")),
            Word::Tilde,
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foo~bar")))));
        assert_eq!(Word::Concat(vec!(
            Word::Literal(String::from("foo")),
            Word::Tilde,
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foo~")))));
    }

    #[test]
    fn test_eval_word_concat_param_at_expands_when_args_set() {
        let mut env = Env::with_config(None, Some(vec!(
            String::from("one"),
            String::from("two"),
            String::from("three"),
        )), None, None).unwrap();

        assert_eq!(Word::Concat(vec!(
            Word::Param(Parameter::At),
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

        assert_eq!(Word::Concat(vec!(
            Word::Literal(String::from("foo")),
            Word::Param(Parameter::At),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Many(vec!(
            Rc::new(String::from("fooone")),
            Rc::new(String::from("two")),
            Rc::new(String::from("threebar")),
        ))));
    }

    #[test]
    fn test_eval_word_concat_param_at_expands_to_nothing_when_args_not_set_and_concats_with_rest() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::Concat(vec!(
            Word::Literal(String::from("foo")),
            Word::Param(Parameter::At),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foobar")))));
    }

    #[test]
    fn test_eval_word_concat_within_double_quoted_same_as_if_inner_was_not_there() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Word::Concat(vec!(Word::Literal(String::from("foo baz\nqux")))),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foo baz\nquxbar")))));
    }

    #[test]
    fn test_eval_word_double_quoted_within_concat_within_double_quoted_same_as_if_inner_was_not_there() {
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Word::DoubleQuoted(vec!(
                Word::Concat(vec!(Word::DoubleQuoted(vec!(Word::Literal(String::from("foo baz\nqux"))))))
            )),
            Word::Literal(String::from("bar")),
        )).eval(&mut env), Ok(Fields::Single(Rc::new(String::from("foo baz\nquxbar")))));
    }

    #[test]
    fn test_eval_word_single_quoted_removes_quotes() {
        let value = String::from("hello world");
        let mut env = Env::new().unwrap();
        assert_eq!(Word::SingleQuoted(value.clone()).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_eval_word_double_quoted_removes_quotes() {
        let value = String::from("hello world");
        let mut env = Env::new().unwrap();
        assert_eq!(Word::DoubleQuoted(vec!(
            Word::Literal(value.clone())
        )).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_eval_word_escaped_quoted_removes_slash() {
        let value = String::from("&");
        let mut env = Env::new().unwrap();
        assert_eq!(Word::Escaped(value.clone()).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_eval_word_single_quoted_should_not_split_fields() {
        let value = String::from("hello world\nfoo\tbar");
        let mut env = Env::new().unwrap();
        assert_eq!(Word::SingleQuoted(value.clone()).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_eval_word_single_quoted_should_not_expand_anything() {
        let value = String::from("hello world\nfoo\tbar * baz ~");
        let mut env = Env::new().unwrap();
        assert_eq!(Word::SingleQuoted(value.clone()).eval(&mut env), Ok(Fields::Single(Rc::new(value))));
    }

    #[test]
    fn test_run_command_and() {
        let mut env = Env::new().unwrap();
        assert_eq!(Command::And(true_cmd(), true_cmd()).run(&mut env), Ok(ExitStatus::Code(0)));
        assert_eq!(Command::And(true_cmd(), exit(5)).run(&mut env), Ok(ExitStatus::Code(5)));
        assert_eq!(Command::And(false_cmd(), exit(5)).run(&mut env), Ok(ExitStatus::Code(1)));
    }

    #[test]
    fn test_run_command_and_error_handling() {
        let mut env = Env::new().unwrap();

        // CommandError::NotFound
        assert_eq!(Command::And(cmd!("missing"), true_cmd()).run(&mut env), Ok(EXIT_CMD_NOT_FOUND));

        // CommandError::NotExecutable: there isn't a good/consistent test to invoke this error

        // RuntimeError::Io
        assert_eq!(Command::And(
                cmd!("cat", Word::Literal(String::from("missing file"))), true_cmd()).run(&mut env),
                Ok(EXIT_ERROR));

        // RuntimeError::Unimplemented
        assert_eq!(Command::And(Box::new(Command::Job(cmd!("echo"))), true_cmd()).run(&mut env),
            Ok(EXIT_ERROR));

        let cmd = cmd!("echo", Word::Subst(Box::new(ParameterSubstitution::Arithmetic(Some(
            Arith::Div(Box::new(Arith::Literal(1)), Box::new(Arith::Literal(0)))
        )))));
        assert_eq!(Command::And(cmd, true_cmd()).run(&mut env),
            Err(RuntimeError::Expansion(ExpansionError::DivideByZero)));

        let cmd = cmd!("echo", Word::Subst(Box::new(ParameterSubstitution::Arithmetic(Some(
            Arith::Pow(Box::new(Arith::Literal(1)), Box::new(Arith::Literal(-5)))
        )))));
        assert_eq!(Command::And(cmd, true_cmd()).run(&mut env),
            Err(RuntimeError::Expansion(ExpansionError::NegativeExponent)));

        let cmd = cmd!("echo", Word::Subst(Box::new(
                    ParameterSubstitution::Assign(true, Parameter::At, Some(Word::Literal(String::from("foo")))))));
        assert_eq!(Command::And(cmd, true_cmd()).run(&mut env),
            Err(RuntimeError::Expansion(ExpansionError::BadAssig(Parameter::At))));

        let var = Parameter::Var(String::from("var"));
        let msg = String::from("empty");
        let cmd = cmd!("echo", Word::Subst(Box::new(
                    ParameterSubstitution::Error(true, var.clone(), Some(Word::Literal(msg.clone()))))));
        assert_eq!(Command::And(cmd, true_cmd()).run(&mut env),
            Err(RuntimeError::Expansion(ExpansionError::EmptyParameter(var, Rc::new(msg)))));
    }

    #[test]
    fn test_run_command_or() {
        let mut env = Env::new().unwrap();
        assert_eq!(Command::Or(true_cmd(), exit(5)).run(&mut env), Ok(ExitStatus::Code(0)));
        assert_eq!(Command::Or(false_cmd(), exit(5)).run(&mut env), Ok(ExitStatus::Code(5)));
    }

    #[test]
    fn test_run_command_or_error_handling() {
        let mut env = Env::new().unwrap();

        // CommandError::NotFound
        assert_eq!(Command::Or(cmd!("missing"), true_cmd()).run(&mut env), Ok(EXIT_SUCCESS));

        // CommandError::NotExecutable: there isn't a good/consistent test to invoke this error

        // RuntimeError::Io
        assert_eq!(Command::Or(
                cmd!("cat", Word::Literal(String::from("missing file"))), true_cmd()).run(&mut env),
                Ok(EXIT_SUCCESS));

        // RuntimeError::Unimplemented
        assert_eq!(Command::Or(Box::new(Command::Job(cmd!("echo"))), true_cmd()).run(&mut env),
            Ok(EXIT_SUCCESS));

        let cmd = cmd!("echo", Word::Subst(Box::new(ParameterSubstitution::Arithmetic(Some(
            Arith::Div(Box::new(Arith::Literal(1)), Box::new(Arith::Literal(0)))
        )))));
        assert_eq!(Command::Or(cmd, true_cmd()).run(&mut env),
            Err(RuntimeError::Expansion(ExpansionError::DivideByZero)));

        let cmd = cmd!("echo", Word::Subst(Box::new(ParameterSubstitution::Arithmetic(Some(
            Arith::Pow(Box::new(Arith::Literal(1)), Box::new(Arith::Literal(-5)))
        )))));
        assert_eq!(Command::Or(cmd, true_cmd()).run(&mut env),
            Err(RuntimeError::Expansion(ExpansionError::NegativeExponent)));

        let cmd = cmd!("echo", Word::Subst(Box::new(
                    ParameterSubstitution::Assign(true, Parameter::At, Some(Word::Literal(String::from("foo")))))));
        assert_eq!(Command::Or(cmd, true_cmd()).run(&mut env),
            Err(RuntimeError::Expansion(ExpansionError::BadAssig(Parameter::At))));

        let var = Parameter::Var(String::from("var"));
        let msg = String::from("empty");
        let cmd = cmd!("echo", Word::Subst(Box::new(
                    ParameterSubstitution::Error(true, var.clone(), Some(Word::Literal(msg.clone()))))));
        assert_eq!(Command::Or(cmd, true_cmd()).run(&mut env),
            Err(RuntimeError::Expansion(ExpansionError::EmptyParameter(var, Rc::new(msg)))));
    }

    #[test]
    fn test_run_command_function_declaration() {
        let fn_name = "function_name";
        let mut env = Env::new().unwrap();
        let func = Command::Function(fn_name.to_string(), Rc::new(*false_cmd()));
        assert_eq!(func.run(&mut env), Ok(EXIT_SUCCESS));
        assert_eq!(cmd!(fn_name).run(&mut env), Ok(ExitStatus::Code(1)));
    }

    #[test]
    fn test_run_command_function_can_be_recursive() {
        let fn_name = "function_name";
        let var = "var";
        let value = "value";
        let double_value = format!("{}{}", value, value);

        let mut env = Env::new().unwrap();
        let func = Command::Function(fn_name.to_string(), Rc::new(Command::Compound(
            Box::new(CompoundCommand::Brace(vec!(
                Command::Simple(Box::new(SimpleCommand {
                    cmd: None,
                    vars: vec!((var.to_string(), Some(Word::Concat(vec!(
                        Word::Literal(value.to_string()),
                        Word::Param(Parameter::Var(var.to_string())),
                    ))))),
                    io: vec!(),
                })),
                Command::Compound(Box::new(CompoundCommand::If(vec!(
                    (vec!(cmd_unboxed!("[",
                      Word::Param(Parameter::Var(var.to_string())),
                      Word::Literal(String::from("!=")),
                      Word::Literal(double_value.clone()),
                      Word::Literal(String::from("]")),
                    )), vec!(cmd_unboxed!(fn_name))),
                ), None)), vec!()),
            ))),
            vec!()
        )));

        assert_eq!(func.run(&mut env), Ok(EXIT_SUCCESS));
        assert_eq!(cmd!(fn_name).run(&mut env), Ok(EXIT_SUCCESS));
        assert_eq!(env.var(var), Some(&Rc::new(double_value)));
    }

    #[test]
    fn test_eval_compound_local_redirections_applied_correctly_with_no_prev_redirections() {
        // Make sure the environment has NO open file descriptors
        let mut env = Env::with_config(None, None, None, Some(vec!())).unwrap();
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push(String::from("out"));

        let cmd = Command::Compound(
            Box::new(CompoundCommand::Brace(vec!(
                Command::Simple(Box::new(SimpleCommand {
                    cmd: Some((Word::Literal(String::from("echo")), vec!(Word::Literal(String::from("out"))))),
                    io: vec!(),
                    vars: vec!(),
                })),
                Command::Simple(Box::new(SimpleCommand {
                    cmd: Some((Word::Literal(String::from("echo")), vec!(Word::Literal(String::from("err"))))),
                    io: vec!(Redirect::DupWrite(Some(1), Word::Literal(String::from("2")))),
                    vars: vec!(),
                })),
            ))),
            vec!(
                Redirect::Write(Some(2), Word::Literal(file_path.display().to_string())),
                Redirect::DupWrite(Some(1), Word::Literal(String::from("2"))),
            )
        );

        assert_eq!(cmd.run(&mut env), Ok(EXIT_SUCCESS));
        assert!(env.file_desc(1).is_none());
        assert!(env.file_desc(2).is_none());

        let mut read = String::new();
        Permissions::Read.open(&file_path).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "out\nerr\n");
    }

    #[test]
    fn test_eval_compound_local_redirections_applied_correctly_with_prev_redirections() {
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push(String::from("out"));

        let mut file_path_out = PathBuf::new();
        file_path_out.push(tempdir.path());
        file_path_out.push(String::from("out_prev"));

        let mut file_path_err = PathBuf::new();
        file_path_err.push(tempdir.path());
        file_path_err.push(String::from("err_prev"));

        let file_out = Permissions::Write.open(&file_path_out).unwrap();
        let file_err = Permissions::Write.open(&file_path_err).unwrap();

        let mut env = Env::with_config(None, None, None, Some(vec!(
            (STDOUT_FILENO, Rc::new(FileDesc::from(file_out)), Permissions::Write),
            (STDERR_FILENO, Rc::new(FileDesc::from(file_err)), Permissions::Write),
        ))).unwrap();

        let (cmd_body, cmd_redirects) = (
            Box::new(CompoundCommand::Brace(vec!(
                Command::Simple(Box::new(SimpleCommand {
                    cmd: Some((Word::Literal(String::from("echo")), vec!(Word::Literal(String::from("out"))))),
                    io: vec!(),
                    vars: vec!(),
                })),
                Command::Simple(Box::new(SimpleCommand {
                    cmd: Some((Word::Literal(String::from("echo")), vec!(Word::Literal(String::from("err"))))),
                    io: vec!(Redirect::DupWrite(Some(1), Word::Literal(String::from("2")))),
                    vars: vec!(),
                })),
            ))),
            vec!(
                Redirect::Write(Some(2), Word::Literal(file_path.display().to_string())),
                Redirect::DupWrite(Some(1), Word::Literal(String::from("2"))),
            )
        );

        // Check that local override worked
        assert_eq!(Command::Compound(cmd_body.clone(), cmd_redirects).run(&mut env), Ok(EXIT_SUCCESS));
        let mut read = String::new();
        Permissions::Read.open(&file_path).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "out\nerr\n");

        // Check that defaults remained the same
        assert_eq!(Command::Compound(cmd_body, vec!()).run(&mut env), Ok(EXIT_SUCCESS));

        read.clear();
        Permissions::Read.open(&file_path_out).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "out\n");

        read.clear();
        Permissions::Read.open(&file_path_err).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "err\n");
    }

    #[test]
    fn test_eval_compound_multiple_local_redirections_last_wins_and_prev_fd_properly_restored() {
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push(String::from("out"));

        let mut file_path_empty = PathBuf::new();
        file_path_empty.push(tempdir.path());
        file_path_empty.push(String::from("out_empty"));

        let mut file_path_default = PathBuf::new();
        file_path_default.push(tempdir.path());
        file_path_default.push(String::from("default"));

        let file_default = Permissions::Write.open(&file_path_default).unwrap();

        let mut env = Env::with_config(None, None, None, Some(vec!(
            (STDOUT_FILENO, Rc::new(FileDesc::from(file_default)), Permissions::Write),
        ))).unwrap();

        let cmd = Command::Compound(
            Box::new(CompoundCommand::Brace(vec!(
                Command::Simple(Box::new(SimpleCommand {
                    cmd: Some((Word::Literal(String::from("echo")), vec!(Word::Literal(String::from("out"))))),
                    io: vec!(),
                    vars: vec!(),
                })),
            ))),
            vec!(
                Redirect::Write(Some(1), Word::Literal(file_path_empty.display().to_string())),
                Redirect::Write(Some(1), Word::Literal(file_path.display().to_string())),
            )
        );

        let cmd2 = Command::Simple(Box::new(SimpleCommand {
            cmd: Some((Word::Literal(String::from("echo")), vec!(Word::Literal(String::from("default"))))),
            io: vec!(),
            vars: vec!(),
        }));

        assert_eq!(cmd.run(&mut env), Ok(EXIT_SUCCESS));
        assert_eq!(cmd2.run(&mut env), Ok(EXIT_SUCCESS));

        let mut read = String::new();
        Permissions::Read.open(&file_path).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "out\n");

        read.clear();
        Permissions::Read.open(&file_path_empty).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "");

        read.clear();
        Permissions::Read.open(&file_path_default).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "default\n");
    }

    #[test]
    fn test_eval_compound_local_redirections_closed_after_command_exits_but_side_effects_remain() {
        let var = "var";
        let value = "foobar";
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push(String::from("out"));

        let mut env = Env::new().unwrap();

        let cmd = Command::Compound(
            Box::new(CompoundCommand::Brace(vec!(*true_cmd()))),
            vec!(
                Redirect::Write(Some(3), Word::Literal(file_path.display().to_string())),
                Redirect::Write(Some(4), Word::Literal(file_path.display().to_string())),
                Redirect::Write(Some(5), Word::Subst(Box::new(ParameterSubstitution::Assign(
                    true,
                    Parameter::Var(String::from(var)),
                    Some(Word::Literal(String::from(value))),
                )))),
            )
        );

        assert_eq!(cmd.run(&mut env), Ok(EXIT_SUCCESS));
        assert!(env.file_desc(3).is_none());
        assert!(env.file_desc(4).is_none());
        assert!(env.file_desc(5).is_none());
        assert_eq!(**env.var(var).unwrap(), value);
    }
}
