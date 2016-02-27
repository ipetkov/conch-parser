//! This module defines a runtime envirnment capable of executing parsed shell commands.

use glob;
use libc;

use std::borrow::Cow;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::convert::{From, Into};
use std::fmt;
use std::io::{Error as IoError, ErrorKind as IoErrorKind, Result as IoResult, Write};
use std::iter::{IntoIterator, Iterator};
use std::process::{self, Stdio};
use std::rc::Rc;
use std::result;

use syntax::ast::{Command, CompoundCommand, SimpleCommand, Redirect};
use runtime::eval::{Fields, TildeExpansion, WordEval, WordEvalConfig};
use runtime::io::dup_stdio;
use runtime::io::{FileDesc, Permissions};
use void::Void;

mod errors;

pub mod eval;
pub mod io;
pub use self::errors::*;

/// Exit code for commands that exited successfully.
pub const EXIT_SUCCESS:            ExitStatus = ExitStatus::Code(0);
/// Exit code for commands that did not exit successfully.
pub const EXIT_ERROR:              ExitStatus = ExitStatus::Code(1);
/// Exit code for commands which are not executable.
pub const EXIT_CMD_NOT_EXECUTABLE: ExitStatus = ExitStatus::Code(126);
/// Exit code for missing commands.
pub const EXIT_CMD_NOT_FOUND:      ExitStatus = ExitStatus::Code(127);

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
    /// Get the name of the shell or the current function that is executing.
    fn name(&self) -> &Rc<String>;
    /// Get the value of some variable. The values of both shell-only
    /// and environment variables will be looked up and returned.
    fn var(&self, name: &str) -> Option<&Rc<String>>;
    /// Set the value of some variable (including environment variables).
    fn set_var(&mut self, name: String, val: Rc<String>);
    /// Unset the value of some variable (including environment variables).
    fn unset_var(&mut self, name: String);
    /// Indicates if a function is currently defined with a given name.
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
    /// refers to the shell's name. Thus the first real argument starts at index 1.
    fn arg(&self, idx: usize) -> Option<&Rc<String>>;
    /// Get the number of current arguments, NOT including the shell name.
    fn args_len(&self) -> usize;
    /// Get all current arguments as a vector.
    fn args(&self) -> Cow<[Rc<String>]>;
    /// Get all current pairs of environment variables and their values.
    fn env(&self) -> Cow<[(&str, &str)]>;
    /// Get the permissions and OS handle associated with an opened file descriptor.
    fn file_desc(&self, fd: Fd) -> Option<(&Rc<FileDesc>, Permissions)>;
    /// Associate a file descriptor with a given OS handle and permissions.
    fn set_file_desc(&mut self, fd: Fd, fdes: Rc<FileDesc>, perms: Permissions);
    /// Treat the specified file descriptor as closed for the current environment.
    fn close_file_desc(&mut self, fd: Fd);
    /// Indicates if running in interactive mode.
    fn is_interactive(&self) -> bool;
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
            fd.unsafe_write().write_all(&format!("{}: {}\n", self.name(), err).into_bytes())
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

    fn unset_var(&mut self, name: String) {
        self.vars.insert(name, None);
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

    fn env(&self) -> Cow<[(&str, &str)]> {
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

        let ret: Vec<_> = env.into_iter().filter_map(|(k, v)| match v {
            &Some((ref v, true)) => Some((k, &***v)),
            &Some((_, false)) => None,
            &None => None,
        }).collect();
        Cow::Owned(ret)
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

    fn is_interactive(&self) -> bool {
        false
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

impl<W: WordEval> Run for SimpleCommand<W> {
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
        for &(var, val) in &*env.env() {
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
                    f@Fields::Split(_) => cmd.env(var, &*f.join()),
                };
            }
        }

        let get_redirect = |handle: Option<Rc<FileDesc>>, fd_debug| -> Result<Stdio> {
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

impl<W: WordEval + 'static> Run for Command<W> {
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

            Command::Pipe(bool, ref cmds) => unimplemented!(), // FIXME

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

impl<W: WordEval, C: Run> Run for CompoundCommand<W, C> {
    fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
        use syntax::ast::CompoundCommand::*;

        let exit = match *self {
            // Brace commands are just command groupings no different than as if we had
            // sequential commands. Thus, any error that results should be passed up
            // for the caller to decide how to handle.
            Brace(ref cmds) => try!(run(cmds, env)),

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
                while try_and_swallow_non_fatal!(run(guard, env), env).success() ^ invert_guard_status {
                    exit = try_and_swallow_non_fatal!(run(body, env), env);
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
                    if try_and_swallow_non_fatal!(run(guard, env), env).success() {
                        exit = Some(try!(run(body, env)));
                        break;
                    }
                }

                let exit = match exit {
                    Some(e) => e,
                    None => try!(els.as_ref().map_or(Ok(EXIT_SUCCESS), |els| run(els, env))),
                };
                env.set_last_status(exit);
                exit
            },

            // Subshells should swallow (but report) errors since they are considered a separate shell.
            // Thus, errors that occur within here should NOT be propagated upward.
            Subshell(ref body) => {
                let env = &mut *env.sub_env();
                match run(body, env) {
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
                    exit = try_and_swallow_non_fatal!(run(body, env), env);
                }
                exit
            },

            Case(ref word, ref arms) => {
                let match_opts = glob::MatchOptions {
                    case_sensitive: true,
                    require_literal_separator: false,
                    require_literal_leading_dot: false,
                };

                let word = try!(word.eval_with_config(env, WordEvalConfig {
                    tilde_expansion: TildeExpansion::First,
                    split_fields_further: false,
                })).join();

                // If no arm was taken we still consider the command a success
                let mut exit = EXIT_SUCCESS;
                'case: for &(ref pats, ref body) in arms.iter() {
                    for pat in pats {
                        if try!(pat.eval_as_pattern(env)).matches_with(&word, &match_opts) {
                            exit = try!(run(body, env));
                            break 'case;
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

/// A function for running any iterable collection of items which implement `Run`.
/// This is useful for lazily streaming commands to run.
pub fn run<I>(iter: I, env: &mut Environment) -> Result<ExitStatus>
    where I: IntoIterator, I::Item: Run
{
    let mut exit = EXIT_SUCCESS;
    for c in iter {
        exit = try_and_swallow_non_fatal!(c.run(env), env)
    }
    env.set_last_status(exit);
    Ok(exit)
}

/// Adds a number of local redirects to the specified environment, runs the provided closure,
/// then removes the local redirects and restores the previous file descriptors before returning.
pub fn run_with_local_redirections<'a, I, F, W, T>(env: &mut Environment, redirects: I, closure: F)
    -> Result<T>
    where I: IntoIterator<Item = &'a Redirect<W>>,
          F: FnOnce(&mut Environment) -> Result<T>,
          W: 'a + WordEval,
{
    struct RedirectionOverride {
        /// The local FileDesc that should be temporarily placed in/removed from the environment.
        override_fdes: Option<Rc<FileDesc>>,
        /// The previous FileDesc and permissions in the environment, which was overriden.
        previous_fdes: Option<(Rc<FileDesc>, Permissions)>,
    }

    // We'll swap the descriptors here temporarily
    // and hope the environment implementation doesn't mind
    // our shenanigans before we return them.
    let redirects = redirects.into_iter();
    let mut overrides: HashMap<Fd, RedirectionOverride> = HashMap::with_capacity(redirects.size_hint().0);

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
                let new_fdes = fdes_and_perms.as_ref().map(|&(ref fdes, _)| fdes.clone());

                // Only backup any descriptor which has NOT already been LOCALLY
                // overriden, e.g. if `2>err` was already in the environment, but
                // `2>foo 2>bar` are specified as local overrides, only `2>err`
                // should be backed up.
                match overrides.entry(fd) {
                    Entry::Occupied(mut entry) => entry.get_mut().override_fdes = new_fdes,
                    Entry::Vacant(entry) => {
                        entry.insert(RedirectionOverride {
                            override_fdes: new_fdes,
                            previous_fdes: env.file_desc(fd).map(|(fdes, perms)| (fdes.clone(), perms)),
                        });
                    }
                }

                env.close_file_desc(fd);
                fdes_and_perms.map(|(fdes, perms)| env.set_file_desc(fd, fdes, perms));
            },
        }
    }

    let ret = match io_err {
        Some(err) => Err(err),
        None => closure(env),
    };

    // We must only reset descriptors which we know were locally overridden, because
    // it is possible that a descriptor was changed via `exec`, which change we need
    // to keep (e.g. `{ exec 2>new_file; } 2>temp; echo foo 1>&2` should write foo to new_file).
    for (fd, override_) in overrides {
        if env.file_desc(fd).map(|(fdes, _)| fdes) == override_.override_fdes.as_ref() {
            match override_.previous_fdes {
                Some((fdes, perms)) => env.set_file_desc(fd, fdes, perms),
                None => env.close_file_desc(fd),
            }
        }
    }

    ret
}

#[cfg(test)]
mod tests {
    extern crate tempdir;

    use glob;

    use self::tempdir::TempDir;
    use std::cell::RefCell;
    use std::fs::OpenOptions;
    use std::io::{Read, Write, Error as IoError};
    use std::path::PathBuf;
    use std::rc::Rc;
    use std::thread;
    use super::eval::{Fields, WordEval, WordEvalConfig};
    use super::io::{FileDesc, Permissions};
    use super::*;

    use syntax::ast::Command::*;
    use syntax::ast::CompoundCommand::*;
    use syntax::ast::{Redirect, SimpleCommand, Parameter};

    type Command<'a>         = ::syntax::ast::Command<MockWord<'a>>;
    type CompoundCommand<'a> = ::syntax::ast::CompoundCommand<MockWord<'a>, Command<'a>>;

    const EXIT_ERROR_MOCK: ExitStatus = ExitStatus::Code(::std::i32::MAX);

    #[cfg(unix)]
    const DEV_NULL: &'static str = "/dev/null";

    #[cfg(windows)]
    const DEV_NULL: &'static str = "NUL";

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

    #[derive(Clone)]
    enum MockWord<'a> {
        Regular(Rc<String>),
        Error(Rc<Fn() -> RuntimeError + 'a>),
    }

    impl<'a> WordEval for MockWord<'a> {
        fn eval_with_config(&self, env: &mut Environment, _: WordEvalConfig) -> Result<Fields> {
            match *self {
                MockWord::Regular(ref rc) => Ok(rc.clone().into()),
                MockWord::Error(ref e) => {
                    env.set_last_status(EXIT_ERROR_MOCK);
                    Err(e())
                },
            }
        }

        fn eval_as_pattern(&self, env: &mut Environment) -> Result<glob::Pattern> {
            match *self {
                MockWord::Regular(ref rc) => Ok(glob::Pattern::new(rc).unwrap()),
                MockWord::Error(ref e) => {
                    env.set_last_status(EXIT_ERROR_MOCK);
                    Err(e())
                },
            }
        }
    }

    impl<'a, 'b> From<&'b str> for MockWord<'a> {
        fn from(s: &'b str) -> Self {
            MockWord::Regular(Rc::new(s.into()))
        }
    }

    impl<'a> From<String> for MockWord<'a> {
        fn from(s: String) -> Self {
            MockWord::Regular(Rc::new(s))
        }
    }

    impl<'a, F: Fn() -> RuntimeError + 'a> From<F> for MockWord<'a> {
        fn from(f: F) -> Self {
            MockWord::Error(Rc::new(f))
        }
    }

    fn word<'a, T: ToString>(s: T) -> MockWord<'a> {
        MockWord::Regular(Rc::new(s.to_string()))
    }

    fn dev_null() -> FileDesc {
        OpenOptions::new().read(true).write(true).open(DEV_NULL).unwrap().into()
    }

    fn file_desc() -> FileDesc {
        dev_null()
    }

    macro_rules! cmd {
        ($cmd:expr)                  => { cmd!($cmd,) };
        ($cmd:expr, $($arg:expr),*,) => { cmd!($cmd, $($arg),*) };
        ($cmd:expr, $($arg:expr),* ) => {
            Box::new(Simple(Box::new(SimpleCommand {
                cmd: Some((MockWord::from($cmd), vec!($(MockWord::from($arg)),*))),
                vars: vec!(),
                io: vec!(),
            })))
        };
    }

    fn exit<'a>(status: i32) -> Box<Command<'a>> {
        cmd!("sh", "-c", format!("exit {}", status))
    }

    fn true_cmd<'a>() -> Box<Command<'a>> { exit(0) }
    fn false_cmd<'a>() -> Box<Command<'a>> { exit(1) }

    macro_rules! run_test {
        ($swallow_errors:expr, $test:expr, $env:expr, $ok_status:expr, $($case:expr),+,) => {
            $({
                // Use a sub-env for each test case to offer a "clean slate"
                let result = $test(cmd!(move || $case), &mut *$env.sub_env());
                if $swallow_errors {
                    assert_eq!(result, Ok($ok_status.clone().unwrap_or(EXIT_ERROR_MOCK)));
                } else {
                    assert_eq!(result, Err($case));
                }
            })+
        };
    }

    fn test_error_handling_non_fatals<'a, F>(swallow_errors: bool,
                                             test: F,
                                             ok_status: Option<ExitStatus>)
        where F: Fn(Box<Command<'a>>, &mut Environment) -> Result<ExitStatus>
    {
        // We'll be printing a lot of errors, so we'll suppress actually printing
        // to avoid polluting the output of the test runner.
        // NB: consider removing this line when debugging
        let mut env = Env::new().unwrap();
        env.set_file_desc(STDERR_FILENO, Rc::new(dev_null()), Permissions::Write);

        run_test!(swallow_errors, test, env, ok_status,
            RuntimeError::Command(CommandError::NotFound(Rc::new("".to_string()))),
            RuntimeError::Command(CommandError::NotExecutable(Rc::new("".to_string()))),
            RuntimeError::Redirection(RedirectionError::Ambiguous(vec!())),
            RuntimeError::Redirection(RedirectionError::BadFdSrc(Rc::new("".to_string()))),
            RuntimeError::Redirection(RedirectionError::BadFdPerms(0, Permissions::Read)),
            RuntimeError::Unimplemented("unimplemented"),
            RuntimeError::Io(IoError::last_os_error(), Rc::new("".to_string())),
        );
    }

    fn test_error_handling_fatals<'a, F>(swallow_fatals: bool,
                                         test: F,
                                         ok_status: Option<ExitStatus>)
        where F: Fn(Box<Command<'a>>, &mut Environment) -> Result<ExitStatus>
    {
        // We'll be printing a lot of errors, so we'll suppress actually printing
        // to avoid polluting the output of the test runner.
        // NB: consider removing this line when debugging
        let mut env = Env::new().unwrap();
        env.set_file_desc(STDERR_FILENO, Rc::new(dev_null()), Permissions::Write);

        // Fatal errors should not be swallowed
        run_test!(swallow_fatals, test, env, ok_status,
            RuntimeError::Expansion(ExpansionError::DivideByZero),
            RuntimeError::Expansion(ExpansionError::NegativeExponent),
            RuntimeError::Expansion(ExpansionError::BadAssig(Parameter::At)),
            RuntimeError::Expansion(ExpansionError::EmptyParameter(Parameter::At, Rc::new("".to_string()))),
        );
    }

    /// For exhaustively testing against handling of different error types
    fn test_error_handling<'a, F>(swallow_errors: bool, test: F, ok_status: Option<ExitStatus>)
        where F: Fn(Box<Command<'a>>, &mut Environment) -> Result<ExitStatus>
    {
        test_error_handling_non_fatals(swallow_errors, &test, ok_status);
        test_error_handling_fatals(false, test, ok_status);
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
    fn test_env_set_get_unset_var() {
        let name = "var".to_string();
        let value = "value";
        let mut env = Env::new().unwrap();
        assert_eq!(env.var(&name), None);
        env.set_var(name.clone(), Rc::new(value.to_string()));
        assert_eq!(&**env.var(&name).unwrap(), value);
        env.unset_var(name.clone());
        assert_eq!(env.var(&name), None);
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
        let fn_name_owned = "fn name".to_string();
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
        let fn_name = "fn name";
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push("out");

        let mut env = Env::new().unwrap();
        env.set_function(fn_name.to_string(), MockFn::new(|env| {
            let args = env.args().iter().map(|rc| rc.to_string()).collect::<Vec<_>>();
            let msg = args.join(" ");
            let fd = env.file_desc(STDOUT_FILENO).unwrap().0;
            unsafe { fd.unsafe_write().write_all(msg.as_bytes()).unwrap(); }
            Ok(EXIT_SUCCESS)
        }));

        let cmd = SimpleCommand {
            cmd: Some((word(fn_name), vec!(word("foo"), word("bar")))),
            vars: vec!(),
            io: vec!(Redirect::Write(None, word(file_path.display()))),
        };

        assert_eq!(cmd.run(&mut env), Ok(EXIT_SUCCESS));

        let mut read = String::new();
        Permissions::Read.open(&file_path).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "foo bar");
    }

    #[test]
    fn test_env_inherit_env_vars_if_not_overridden() {
        let env = Env::new().unwrap();

        let mut vars: Vec<(String, String)> = ::std::env::vars().collect();
        vars.sort();
        let vars: Vec<(&str, &str)> = vars.iter().map(|&(ref k, ref v)| (&**k, &**v)).collect();
        let mut env_vars: Vec<_> = (&*env.env()).into();
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
        let mut vars: Vec<_> = (&*env.env()).into();
        vars.sort();
        assert_eq!(vars, env_vars);
        let child = env.sub_env();
        let mut vars: Vec<_> = (&*child.env()).into();
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
            assert_eq!(**got_file_desc, *file_desc);
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
        assert_eq!(**got_file_desc, *file_desc);
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
            assert_eq!(**got_file_desc, *file_desc);
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
        assert_eq!(**got_file_desc, *file_desc);
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
    fn test_run_command_and() {
        let mut env = Env::new().unwrap();
        assert_eq!(And(true_cmd(), true_cmd()).run(&mut env), Ok(ExitStatus::Code(0)));
        assert_eq!(And(true_cmd(), exit(5)).run(&mut env), Ok(ExitStatus::Code(5)));
        assert_eq!(And(false_cmd(), exit(5)).run(&mut env), Ok(ExitStatus::Code(1)));
    }

    #[test]
    fn test_run_command_and_error_handling() {
        test_error_handling(true,  |cmd, env| {
            let should_not_run = "should not run";
            env.set_function(should_not_run.to_string(), MockFn::new(|_| {
                panic!("ran command that should not be run")
            }));

            And(cmd, cmd!(should_not_run)).run(env)
        }, None);
        test_error_handling(false, |cmd, env| And(true_cmd(), cmd).run(env), None);
    }

    #[test]
    fn test_run_command_or() {
        let mut env = Env::new().unwrap();
        let should_not_run = "should not run";
        env.set_function(should_not_run.to_string(), MockFn::new(|_| {
            panic!("ran command that should not be run")
        }));

        assert_eq!(Or(true_cmd(), cmd!(should_not_run)).run(&mut env), Ok(ExitStatus::Code(0)));
        assert_eq!(Or(false_cmd(), exit(5)).run(&mut env), Ok(ExitStatus::Code(5)));
    }

    #[test]
    fn test_run_command_or_error_handling() {
        test_error_handling(true,  |cmd, env| Or(cmd, true_cmd()).run(env), Some(EXIT_SUCCESS));
        test_error_handling(false, |cmd, env| Or(false_cmd(), cmd).run(env), Some(EXIT_SUCCESS));
    }

    #[test]
    fn test_run_command_function_declaration() {
        let fn_name = "function_name";
        let mut env = Env::new().unwrap();
        let func = Function(fn_name.to_string(), Rc::new(*false_cmd()));
        assert_eq!(func.run(&mut env), Ok(EXIT_SUCCESS));
        assert_eq!(cmd!(fn_name).run(&mut env), Ok(ExitStatus::Code(1)));
    }

    #[test]
    fn test_run_compound_local_redirections_applied_correctly_with_no_prev_redirections() {
        // Make sure the environment has NO open file descriptors
        let mut env = Env::with_config(None, None, None, Some(vec!())).unwrap();
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push(String::from("out"));

        let cmd = Compound(
            Box::new(Brace(vec!(
                Simple(Box::new(SimpleCommand {
                    cmd: Some((word("echo"), vec!(word("out")))),
                    io: vec!(),
                    vars: vec!(),
                })),
                Simple(Box::new(SimpleCommand {
                    cmd: Some((word("echo"), vec!(word("err")))),
                    io: vec!(Redirect::DupWrite(Some(1), word("2"))),
                    vars: vec!(),
                })),
            ))),
            vec!(
                Redirect::Write(Some(2), word(file_path.display())),
                Redirect::DupWrite(Some(1), word("2")),
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
    fn test_run_compound_local_redirections_applied_correctly_with_prev_redirections() {
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
            Box::new(Brace(vec!(
                Simple(Box::new(SimpleCommand {
                    cmd: Some((word("echo"), vec!(word("out")))),
                    io: vec!(),
                    vars: vec!(),
                })),
                Simple(Box::new(SimpleCommand {
                    cmd: Some((word("echo"), vec!(word("err")))),
                    io: vec!(Redirect::DupWrite(Some(1), word("2"))),
                    vars: vec!(),
                })),
            ))),
            vec!(
                Redirect::Write(Some(2), word(file_path.display())),
                Redirect::DupWrite(Some(1), word("2")),
            )
        );

        // Check that local override worked
        assert_eq!(Compound(cmd_body.clone(), cmd_redirects).run(&mut env), Ok(EXIT_SUCCESS));
        let mut read = String::new();
        Permissions::Read.open(&file_path).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "out\nerr\n");

        // Check that defaults remained the same
        assert_eq!(Compound(cmd_body, vec!()).run(&mut env), Ok(EXIT_SUCCESS));

        read.clear();
        Permissions::Read.open(&file_path_out).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "out\n");

        read.clear();
        Permissions::Read.open(&file_path_err).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "err\n");
    }

    #[test]
    fn test_run_compound_multiple_local_redirections_last_wins_and_prev_fd_properly_restored() {
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

        let cmd = Compound(
            Box::new(Brace(vec!(*cmd!("echo", "out")))),
            vec!(
                Redirect::Write(Some(1), word(&file_path_empty.display())),
                Redirect::Write(Some(1), word(&file_path.display())),
            )
        );

        assert_eq!(cmd.run(&mut env), Ok(EXIT_SUCCESS));
        assert_eq!(cmd!("echo", "default").run(&mut env), Ok(EXIT_SUCCESS));

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
    fn test_run_compound_local_redirections_closed_after_command_exits_but_side_effects_remain() {
        use syntax::ast::ParameterSubstitution::Assign;
        use syntax::ast::ComplexWord::Single;
        use syntax::ast::SimpleWord::{Literal, Subst};
        use syntax::ast::TopLevelWord;
        use syntax::ast::Word::Simple;

        let var = "var";
        let value = "foobar";
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push(String::from("out"));

        let file = file_path.display().to_string();
        let file = TopLevelWord(Single(Simple(Box::new(Literal(file)))));
        let var_value = TopLevelWord(Single(Simple(Box::new(Literal(value.to_string())))));

        let mut env = Env::new().unwrap();

        let cmd = Compound(
            Box::new(Brace(vec!())),
            vec!(
                Redirect::Write(Some(3), file.clone()),
                Redirect::Write(Some(4), file.clone()),
                Redirect::Write(Some(5), TopLevelWord(Single(Simple(Box::new(Subst(Box::new(Assign(
                    true,
                    Parameter::Var(var.to_string()),
                    Some(var_value),
                )))))))),
            )
        );

        assert_eq!(cmd.run(&mut env), Ok(EXIT_SUCCESS));
        assert!(env.file_desc(3).is_none());
        assert!(env.file_desc(4).is_none());
        assert!(env.file_desc(5).is_none());
        assert_eq!(**env.var(var).unwrap(), value);
    }

    #[test]
    fn test_run_compound_local_redirections_not_reset_if_fd_changed_via_exec() {
        const FD_EXEC_OPEN: Fd = STDOUT_FILENO;
        const FD_EXEC_CLOSE: Fd = STDERR_FILENO;
        const FD_EXEC_CHANGE: Fd = 3;

        let fn_name = String::from("foofn");
        let tempdir = mktmp!();

        let mut file_path_default = PathBuf::new();
        file_path_default.push(tempdir.path());
        file_path_default.push(String::from("default"));

        let mut file_exec_open_path = PathBuf::new();
        file_exec_open_path.push(tempdir.path());
        file_exec_open_path.push(String::from("exec_open"));

        let mut file_exec_change_path = PathBuf::new();
        file_exec_change_path.push(tempdir.path());
        file_exec_change_path.push(String::from("exec_change"));

        let file_default = Permissions::Write.open(&file_path_default).unwrap();

        let mut env = Env::with_config(None, None, None, Some(vec!(
            (FD_EXEC_CLOSE, Rc::new(FileDesc::from(file_default)), Permissions::Write),
        ))).unwrap();

        // Mock a function which will change some file descriptors via `exec` utility
        {
            let file_exec_open_path = file_exec_open_path.clone();
            let file_exec_change_path = file_exec_change_path.clone();

            env.set_function(fn_name.clone(), MockFn::new(move |mut env| {
                let file_exec_open = FileDesc::from(Permissions::Write.open(&file_exec_open_path).unwrap());
                let file_exec_change = FileDesc::from(Permissions::Write.open(&file_exec_change_path).unwrap());

                env.close_file_desc(FD_EXEC_CLOSE);
                env.set_file_desc(FD_EXEC_CHANGE, Rc::new(file_exec_change), Permissions::Write);
                env.set_file_desc(FD_EXEC_OPEN, Rc::new(file_exec_open), Permissions::Write);
                Ok(EXIT_SUCCESS)
            }));
        }

        let cmd = Compound(
            Box::new(Brace(vec!(*cmd!(fn_name)))),
            vec!(
                Redirect::Write(Some(FD_EXEC_CLOSE), word(DEV_NULL)),
                Redirect::Write(Some(FD_EXEC_CHANGE), word(DEV_NULL)),
                Redirect::DupWrite(Some(FD_EXEC_OPEN), word("-")),
            )
        );

        assert_eq!(cmd.run(&mut env), Ok(EXIT_SUCCESS));
        assert!(env.file_desc(FD_EXEC_CLOSE).is_none());

        unsafe {
            env.file_desc(FD_EXEC_OPEN).unwrap().0.unsafe_write().write(stringify!(FD_EXEC_OPEN).as_bytes()).unwrap();
            env.file_desc(FD_EXEC_CHANGE).unwrap().0.unsafe_write().write(stringify!(FD_EXEC_CHANGE).as_bytes()).unwrap();
        }

        let mut read = String::new();
        Permissions::Read.open(&file_exec_open_path).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, stringify!(FD_EXEC_OPEN));

        read.clear();
        Permissions::Read.open(&file_exec_change_path).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, stringify!(FD_EXEC_CHANGE));

        read.clear();
        Permissions::Read.open(&file_path_default).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "");
    }

    #[test]
    fn test_run_compound_brace() {
        let tempdir = mktmp!();

        let mut file_path = PathBuf::new();
        file_path.push(tempdir.path());
        file_path.push(String::from("out"));

        let file = Permissions::Write.open(&file_path).unwrap();

        let mut env = Env::with_config(None, None, None, Some(vec!(
            (STDOUT_FILENO, Rc::new(file.into()), Permissions::Write)
        ))).unwrap();

        let cmd: CompoundCommand = Brace(vec!(
            *cmd!("echo", "foo"),
            *false_cmd(),
            *cmd!("echo", "bar"),
            *true_cmd(),
            *exit(42),
        ));

        assert_eq!(cmd.run(&mut env), Ok(ExitStatus::Code(42)));

        let mut read = String::new();
        Permissions::Read.open(&file_path).unwrap().read_to_string(&mut read).unwrap();
        assert_eq!(read, "foo\nbar\n");
    }

    #[test]
    fn test_run_command_compound_brace_error_handling() {
        test_error_handling(true, |cmd, env| {
            let compound: CompoundCommand = Brace(vec!(*cmd, *exit(42)));
            compound.run(env)
        }, Some(ExitStatus::Code(42)));

        test_error_handling(true, |cmd, env| {
            let compound: CompoundCommand = Brace(vec!(*true_cmd(), *cmd));
            compound.run(env)
        }, None);

        test_error_handling_fatals(false, |cmd, env| {
            let should_not_run = "should not run";
            env.set_function(should_not_run.to_string(), MockFn::new(|_| {
                panic!("ran command that should not be run")
            }));

            let compound: CompoundCommand = Brace(vec!(*cmd, *cmd!(should_not_run)));
            compound.run(env)
        }, None);
    }

    #[test]
    fn test_run_command_if() {
        let fn_name_should_not_run = "foo_fn_should_not_run";
        let cmd_should_not_run = *cmd!(fn_name_should_not_run);
        let cmd_exit = *exit(42);
        const EXIT: ExitStatus = ExitStatus::Code(42);

        let mut env = Env::new().unwrap();
        env.set_function(String::from(fn_name_should_not_run), MockFn::new(|_| {
            panic!("ran command that should not be run")
        }));

        let body_with_true_guard = vec!(
            (vec!(*false_cmd()), vec!(cmd_should_not_run.clone())),
            (vec!(*false_cmd()), vec!(cmd_should_not_run.clone())),
            (vec!(*true_cmd()), vec!(cmd_exit.clone())),
            (vec!(cmd_should_not_run.clone()), vec!(cmd_should_not_run.clone())),
        );

        let body_without_true_guard = vec!(
            (vec!(*false_cmd()), vec!(cmd_should_not_run.clone())),
            (vec!(*false_cmd()), vec!(cmd_should_not_run.clone())),
        );

        let compound: CompoundCommand =
            If(body_with_true_guard.clone(), Some(vec!(cmd_should_not_run.clone())));
        assert_eq!(compound.run(&mut env), Ok(EXIT));
        let compound: CompoundCommand =
            If(body_without_true_guard.clone(), Some(vec!(cmd_exit.clone())));
        assert_eq!(compound.run(&mut env), Ok(EXIT));

        let compound: CompoundCommand = If(body_with_true_guard.clone(), None);
        assert_eq!(compound.run(&mut env), Ok(EXIT));
        let compound: CompoundCommand = If(body_without_true_guard.clone(), None);
        assert_eq!(compound.run(&mut env), Ok(EXIT_SUCCESS));
    }

    #[test]
    fn test_run_command_if_malformed() {
        let mut env = Env::new().unwrap();

        let compound: CompoundCommand = If(vec!(), Some(vec!(*true_cmd())));
        assert_eq!(compound.run(&mut env), Ok(EXIT_ERROR));
        assert_eq!(env.last_status.success(), false);

        let compound: CompoundCommand = If(vec!(), None);
        assert_eq!(compound.run(&mut env), Ok(EXIT_ERROR));
        assert_eq!(env.last_status.success(), false);
    }

    #[test]
    fn test_run_command_if_error_handling() {
        let should_not_run = "foo_fn_should_not_run";
        let fn_should_not_run = MockFn::new(|_| {
            panic!("ran command that should not be run")
        });

        // Error in guard
        test_error_handling(true, |cmd, env| {
            env.set_function(should_not_run.to_string(), fn_should_not_run.clone());
            let compound: CompoundCommand = If(
                vec!((vec!(*cmd), vec!(*cmd!(should_not_run)))),
                Some(vec!(*exit(42)))
            );
            compound.run(env)
        }, Some(ExitStatus::Code(42)));

        // Error in body of successful guard
        test_error_handling(true, |cmd, env| {
            env.set_function(should_not_run.to_string(), fn_should_not_run.clone());
            let compound: CompoundCommand = If(
                vec!((vec!(*true_cmd()), vec!(*cmd))),
                Some(vec!(*cmd!(should_not_run)))
            );
            compound.run(env)
        }, None);

        // Error in body of else part
        test_error_handling(true, |cmd, env| {
            env.set_function(should_not_run.to_string(), fn_should_not_run.clone());
            let compound: CompoundCommand = If(
                vec!((vec!(*false_cmd()), vec!(*cmd!(should_not_run)))),
                Some(vec!(*cmd))
            );
            compound.run(env)
        }, None);
    }

    #[test]
    fn test_run_command_subshell() {
        let mut env = Env::new().unwrap();
        let compound: CompoundCommand = Subshell(vec!(*exit(5), *exit(42)));
        assert_eq!(compound.run(&mut env), Ok(ExitStatus::Code(42)));
    }

    #[test]
    fn test_run_command_subshell_child_inherits_var_definitions() {
        let var_name = "var".to_string();
        let var_value = "value".to_string();
        let fn_check_vars = "fn_check_vars";

        let mut env = Env::new().unwrap();
        env.set_var(var_name.clone(), Rc::new(var_value.clone()));

        {
            env.set_function(fn_check_vars.to_string(), MockFn::new(move |env| {
                assert_eq!(&**env.var(&var_name).unwrap(), &var_value);
                Ok(EXIT_SUCCESS)
            }));
        }
        assert_eq!(cmd!(fn_check_vars).run(&mut env), Ok(EXIT_SUCCESS));
    }

    #[test]
    fn test_run_command_subshell_parent_isolated_from_var_changes() {
        let parent_name = "parent-var".to_string();
        let parent_value = "parent-value".to_string();
        let child_name = "child-var".to_string();
        let child_value = "child-value";
        let fn_check_vars = "fn_check_vars";

        let mut env = Env::new().unwrap();
        env.set_var(parent_name.clone(), Rc::new(parent_value.clone()));

        {
            let parent_name = parent_name.clone();
            let child_name = child_name.clone();

            env.set_function(fn_check_vars.to_string(), MockFn::new(move |env| {
                assert_eq!(&**env.var(&parent_name).unwrap(), child_value);
                assert_eq!(&**env.var(&child_name).unwrap(), child_value);
                Ok(EXIT_SUCCESS)
            }));
        }

        let compound: CompoundCommand = Subshell(vec!(
            Simple(Box::new(SimpleCommand {
                cmd: None,
                io: vec!(),
                vars: vec!((parent_name.clone(), Some(word(child_value)))),
            })),
            Simple(Box::new(SimpleCommand {
                cmd: None,
                io: vec!(),
                vars: vec!((child_name.clone(), Some(word(child_value)))),
            })),
            *cmd!(fn_check_vars)
        ));
        assert_eq!(compound.run(&mut env), Ok(EXIT_SUCCESS));

        assert_eq!(&**env.var(&parent_name).unwrap(), &parent_value);
        assert_eq!(env.var(&child_name), None);
    }

    #[test]
    fn test_run_command_subshell_child_inherits_function_definitions() {
        let fn_name_default = "fn_name_default";
        let default_exit_code = 10;

        let mut env = Env::new().unwrap();

        // Subshells should inherit function definitions
        {
            env.set_function(String::from(fn_name_default), MockFn::new(move |_| {
                Ok(ExitStatus::Code(default_exit_code))
            }));
        }
        let compound: CompoundCommand = Subshell(vec!(*cmd!(fn_name_default)));
        assert_eq!(compound.run(&mut env), Ok(ExitStatus::Code(default_exit_code)));
    }

    #[test]
    fn test_run_command_subshell_parent_isolated_from_function_changes() {
        let fn_name = "fn_name";
        let fn_name_parent = "fn_name_parent";

        let parent_exit_code = 5;
        let override_exit_code = 42;

        let mut env = Env::new().unwrap();

        // Defining a new function within subshell should disappear
        let compound: CompoundCommand = Subshell(vec!(
            Function(fn_name.to_string(), Rc::new(*exit(42))),
            *cmd!(fn_name),
        ));
        assert_eq!(compound.run(&mut env), Ok(ExitStatus::Code(override_exit_code)));
        assert_eq!(env.run_function(Rc::new(fn_name.to_string()), vec!()), None);

        // Redefining function within subshell should revert to original
        {
            let parent_exit_code = parent_exit_code.clone();
            env.set_function(fn_name_parent.to_string(), MockFn::new(move |_| {
                Ok(ExitStatus::Code(parent_exit_code))
            }));
        }
        let compound: CompoundCommand = Subshell(vec!(
            Function(fn_name_parent.to_string(), Rc::new(*exit(42))),
            *cmd!(fn_name_parent),
        ));
        assert_eq!(compound.run(&mut env), Ok(ExitStatus::Code(override_exit_code)));
        assert_eq!(cmd!(fn_name_parent).run(&mut env), Ok(ExitStatus::Code(parent_exit_code)));
    }

    #[test]
    fn test_run_command_subshell_child_inherits_file_descriptors() {
        let msg = "some secret message";
        let io::Pipe { mut reader, writer } = io::Pipe::new().unwrap();

        let guard = thread::spawn(move || {
            let target_fd = 5;
            let mut env = Env::new().unwrap();
            let writer = Rc::new(writer);
            env.set_file_desc(target_fd, writer.clone(), Permissions::Write);

            let compound: CompoundCommand = Subshell(vec!(
                Simple(Box::new(SimpleCommand {
                    cmd: Some((word("echo"), vec!(word(msg)))),
                    vars: vec!(),
                    io: vec!(Redirect::DupWrite(Some(STDOUT_FILENO), word(target_fd))),
                }))
            ));
            assert_eq!(compound.run(&mut env), Ok(EXIT_SUCCESS));

            env.close_file_desc(target_fd);
            let mut writer = Rc::try_unwrap(writer).unwrap();
            writer.flush().unwrap();
            drop(writer);
        });

        let mut read = String::new();
        reader.read_to_string(&mut read).unwrap();
        guard.join().unwrap();
        assert_eq!(read, format!("{}\n", msg));
    }

    #[test]
    fn test_run_command_subshell_parent_isolated_from_file_descritor_changes() {
        let target_fd = 5;
        let new_fd = 6;
        let new_msg = "some new secret message";
        let change_msg = "some change secret message";
        let parent_msg = "parent post msg";
        let io::Pipe { reader: mut new_reader,    writer: new_writer    } = io::Pipe::new().unwrap();
        let io::Pipe { reader: mut change_reader, writer: change_writer } = io::Pipe::new().unwrap();
        let io::Pipe { reader: mut parent_reader, writer: parent_writer } = io::Pipe::new().unwrap();

        let guard = thread::spawn(move || {
            let exec = "exec_fn";
            let new_writer    = Rc::new(new_writer);
            let change_writer = Rc::new(change_writer);
            let parent_writer = Rc::new(parent_writer);

            let mut env = Env::new().unwrap();
            env.set_file_desc(target_fd, parent_writer.clone(), Permissions::Write);

            {
                let new_writer = new_writer;
                let change_writer = change_writer;
                env.set_function(exec.to_string(), MockFn::new(move |mut env| {
                    env.set_file_desc(new_fd, new_writer.clone(), Permissions::Write);
                    env.set_file_desc(target_fd, change_writer.clone(), Permissions::Write);
                    Ok(EXIT_SUCCESS)
                }));
            }

            let compound: CompoundCommand = Subshell(vec!(
                *cmd!(exec),
                Simple(Box::new(SimpleCommand {
                    cmd: Some((word("echo"), vec!(word(new_msg)))),
                    vars: vec!(),
                    io: vec!(Redirect::DupWrite(Some(STDOUT_FILENO), word(new_fd))),
                })),
                Simple(Box::new(SimpleCommand {
                    cmd: Some((word("echo"), vec!(word(change_msg)))),
                    vars: vec!(),
                    io: vec!(Redirect::DupWrite(Some(STDOUT_FILENO), word(target_fd))),
                })),
            ));
            assert_eq!(compound.run(&mut env), Ok(EXIT_SUCCESS));

            env.close_file_desc(target_fd);
            assert!(env.file_desc(new_fd).is_none());

            let mut parent_writer = Rc::try_unwrap(parent_writer).unwrap();
            parent_writer.write_all(parent_msg.as_bytes()).unwrap();
            parent_writer.flush().unwrap();

            drop(parent_writer);
        });

        let mut new_read = String::new();
        new_reader.read_to_string(&mut new_read).unwrap();

        let mut change_read = String::new();
        change_reader.read_to_string(&mut change_read).unwrap();

        let mut parent_read = String::new();
        parent_reader.read_to_string(&mut parent_read).unwrap();

        guard.join().unwrap();

        assert_eq!(new_read, format!("{}\n", new_msg));
        assert_eq!(change_read, format!("{}\n", change_msg));
        assert_eq!(parent_read, parent_msg);
    }

    #[test]
    fn test_run_command_subshell_error_handling() {
        test_error_handling_non_fatals(true, |cmd, env| {
            let compound: CompoundCommand = Subshell(vec!(*cmd, *exit(42)));
            compound.run(env)
        }, Some(ExitStatus::Code(42)));
        test_error_handling_fatals(true, |cmd, env| {
            let compound: CompoundCommand = Subshell(vec!(*cmd, *exit(42)));
            compound.run(env)
        }, None);

        test_error_handling_non_fatals(true, |cmd, env| {
            let compound: CompoundCommand = Subshell(vec!(*true_cmd(), *cmd));
            compound.run(env)
        }, None);
        test_error_handling_fatals(true, |cmd, env| {
            let compound: CompoundCommand = Subshell(vec!(*true_cmd(), *cmd));
            compound.run(env)
        }, None);

        test_error_handling_fatals(true, |cmd, env| {
            let should_not_run = "should not run";
            env.set_function(should_not_run.to_string(), MockFn::new(|_| {
                panic!("ran command that should not be run")
            }));

            let compound: CompoundCommand = Subshell(vec!(*cmd, *cmd!(should_not_run)));
            compound.run(env)
        }, None);
    }
}
