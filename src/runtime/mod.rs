//! This module defines a runtime environment capable of executing parsed shell commands.

use glob;
use libc;

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::convert::{From, Into};
use std::fmt;
use std::io::{Error as IoError, ErrorKind as IoErrorKind, Write};
use std::iter::{IntoIterator, Iterator};
use std::process::{self, Stdio};
use std::rc::Rc;
use std::result;

use syntax::ast::{Command, CompoundCommand, GuardBodyPair, SimpleCommand, Redirect};
use runtime::eval::{Fields, TildeExpansion, WordEval, WordEvalConfig};
use runtime::io::{FileDesc, Permissions};

mod errors;
mod env;

pub mod eval;
pub mod io;
pub use self::env::*;
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
                RuntimeError::Custom(..) |
                RuntimeError::Expansion(..) => return Err(err),

                RuntimeError::Io(..)            |
                RuntimeError::Redirection(..)   |
                RuntimeError::Command(..)       |
                RuntimeError::Unimplemented(..) => {
                    // Whoever returned the error should have been responsible
                    // enough to set the last status as appropriate.
                    $env.report_error(&err);
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
            for &(ref var, ref val) in &self.vars {
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
                return Err(CommandError::NotFound(String::new()).into());
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
                        Err(CommandError::NotFound(rc_to_owned(cmd_name)).into())
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
        for &(ref var, ref val) in &self.vars {
            if let Some(ref w) = *val {
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
                .map_err(|io| RuntimeError::Io(io, format!("file descriptor {}", fd_debug)));

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
                let cmd_name = rc_to_owned(cmd_name);
                let (exit, err) = if IoErrorKind::NotFound == e.kind() {
                    (EXIT_CMD_NOT_FOUND, CommandError::NotFound(cmd_name).into())
                } else if is_enoexec(&e) {
                    (EXIT_CMD_NOT_EXECUTABLE, CommandError::NotExecutable(cmd_name).into())
                } else {
                    (EXIT_ERROR, RuntimeError::Io(e, cmd_name))
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

            While(GuardBodyPair { ref guard, ref body }) |
            Until(GuardBodyPair { ref guard, ref body }) => {
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

            If(ref conditionals, ref els) => if conditionals.is_empty() {
                // An `If` AST node without any branches (conditional guards)
                // isn't really a valid instantiation, but we'll just
                // pretend it was an unsuccessful command (which it sort of is).
                let exit = EXIT_ERROR;
                env.set_last_status(exit);
                exit
            } else {
                let mut exit = None;
                for &GuardBodyPair { ref guard, ref body } in conditionals.iter() {
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
                        env.report_error(&err);
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
    use runtime::eval::RedirectAction::*;

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

            Ok(redirect_action) => {
                let (fd, fdes_and_perms) = match redirect_action {
                    Close(fd) => (fd, None),
                    Open(fd, fdes, perms) => (fd, Some((fdes, perms))),
                };

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

/// Attempts to unwrap an Rc<T>, cloning the inner value if the unwrap fails.
fn rc_to_owned<T: Clone>(rc: Rc<T>) -> T {
    Rc::try_unwrap(rc).unwrap_or_else(|rc| (*rc).clone())
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
    pub const DEV_NULL: &'static str = "/dev/null";

    #[cfg(windows)]
    pub const DEV_NULL: &'static str = "NUL";

    pub struct MockFn<F: FnMut(&mut Environment) -> Result<ExitStatus>> {
        callback: RefCell<F>,
    }

    impl<F: FnMut(&mut Environment) -> Result<ExitStatus>> MockFn<F> {
        pub fn new(f: F) -> Rc<Self> {
            Rc::new(MockFn { callback: RefCell::new(f) })
        }
    }

    impl<F: FnMut(&mut Environment) -> Result<ExitStatus>> Run for MockFn<F> {
        fn run(&self, env: &mut Environment) -> Result<ExitStatus> {
            (&mut *self.callback.borrow_mut())(env)
        }
    }

    #[derive(Clone)]
    pub enum MockWord<'a> {
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

    pub fn word<'a, T: ToString>(s: T) -> MockWord<'a> {
        MockWord::Regular(Rc::new(s.to_string()))
    }

    fn dev_null() -> FileDesc {
        OpenOptions::new().read(true).write(true).open(DEV_NULL).unwrap().into()
    }

    pub fn file_desc() -> FileDesc {
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
            RuntimeError::Command(CommandError::NotFound("".to_string())),
            RuntimeError::Command(CommandError::NotExecutable("".to_string())),
            RuntimeError::Redirection(RedirectionError::Ambiguous(vec!())),
            RuntimeError::Redirection(RedirectionError::BadFdSrc("".to_string())),
            RuntimeError::Redirection(RedirectionError::BadFdPerms(0, Permissions::Read)),
            RuntimeError::Unimplemented("unimplemented"),
            RuntimeError::Io(IoError::last_os_error(), "".to_string()),
        );
    }

    fn test_error_handling_fatals<'a, F>(swallow_fatals: bool,
                                         test: F,
                                         ok_status: Option<ExitStatus>)
        where F: Fn(Box<Command<'a>>, &mut Environment) -> Result<ExitStatus>
    {
        use std::error::Error;
        use std::fmt;

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
            RuntimeError::Expansion(ExpansionError::EmptyParameter(Parameter::At, "".to_string())),
        );

        // Custom errors might not be Eq so we have to be more creative to check them.
        #[derive(Debug, Copy, Clone, Eq, PartialEq)]
        struct MockErr(isize);
        impl Error for MockErr {
            fn description(&self) -> &str { "" }
        }
        impl fmt::Display for MockErr {
            fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result { Ok(()) }
        }

        let result = test(
            cmd!(move || { RuntimeError::Custom(Box::new(MockErr(42))) }),
            &mut *env.sub_env()
        );

        if swallow_fatals {
            assert_eq!(result, Ok(ok_status.clone().unwrap_or(EXIT_ERROR_MOCK)));
        } else {
            // Good enough for now
            assert!(result.is_err());
        }
    }

    /// For exhaustively testing against handling of different error types
    fn test_error_handling<'a, F>(swallow_errors: bool, test: F, ok_status: Option<ExitStatus>)
        where F: Fn(Box<Command<'a>>, &mut Environment) -> Result<ExitStatus>
    {
        test_error_handling_non_fatals(swallow_errors, &test, ok_status);
        test_error_handling_fatals(false, test, ok_status);
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
        let mut env = Env::with_config(false, None, None, None, Some(vec!())).unwrap();
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

        let mut env = Env::with_config(false, None, None, None, Some(vec!(
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

        let mut env = Env::with_config(false, None, None, None, Some(vec!(
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
    fn test_run_compound_redirections_closed_after_command_exits_side_effects_remain_after_error() {
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

        let mut missing_file_path = PathBuf::new();
        missing_file_path.push(tempdir.path());
        missing_file_path.push(String::from("if_this_file_exists_the_unverse_has_ended"));

        let file = file_path.display().to_string();
        let file = TopLevelWord(Single(Simple(Box::new(Literal(file)))));

        let missing = missing_file_path.display().to_string();
        let missing = TopLevelWord(Single(Simple(Box::new(Literal(missing)))));

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
                Redirect::Read(Some(6), missing)
            )
        );

        cmd.run(&mut env).unwrap_err();
        assert!(env.file_desc(3).is_none());
        assert!(env.file_desc(4).is_none());
        assert!(env.file_desc(5).is_none());
        assert!(env.file_desc(6).is_none());
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

        let mut env = Env::with_config(false, None, None, None, Some(vec!(
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

        let mut env = Env::with_config(false, None, None, None, Some(vec!(
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
        use syntax::ast::GuardBodyPair;

        let fn_name_should_not_run = "foo_fn_should_not_run";
        let cmd_should_not_run = *cmd!(fn_name_should_not_run);
        let cmd_exit = *exit(42);
        const EXIT: ExitStatus = ExitStatus::Code(42);

        let mut env = Env::new().unwrap();
        env.set_function(String::from(fn_name_should_not_run), MockFn::new(|_| {
            panic!("ran command that should not be run")
        }));

        let body_with_true_guard = vec!(
            GuardBodyPair { guard: vec!(*false_cmd()), body: vec!(cmd_should_not_run.clone()) },
            GuardBodyPair { guard: vec!(*false_cmd()), body: vec!(cmd_should_not_run.clone()) },
            GuardBodyPair { guard: vec!(*true_cmd()), body: vec!(cmd_exit.clone()) },
            GuardBodyPair { guard: vec!(cmd_should_not_run.clone()), body: vec!(cmd_should_not_run.clone()) },
        );

        let body_without_true_guard = vec!(
            GuardBodyPair { guard: vec!(*false_cmd()), body: vec!(cmd_should_not_run.clone()) },
            GuardBodyPair { guard: vec!(*false_cmd()), body: vec!(cmd_should_not_run.clone()) },
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
        assert_eq!(env.last_status().success(), false);

        let compound: CompoundCommand = If(vec!(), None);
        assert_eq!(compound.run(&mut env), Ok(EXIT_ERROR));
        assert_eq!(env.last_status().success(), false);
    }

    #[test]
    fn test_run_command_if_error_handling() {
        use syntax::ast::GuardBodyPair;

        let should_not_run = "foo_fn_should_not_run";
        let fn_should_not_run = MockFn::new(|_| {
            panic!("ran command that should not be run")
        });

        // Error in guard
        test_error_handling(true, |cmd, env| {
            env.set_function(should_not_run.to_string(), fn_should_not_run.clone());
            let compound: CompoundCommand = If(
                vec!(GuardBodyPair { guard: vec!(*cmd), body: vec!(*cmd!(should_not_run)) }),
                Some(vec!(*exit(42)))
            );
            compound.run(env)
        }, Some(ExitStatus::Code(42)));

        // Error in body of successful guard
        test_error_handling(true, |cmd, env| {
            env.set_function(should_not_run.to_string(), fn_should_not_run.clone());
            let compound: CompoundCommand = If(
                vec!(GuardBodyPair { guard: vec!(*true_cmd()), body: vec!(*cmd) }),
                Some(vec!(*cmd!(should_not_run)))
            );
            compound.run(env)
        }, None);

        // Error in body of else part
        test_error_handling(true, |cmd, env| {
            env.set_function(should_not_run.to_string(), fn_should_not_run.clone());
            let compound: CompoundCommand = If(
                vec!(GuardBodyPair { guard: vec!(*false_cmd()), body: vec!(*cmd!(should_not_run))}),
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
        env.set_function(fn_name_parent.to_string(), MockFn::new(move |_| {
            Ok(ExitStatus::Code(parent_exit_code))
        }));

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
