//! Implementation of running `SimpleCommands`

#[cfg(unix)]
use libc;

use runtime::{EXIT_CMD_NOT_EXECUTABLE, EXIT_CMD_NOT_FOUND, EXIT_ERROR, EXIT_SUCCESS,
              ExitStatus, Result, Run, STDERR_FILENO, STDIN_FILENO, STDOUT_FILENO,
              run_with_local_redirections};
use runtime::env::{ArgumentsEnvironment, FileDescEnvironment, FunctionEnvironment,
                   FunctionExecutorEnvironment, IsInteractiveEnvironment,
                   LastStatusEnvironment, StringWrapper, SubEnvironment,
                   VariableEnvironment};
use runtime::errors::{CommandError, RuntimeError};
use runtime::eval::{Fields, WordEval};
use runtime::io::FileDescWrapper;

use std::borrow::Borrow;
use std::convert::Into;
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::iter::{IntoIterator, Iterator};
use std::process::{self, Stdio};

use syntax::ast::SimpleCommand;

impl<T, E: ?Sized, W> Run<E> for SimpleCommand<W>
    where T: StringWrapper,
          E: ArgumentsEnvironment<Arg = T>
              + FileDescEnvironment
              + FunctionEnvironment<Name = T>
              + FunctionExecutorEnvironment
              + IsInteractiveEnvironment
              + LastStatusEnvironment
              + SubEnvironment
              + VariableEnvironment<Var = T>,
          E::FileHandle: FileDescWrapper,
          W: WordEval<T, E>,
{
    fn run(&self, env: &mut E) -> Result<ExitStatus> {
        #[cfg(unix)]
        fn is_enoexec(err: &IoError) -> bool { Some(libc::ENOEXEC) == err.raw_os_error() }

        #[cfg(windows)]
        fn is_enoexec(_err: &IoError) -> bool { false }

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
                match env.run_function(&cmd_name, cmd_args) {
                    Some(ret) => ret,
                    None => {
                        env.set_last_status(EXIT_CMD_NOT_FOUND);
                        Err(CommandError::NotFound(cmd_name.into_owned()).into())
                    },
                }
            });
        }

        let mut cmd = process::Command::new(cmd_name.as_str());
        for arg in cmd_args {
            cmd.arg(arg.as_str());
        }

        // First inherit all default ENV variables
        for &(var, val) in &*env.env_vars() {
            cmd.env(var, val.as_str());
        }

        // Then do any local insertions/overrides
        for &(ref var, ref val) in &self.vars {
            if let Some(ref w) = *val {
                match try!(w.eval(env)) {
                    Fields::Zero      => continue,
                    Fields::Single(s) => cmd.env(var, s.as_str()),
                    f@Fields::At(_)   |
                    f@Fields::Star(_) |
                    f@Fields::Split(_) => cmd.env(var, f.join().as_str()),
                };
            }
        }

        let get_redirect = |handle: Option<E::FileHandle>, fd_debug| -> Result<Stdio> {
            let unwrap_fdes = |fdes: E::FileHandle| fdes.try_unwrap()
                .or_else(|wrapper| wrapper.borrow().duplicate())
                .map_err(|io| RuntimeError::Io(io, Some(format!("file descriptor {}", fd_debug))));

            handle.map_or_else(|| Ok(Stdio::null()),
                               |fdes| unwrap_fdes(fdes).map(|fdes| fdes.into()))
        };

        // All local redirects here will only be used for spawning this specific command.
        // At the end of the call the local redirects will be dropped by the environment,
        // so we should be able to unwrap any Rc/Arc to a raw handle (since they will be
        // the only copy at that point), which avoids us having to (needlessly) duplicate
        // the underlying OS file handle.
        let (cmd_std_in, cmd_std_out, cmd_std_err) = try!(run_with_local_redirections(env,
                                                                                      &self.io,
                                                                                      |env| {
            let extract = |fd: Option<(&E::FileHandle, _)>| fd.map(|(fdes, _)| fdes.clone());
            Ok((extract(env.file_desc(STDIN_FILENO)),
                extract(env.file_desc(STDOUT_FILENO)),
                extract(env.file_desc(STDERR_FILENO))))
        }));

        // FIXME: we should eventually inherit all fds in the environment (at least on UNIX)
        cmd.stdin(try!(get_redirect(cmd_std_in,   STDIN_FILENO)));
        cmd.stdout(try!(get_redirect(cmd_std_out, STDOUT_FILENO)));
        cmd.stderr(try!(get_redirect(cmd_std_err, STDERR_FILENO)));

        match cmd.status() {
            Err(e) => {
                let cmd_name = cmd_name.into_owned();
                let (exit, err) = if IoErrorKind::NotFound == e.kind() {
                    (EXIT_CMD_NOT_FOUND, CommandError::NotFound(cmd_name).into())
                } else if is_enoexec(&e) {
                    (EXIT_CMD_NOT_EXECUTABLE, CommandError::NotExecutable(cmd_name).into())
                } else {
                    (EXIT_ERROR, RuntimeError::Io(e, Some(cmd_name)))
                };
                env.set_last_status(exit);
                Err(err)
            },

            Ok(exit) => {
                let exit = exit.into();
                env.set_last_status(exit);
                Ok(exit)
            }
        }
    }
}
