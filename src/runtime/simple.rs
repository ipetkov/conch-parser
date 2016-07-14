//! Implementation of running `SimpleCommands`

#[cfg(unix)]
use libc;

use runtime::{EXIT_CMD_NOT_EXECUTABLE, EXIT_CMD_NOT_FOUND, EXIT_ERROR, EXIT_SUCCESS,
              ExitStatus, Fd, Result, Run, STDERR_FILENO, STDIN_FILENO, STDOUT_FILENO,
              run_with_local_redirections};
use runtime::env::{FileDescEnvironment, FunctionEnvironment, FunctionExecutorEnvironment,
                   IsInteractiveEnvironment, LastStatusEnvironment, StringWrapper, SubEnvironment,
                   VariableEnvironment};
use runtime::errors::{CommandError, RuntimeError};
use runtime::eval::WordEval;
use runtime::io::FileDescWrapper;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::convert::Into;
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::iter::{FromIterator, IntoIterator, Iterator};
use std::process::{self, Stdio};

use syntax::ast::SimpleCommand;

enum CommandPrep<T, F> {
    Finished(ExitStatus),
    Data(PrepData<T, F>),
}

struct PrepData<T, F> {
    name: T,
    args: Vec<T>,
    extra_env_vars: Vec<(String, T)>,
    io: HashMap<Fd, F>,
}

impl<T, E: ?Sized, W> Run<E> for SimpleCommand<W>
    where T: StringWrapper,
          E: FileDescEnvironment
              + FunctionExecutorEnvironment<FnName = T>
              + IsInteractiveEnvironment
              + LastStatusEnvironment
              + SubEnvironment
              + VariableEnvironment<Var = T>,
          E::FileHandle: FileDescWrapper,
          E::VarName: StringWrapper,
          W: WordEval<T, E>,
{
    fn run(&self, env: &mut E) -> Result<ExitStatus> {
        let ret = self.run_simple_command(env);
        let last_status = match ret {
            Ok(exit) => exit,
            Err(RuntimeError::Command(CommandError::NotExecutable(_))) => EXIT_CMD_NOT_EXECUTABLE,
            Err(RuntimeError::Command(CommandError::NotFound(_))) => EXIT_CMD_NOT_FOUND,
            Err(_) => EXIT_ERROR,
        };

        env.set_last_status(last_status);
        ret
    }
}

impl<W> SimpleCommand<W> {
    fn run_simple_command<T, E>(&self, env: &mut E) -> Result<ExitStatus>
        where T: StringWrapper,
              E: FileDescEnvironment
                  + FunctionExecutorEnvironment<FnName = T>
                  + IsInteractiveEnvironment
                  + SubEnvironment
                  + VariableEnvironment<Var = T>,
              E::FileHandle: FileDescWrapper,
              E::VarName: StringWrapper,
              W: WordEval<T, E>,
    {
        // Whether this is a variable assignment, function invocation,
        // or regular command, make sure we open/touch all redirects,
        // as this will have side effects (possibly desired by script).
        let prep = try!(run_with_local_redirections(env, &self.io, |env| {
            let vars: Vec<_> = try!(self.vars.iter()
                .map(|&(ref var, ref val)| val.as_ref()
                     .map_or_else(|| Ok(String::new().into()), |val| val.eval_as_assignment(env))
                     .map(|val| (var.clone(), val))
                )
                .collect()
            );

            let (cmd, args) = match self.cmd {
                None => {
                    for (var, val) in vars {
                        env.set_var(var.into(), val);
                    }
                    return Ok(CommandPrep::Finished(EXIT_SUCCESS));
                },
                Some((ref cmd, ref args)) => {
                    // bash and zsh just grab first field of an expansion
                    let mut cmd_fields = try!(cmd.eval(env)).into_iter();
                    let cmd_name = match cmd_fields.next() {
                        Some(exe) => exe,
                        None => return Err(CommandError::NotFound(String::new()).into()),
                    };

                    let mut cmd_args = Vec::from_iter(cmd_fields);
                    for arg in args.iter() {
                        cmd_args.extend(try!(arg.eval(env)))
                    }

                    (cmd_name, cmd_args)
                },
            };

            // FIXME: look up aliases

            // According to POSIX, functions preceed the build-in utilities, but bash and zsh
            // treat functions with first priority, so we will follow this precendent.
            // FIXME: local var overloads not handled
            if env.has_function(&cmd) {
                return match env.run_function(&cmd, args) {
                    Some(ret) => ret.map(CommandPrep::Finished),
                    None => Err(CommandError::NotFound(cmd.into_owned()).into()),
                };
            }

            // All local redirects here will only be used for spawning this specific command.
            // At the end of the call the local redirects will be dropped by the environment,
            // so we should be able to unwrap any Rc/Arc to a raw handle (since they will be
            // the only copy at that point), which avoids us having to (needlessly) duplicate
            // the underlying OS file handle.
            let io = [STDIN_FILENO, STDOUT_FILENO, STDERR_FILENO].iter()
                .filter_map(|&fd| env.file_desc(fd).map(|(fdes, _)| (fd, fdes.clone())))
                .collect();

            Ok(CommandPrep::Data(PrepData {
                name: cmd,
                args: args,
                extra_env_vars: vars,
                io: io,
            }))
        }));

        let prep = match prep {
            CommandPrep::Finished(exit) => return Ok(exit),
            CommandPrep::Data(prep) => prep,
        };

        let mut cmd = process::Command::new(prep.name.as_str());
        for arg in prep.args {
            cmd.arg(arg.as_str());
        }

        // First inherit all default ENV variables
        for &(var, val) in &*env.env_vars() {
            cmd.env(var.as_str(), val.as_str());
        }

        // Then apply the overrides
        for (var, val) in prep.extra_env_vars {
            cmd.env(var.as_str(), val.as_str());
        }

        let mut local_io: HashMap<_, _> = try!(prep.io.into_iter()
            .map(|(fd, wrapper)| wrapper.try_unwrap()
                 .or_else(|w| w.borrow().duplicate())
                 .map_err(|io| RuntimeError::Io(io, Some(format!("file descriptor {}", fd))))
                 .map(|fdes| (fd, fdes))
            )
            .collect()
        );

        let mut get_redirect = |fd| -> Stdio {
            local_io.remove(&fd).map_or_else(Stdio::null, Into::into)
        };

        // FIXME: we should eventually inherit all fds in the environment (at least on UNIX)
        cmd.stdin(get_redirect(STDIN_FILENO));
        cmd.stdout(get_redirect(STDOUT_FILENO));
        cmd.stderr(get_redirect(STDERR_FILENO));

        let cmd_name = prep.name;
        cmd.status()
            .map(ExitStatus::from)
            .map_err(|e| {
                let cmd_name = cmd_name.into_owned();
                if IoErrorKind::NotFound == e.kind() {
                    CommandError::NotFound(cmd_name).into()
                } else if is_enoexec(&e) {
                    CommandError::NotExecutable(cmd_name).into()
                } else {
                    RuntimeError::Io(e, Some(cmd_name))
                }
            })
    }
}

#[cfg(unix)]
fn is_enoexec(err: &IoError) -> bool {
    Some(libc::ENOEXEC) == err.raw_os_error()
}

#[cfg(windows)]
fn is_enoexec(_err: &IoError) -> bool {
    false
}
