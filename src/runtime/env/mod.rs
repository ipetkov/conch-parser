//! This module defines an Environment trait to store state between command executions.

use std::borrow::Cow;
use std::collections::HashMap;
use std::convert::From;
use std::fmt;
use std::error;
use std::io::Result as IoResult;
use std::iter::{IntoIterator, Iterator};
use std::rc::Rc;

use runtime::{EXIT_SUCCESS, STDIN_FILENO, STDOUT_FILENO, STDERR_FILENO};
use runtime::{ExitStatus, Fd, Result, Run};
use runtime::io::{dup_stdio, FileDesc, Permissions};

mod last_status_env;

pub use self::last_status_env::*;

/// A struct for configuring a new `Env` instance.
///
/// It implements `Default` so it is possible to selectively override
/// certain attributes while retaining the rest of the default values.
///
/// ```
/// # use shell_lang::runtime::env::{Env, EnvConfig, Environment};
/// let cfg = EnvConfig {
///     name: Some("my_shell".to_owned()),
///     .. Default::default()
/// };
///
/// let env = Env::with_config(cfg).unwrap();
/// assert_eq!(**env.name(), "my_shell");
/// ```
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct EnvConfig {
    /// Specify if the environment is running in interactive mode.
    pub interactive: bool,
    /// The name of the shell/script executing.
    pub name: Option<String>,
    /// The current arguments of the shell/script/function.
    pub args: Option<Vec<String>>,
    /// Environment variables to be inherited by all processes.
    pub env: Option<Vec<(String, String)>>,
    /// A mapping of file descriptors to their OS handles.
    pub fds: Option<Vec<(Fd, Rc<FileDesc>, Permissions)>>,
}

impl Default for EnvConfig {
    fn default() -> Self {
        EnvConfig {
            interactive: false,
            name: None,
            args: None,
            env: None,
            fds: None,
        }
    }
}

/// A shell environment containing any relevant variable, file descriptor, and other information.
#[derive(Clone)]
pub struct Env<'a> {
    /// The current name of the shell/script executing.
    shell_name: Cow<'a, Rc<String>>,
    /// The current arguments of the shell/script/function.
    args: Cow<'a, [Rc<String>]>,
    /// A mapping of all defined function names and executable bodies.
    functions: Cow<'a, HashMap<String, Rc<Run<Env<'a>>>>>,
    /// A mapping of variable names to their values.
    ///
    /// The tupled boolean indicates if a variable should be exported to other commands.
    vars: Cow<'a, HashMap<String, (Rc<String>, bool)>>,
    /// A mapping of file descriptors and their OS handles.
    ///
    /// environment. The tupled value also holds the permissions of the descriptor.
    fds: Cow<'a, HashMap<Fd, (Rc<FileDesc>, Permissions)>>,
    /// The exit status of the last command that was executed.
    last_status: ExitStatus,
    /// If the shell is running in interactive mode
    interactive: bool,
}

impl<'a> fmt::Debug for Env<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        use std::collections::{BTreeMap, BTreeSet};
        #[cfg(windows)] use std::os::windows::io::RawHandle;

        #[derive(Debug)]
        struct FileDescDebug {
            #[cfg(unix)]
            os_handle: ::libc::c_int,
            #[cfg(windows)]
            os_handle: RawHandle,
            permissions: Permissions,
        }

        #[cfg(unix)]
        fn get_os_handle(fdes: &FileDesc) -> ::libc::c_int {
            use std::os::unix::io::AsRawFd;
            fdes.as_raw_fd()
        }

        #[cfg(windows)]
        fn get_os_handle(fdes: &FileDesc) -> RawHandle {
            use std::os::windows::io::AsRawHandle;
            fdes.as_raw_handle()
        }

        let functions: BTreeSet<_> = self.functions.keys().collect();

        let mut vars = BTreeMap::new();
        let mut env_vars = BTreeMap::new();
        for (name, &(ref val, is_env)) in &*self.vars {
            if is_env {
                env_vars.insert(name, val);
            } else {
                vars.insert(name, val);
            };
        }

        let mut fds = BTreeMap::new();
        for (fd, &(ref fdesc, perms)) in &*self.fds {
            fds.insert(fd, FileDescDebug {
                os_handle: get_os_handle(fdesc),
                permissions: perms,
            });
        }

        fmt.debug_struct("Env")
            .field("interactive", &self.interactive)
            .field("shell_name", &self.shell_name)
            .field("args", &self.args)
            .field("functions", &functions)
            .field("env_vars", &env_vars)
            .field("vars", &vars)
            .field("fds", &fds)
            .field("last_status", &self.last_status)
            .finish()
    }
}

impl<'a> Env<'a> {
    /// Creates a new default environment.
    /// See the docs for `Env::with_config` for more information.
    pub fn new() -> IoResult<Self> {
        Self::with_config(Default::default())
    }

    /// Creates an environment using provided config overrides, or data from the
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
    pub fn with_config(cfg: EnvConfig) -> IoResult<Self> {
        use std::env;

        let name = cfg.name.unwrap_or_else(|| env::current_exe().ok().and_then(|path| {
            path.file_name().and_then(|os_str| os_str.to_str().map(|s| s.to_owned()))
        }).unwrap_or_default());

        let args = cfg.args.map_or(Vec::new(), |args| args.into_iter().map(Rc::new).collect());

        let vars = cfg.env.map_or_else(
            || env::vars().map(|(k, v)| (k, (Rc::new(v), true))).collect(),
            |pairs| pairs.into_iter().map(|(k,v)| (k, (Rc::new(v), true))).collect()
        );

        let fds = match cfg.fds {
            Some(fds) => fds.into_iter().map(|(fd, fdes, perm)| (fd, (fdes, perm))).collect(),
            None => {
                let (stdin, stdout, stderr) = try!(dup_stdio());

                let mut fds = HashMap::with_capacity(3);
                fds.insert(STDIN_FILENO,  (Rc::new(stdin),  Permissions::Read));
                fds.insert(STDOUT_FILENO, (Rc::new(stdout), Permissions::Write));
                fds.insert(STDERR_FILENO, (Rc::new(stderr), Permissions::Write));
                fds
            },
        };

        Ok(Env {
            shell_name: Cow::Owned(Rc::new(String::from(name))),
            args: Cow::Owned(args),
            functions: Cow::Owned(HashMap::new()),
            vars: Cow::Owned(vars),
            fds: Cow::Owned(fds),
            last_status: EXIT_SUCCESS,
            interactive: cfg.interactive,
        })
    }
}

/// An interface for shell commands to use for querying or updating the environment in which they run.
pub trait Environment {
    /// Create a new sub-environment, which starts out idential to its parent,
    /// but any changes on the new environment must not be reflected on the parent.
    fn sub_env(&self) -> Self;
    /// Get the name of the shell or the current function that is executing.
    fn name(&self) -> &Rc<String>;
    /// Get the value of some variable. The values of both shell-only
    /// and environment variables will be looked up and returned.
    fn var(&self, name: &str) -> Option<&Rc<String>>;
    /// Set the value of some variable (including environment variables).
    fn set_var(&mut self, name: String, val: Rc<String>);
    /// Unset the value of some variable (including environment variables).
    fn unset_var(&mut self, name: &str);
    /// Indicates if a function is currently defined with a given name.
    fn has_function(&mut self, fn_name: &str) -> bool;
    /// Attempt to execute a function with a set of arguments if it has been defined.
    fn run_function(&mut self, fn_name: &str, args: Vec<Rc<String>>) -> Option<Result<ExitStatus>>;
    /// Define a function with some `Run`able body.
    fn set_function(&mut self, name: String, func: Rc<Run<Self>>);
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
    /// Reports any `Error` as appropriate, e.g. print to stderr.
    fn report_error(&mut self, err: &error::Error) {
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
    fn sub_env(&self) -> Self {
        self.clone()
    }

    fn name(&self) -> &Rc<String> {
        &self.shell_name
    }

    fn var(&self, name: &str) -> Option<&Rc<String>> {
        self.vars.get(name).map(|&(ref rc, _)| rc)
    }

    fn set_var(&mut self, name: String, val: Rc<String>) {
        if self.var(&name) != Some(&val) {
            self.vars.to_mut().insert(name, (val, false));
        }
    }

    fn unset_var(&mut self, name: &str) {
        if self.vars.contains_key(name) {
            self.vars.to_mut().remove(name);
        }
    }

    fn has_function(&mut self, fn_name: &str) -> bool {
        self.functions.contains_key(fn_name)
    }

    fn run_function(&mut self, fn_name: &str, args: Vec<Rc<String>>)
        -> Option<Result<ExitStatus>>
    {
        use std::mem;

        let mut args = Cow::Owned(args);
        self.functions.get(fn_name)
            .cloned() // Clone the Rc to release the borrow of `self`
            .map(|func| {
                mem::swap(&mut self.args, &mut args);
                let ret = func.run(self);
                mem::swap(&mut self.args, &mut args);
                ret
            })
    }

    fn set_function(&mut self, name: String, func: Rc<Run<Self>>) {
        self.functions.to_mut().insert(name, func);
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
        let ret: Vec<_> = self.vars.iter()
            .filter_map(|(k, &(ref v, exported))| if exported {
                Some((&**k, &***v))
            } else {
                None
            })
            .collect();

        Cow::Owned(ret)
    }

    fn file_desc(&self, fd: Fd) -> Option<(&Rc<FileDesc>, Permissions)> {
        self.fds.get(&fd).map(|&(ref rc, perms)| (rc, perms))
    }

    fn set_file_desc(&mut self, fd: Fd, fdes: Rc<FileDesc>, perms: Permissions) {
        if Some((&fdes, perms)) != self.file_desc(fd) {
            self.fds.to_mut().insert(fd, (fdes, perms));
        }
    }

    fn close_file_desc(&mut self, fd: Fd) {
        if let Some(_) = self.file_desc(fd) {
            self.fds.to_mut().remove(&fd);
        }
    }

    fn is_interactive(&self) -> bool {
        self.interactive
    }
}

#[cfg(test)]
mod tests {
    extern crate tempdir;

    use runtime::{EXIT_ERROR, EXIT_SUCCESS, STDIN_FILENO, STDOUT_FILENO, STDERR_FILENO};
    use runtime::{ExitStatus, ExpansionError, Result, Run, RuntimeError};
    use runtime::io::{Permissions, Pipe};
    use runtime::tests::{dev_null, word};
    use runtime::tests::MockFn;

    use self::tempdir::TempDir;

    use std::io::{Read, Write};
    use std::path::PathBuf;
    use std::rc::Rc;
    use std::thread;

    use super::*;
    use syntax::ast::{Redirect, SimpleCommand};

    struct MockFnRecursive<F> {
        callback: F,
    }

    impl<F> MockFnRecursive<F>
    {
        fn new<E>(f: F) -> Rc<Self>
            where E: Environment,
                  F: Fn(&mut E) -> Result<ExitStatus>,
        {
            Rc::new(MockFnRecursive { callback: f })
        }
    }

    impl<'a, E, F> Run<E> for MockFnRecursive<F>
        where E: Environment,
              F: Fn(&mut E) -> Result<ExitStatus>,
    {
        fn run(&self, env: &mut E) -> Result<ExitStatus> {
            (self.callback)(env)
        }
    }

    #[test]
    fn test_env_name() {
        let name = "shell";
        let env = Env::with_config(EnvConfig {
            name: Some(String::from(name)),
            .. Default::default()
        }).unwrap();
        assert_eq!(&**env.name(), name);
        assert_eq!(&**env.arg(0).unwrap(), name);
    }

    #[test]
    fn test_env_name_should_be_same_in_child_environment() {
        let name = "shell";
        let env = Env::with_config(EnvConfig {
            name: Some(String::from(name)),
            .. Default::default()
        }).unwrap();
        let child = env.sub_env();
        assert_eq!(&**child.name(), name);
        assert_eq!(&**child.arg(0).unwrap(), name);
    }

    #[test]
    fn test_env_set_get_unset_var() {
        let name = "var";
        let value = "value";
        let mut env = Env::new().unwrap();
        assert_eq!(env.var(&name), None);
        env.set_var(name.to_owned(), Rc::new(value.to_owned()));
        assert_eq!(&**env.var(&name).unwrap(), value);
        env.unset_var(name);
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
        let fn_name = "foo";

        let exit = EXIT_ERROR;
        let mut env = Env::new().unwrap();
        assert_eq!(env.has_function(&fn_name), false);
        assert!(env.run_function(&fn_name, vec!()).is_none());

        env.set_function(fn_name.to_owned().into(), MockFn::new(move |_| Ok(exit)));
        assert_eq!(env.has_function(&fn_name), true);
        assert_eq!(env.run_function(&fn_name, vec!()), Some(Ok(exit)));
    }

    #[test]
    fn test_env_set_function_in_parent_visible_in_child() {
        let fn_name = "foo";
        let exit = EXIT_ERROR;
        let mut parent = Env::new().unwrap();
        parent.set_function(fn_name.to_owned(), MockFn::new(move |_| Ok(exit)));

        {
            let mut child = parent.sub_env();
            assert_eq!(child.has_function(&fn_name), true);
            assert_eq!(child.run_function(&fn_name, vec!()), Some(Ok(exit)));
        }
    }

    #[test]
    fn test_env_set_function_in_child_should_not_affect_parent() {
        let fn_name = "foo";
        let exit = EXIT_ERROR;
        let mut parent = Env::new().unwrap();

        {
            let mut child = parent.sub_env();
            child.set_function(fn_name.to_owned(), MockFn::new(move |_| Ok(exit)));
            assert_eq!(child.has_function(&fn_name), true);
            assert_eq!(child.run_function(&fn_name.clone(), vec!()), Some(Ok(exit)));
        }

        assert_eq!(parent.has_function(&fn_name), false);
        assert!(parent.run_function(&fn_name, vec!()).is_none());
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

        let mut env = Env::with_config(EnvConfig {
            name: Some(shell_name_owned),
            args: Some(parent_args.clone()),
            .. Default::default()
        }).unwrap();

        let fn_name = "fn name";
        let args = vec!(
            Rc::new(String::from("child arg1")),
            Rc::new(String::from("child arg2")),
            Rc::new(String::from("child arg3")),
        );

        {
            let args = args.clone();
            let shell_name = shell_name.clone();
            env.set_function(fn_name.to_owned(), MockFn::new::<Env>(move |env| {
                assert_eq!(env.args(), &*args);
                assert_eq!(env.args_len(), args.len());
                assert_eq!(env.name(), &shell_name);
                assert_eq!(env.arg(0), Some(&shell_name));

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
        let fn_name = "fn name";
        let mut env = Env::new().unwrap();
        {
            let num_calls = 3usize;
            let depth = ::std::cell::Cell::new(num_calls);

            env.set_function(fn_name.to_owned(), MockFnRecursive::new::<Env>(move |env| {
                let num_calls = depth.get().saturating_sub(1);
                env.set_var(format!("var{}", num_calls), Rc::new(num_calls.to_string()));

                if num_calls == 0 {
                    Ok(EXIT_SUCCESS)
                } else {
                    depth.set(num_calls);
                    env.run_function(fn_name, vec!()).unwrap()
                }
            }));
        }

        assert_eq!(env.var("var0"), None);
        assert_eq!(env.var("var1"), None);
        assert_eq!(env.var("var2"), None);

        assert!(env.run_function(&fn_name, vec!()).unwrap().unwrap().success());

        assert_eq!(&**env.var("var0").unwrap(), "0");
        assert_eq!(&**env.var("var1").unwrap(), "1");
        assert_eq!(&**env.var("var2").unwrap(), "2");
    }

    #[test]
    fn test_env_run_function_nested_calls_do_not_destroy_upper_args() {
        let fn_name = "fn name";
        let mut env = Env::new().unwrap();
        {
            let num_calls = 3usize;
            let depth = ::std::cell::Cell::new(num_calls);

            env.set_function(fn_name.to_owned(), MockFnRecursive::new::<Env>(move |env| {
                let num_calls = depth.get().saturating_sub(1);

                if num_calls == 0 {
                    Ok(EXIT_SUCCESS)
                } else {
                    depth.set(num_calls);
                    let cur_args: Vec<_> = env.args().iter().cloned().collect();

                    let mut next_args = cur_args.clone();
                    next_args.reverse();
                    next_args.push(Rc::new(format!("arg{}", num_calls)));

                    let ret = env.run_function(fn_name, next_args).unwrap();
                    assert_eq!(&*cur_args, &*env.args());
                    ret
                }
            }));
        }

        assert!(env.run_function(&fn_name, vec!(
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
        env.set_function(fn_name.to_owned(), MockFn::new::<Env>(|env| {
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
        let env = Env::with_config(EnvConfig {
            env: Some(owned_vars),
            .. Default::default()
        }).unwrap();

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
        let file_desc = Rc::new(dev_null());

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
        let file_desc = Rc::new(dev_null());

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
            let file_desc = Rc::new(dev_null());
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
        let file_desc = Rc::new(dev_null());

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
        let Pipe { mut reader, writer } = Pipe::new().unwrap();

        let guard = thread::spawn(move || {
            let mut env = Env::new().unwrap();
            let writer = Rc::new(writer);
            env.set_file_desc(STDERR_FILENO, writer.clone(), Permissions::Write);
            env.report_error(&RuntimeError::Expansion(ExpansionError::DivideByZero));
            env.close_file_desc(STDERR_FILENO);
            let mut writer = Rc::try_unwrap(writer).unwrap();
            writer.flush().unwrap();
            drop(writer);
        });

        let mut msg = String::new();
        reader.read_to_string(&mut msg).unwrap();
        guard.join().unwrap();
        let expected_msg = format!("{}", RuntimeError::Expansion(ExpansionError::DivideByZero));
        assert!(msg.contains(&expected_msg));
    }
}
