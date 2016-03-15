//! This module defines an Environment trait to store state between command executions.

use std::borrow::Cow;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::convert::From;
use std::error;
use std::io::{Result as IoResult, Write};
use std::iter::{IntoIterator, Iterator};
use std::rc::Rc;
use std::result;

use runtime::{EXIT_SUCCESS, STDIN_FILENO, STDOUT_FILENO, STDERR_FILENO};
use runtime::{ExitStatus, Fd, Result, Run};
use runtime::io::{dup_stdio, FileDesc, Permissions};
use void::Void;

/// A shell environment containing any relevant variable, file descriptor, and other information.
#[allow(missing_debug_implementations)]
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
    /// If the shell is running in interactive mode
    interactive: bool,
}

impl<'a> Env<'a> {
    /// Creates a new default environment.
    /// See the docs for `Env::with_config` for more information.
    pub fn new() -> IoResult<Self> {
        Self::with_config(false, None, None, None, None)
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
    pub fn with_config(interactive: bool,
                       name: Option<String>,
                       args: Option<Vec<String>>,
                       env: Option<Vec<(String, String)>>,
                       fds: Option<Vec<(Fd, Rc<FileDesc>, Permissions)>>) -> IoResult<Self>
    {
        use std::env;

        let name = name.unwrap_or_else(|| env::current_exe().ok().and_then(|path| {
            path.file_name().and_then(|os_str| os_str.to_str().map(|s| s.to_string()))
        }).unwrap_or_default());

        let args = args.map_or(Vec::new(), |args| args.into_iter().map(Rc::new).collect());

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
            interactive: interactive,
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
    fn sub_env<'b>(&'b self) -> Box<Environment + 'b> {
        Box::new(Env {
            shell_name: self.shell_name.clone(),
            args: self.args.clone(),

            functions: HashMap::new(),
            vars: HashMap::new(),
            fds: HashMap::new(),
            last_status: self.last_status,
            parent_env: Some(self),
            interactive: self.interactive,
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

        let ret: Vec<_> = env.into_iter().filter_map(|(k, v)| match *v {
            Some((ref v, true)) => Some((k, &***v)),
            Some((_, false)) => None,
            None => None,
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
        self.interactive
    }
}

#[cfg(test)]
mod tests {
    extern crate tempdir;

    use runtime::{EXIT_ERROR, EXIT_SUCCESS, STDIN_FILENO, STDOUT_FILENO, STDERR_FILENO};
    use runtime::{ExitStatus, ExpansionError, Result, Run, RuntimeError};
    use runtime::io::{Permissions, Pipe};
    use runtime::tests::{file_desc, word};
    use runtime::tests::MockFn;

    use self::tempdir::TempDir;

    use std::io::{Read, Write};
    use std::path::PathBuf;
    use std::rc::Rc;
    use std::thread;

    use super::*;
    use syntax::ast::{Redirect, SimpleCommand};

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


    #[test]
    fn test_env_name() {
        let name = "shell";
        let env = Env::with_config(false, Some(String::from(name)), None, None, None).unwrap();
        assert_eq!(&**env.name(), name);
        assert_eq!(&**env.arg(0).unwrap(), name);
    }

    #[test]
    fn test_env_name_should_be_same_in_child_environment() {
        let name = "shell";
        let env = Env::with_config(false, Some(String::from(name)), None, None, None).unwrap();
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

        let mut env = Env::with_config(false, Some(shell_name_owned), Some(parent_args.clone()), None, None).unwrap();

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
        let env = Env::with_config(false, None, None, Some(owned_vars), None).unwrap();
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
