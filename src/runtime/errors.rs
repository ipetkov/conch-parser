use std::cmp::{Eq, PartialEq};
use std::convert::From;
use std::error::Error;
use std::fmt::{Display, Formatter, Result};
use std::io::Error as IoError;
use std::io::Write;
use super::Fd;
use syntax::ast::Parameter;
use runtime::io::Permissions;

/// An error which may arise during parameter expansion.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ExpansionError {
    /// Attempted to divide by zero in an arithmetic subsitution.
    DivideByZero,
    /// Attempted to raise to a negative power in an arithmetic subsitution.
    NegativeExponent,
    /// Attempted to assign a special parameter, e.g. `${!:-value}`.
    BadAssig(Parameter),
    /// Attempted to evaluate a null or unset parameter, i.e. `${var:?msg}`.
    EmptyParameter(Parameter, String),
}

impl Error for ExpansionError {
    fn description(&self) -> &str {
        match *self {
            ExpansionError::DivideByZero       => "attempted to divide by zero",
            ExpansionError::NegativeExponent   => "attempted to raise to a negative power",
            ExpansionError::BadAssig(_)        => "attempted to assign a special parameter",
            ExpansionError::EmptyParameter(..) => "attempted to evaluate a null or unset parameter",
        }
    }
}

impl Display for ExpansionError {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        match *self {
            ExpansionError::DivideByZero                   => write!(fmt, "{}", self.description()),
            ExpansionError::NegativeExponent               => write!(fmt, "{}", self.description()),
            ExpansionError::BadAssig(ref p)                => write!(fmt, "{}: cannot assign in this way", p),
            ExpansionError::EmptyParameter(ref p, ref msg) => write!(fmt, "{}: {}", p, msg),
        }
    }
}

/// An error which may arise during redirection.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum RedirectionError {
    /// A redirect path evaluated to multiple fields.
    Ambiguous(Vec<String>),
    /// Attempted to duplicate an invalid file descriptor.
    BadFdSrc(String),
    /// Attempted to duplicate a file descriptor with Read/Write
    /// access that differs from the original.
    BadFdPerms(Fd, Permissions /* new perms */),
}

impl Error for RedirectionError {
    fn description(&self) -> &str {
        match *self {
            RedirectionError::Ambiguous(_)   => "a redirect path evaluated to multiple fields",
            RedirectionError::BadFdSrc(_)    => "attempted to duplicate an invalid file descriptor",
            RedirectionError::BadFdPerms(..) =>
                "attmpted to duplicate a file descritpr with Read/Write access that differs from the original",
        }
    }
}

impl Display for RedirectionError {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        match *self {
            RedirectionError::Ambiguous(ref v) => {
                try!(write!(fmt, "{}: ", self.description()));
                let mut iter = v.iter();
                if let Some(s) = iter.next() { try!(write!(fmt, "{}", s)); }
                for s in iter { try!(write!(fmt, " {}", s)); }
                Ok(())
            },

            RedirectionError::BadFdSrc(ref fd) => write!(fmt, "{}: {}", self.description(), fd),
            RedirectionError::BadFdPerms(fd, perms) =>
                write!(fmt, "{}: {}, desired permissions: {}", self.description(), fd, perms),
        }
    }
}

/// An error which may arise when spawning a command process.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum CommandError {
    /// Unable to find a command/function/builtin to execute.
    NotFound(String),
    /// Utility or script does not have executable permissions.
    NotExecutable(String),
}

impl Error for CommandError {
    fn description(&self) -> &str {
        match *self {
            CommandError::NotFound(_)      => "command not found",
            CommandError::NotExecutable(_) => "command not executable",
        }
    }
}

impl Display for CommandError {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        match *self {
            CommandError::NotFound(ref c)      |
            CommandError::NotExecutable(ref c) => write!(fmt, "{}: {}", c, self.description()),
        }
    }
}

/// An error which may arise while executing commands.
#[derive(Debug)]
pub enum RuntimeError {
    /// Any I/O error returned by the OS during execution and the file that caused the error.
    Io(IoError, String),
    /// Any error that occured during a parameter expansion.
    Expansion(ExpansionError),
    /// Any error that occured during a redirection.
    Redirection(RedirectionError),
    /// Any error that occured during a command spawning.
    Command(CommandError),
    /// Runtime feature not currently supported.
    Unimplemented(&'static str),
    /// Any external error.
    Custom(Box<Error + Send + Sync>),
}

// IoErrors and other extension errors may not implement Eq/PartialEq, but
// equality checking is invaluable for testing, so we'll compromise and implement
// some equality checking for testing.
#[cfg(test)] impl Eq for RuntimeError {}
#[cfg(test)] impl PartialEq for RuntimeError {
    fn eq(&self, other: &Self) -> bool {
        use self::RuntimeError::*;

        match (self, other) {
            (&Io(ref e1, ref a),    &Io(ref e2, ref b))    => e1.kind() == e2.kind() && a == b,
            (&Expansion(ref a),     &Expansion(ref b))     => a == b,
            (&Redirection(ref a),   &Redirection(ref b))   => a == b,
            (&Command(ref a),       &Command(ref b))       => a == b,
            (&Unimplemented(ref a), &Unimplemented(ref b)) => a == b,
            (&Custom(ref a),        &Custom(ref b))        => {
                let a: *const _ = &**a;
                let b: *const _ = &**b;
                a == b
            },

            _ => false,
        }
    }
}

impl Error for RuntimeError {
    fn description(&self) -> &str {
        match *self {
            RuntimeError::Io(ref e, _)       => e.description(),
            RuntimeError::Expansion(ref e)   => e.description(),
            RuntimeError::Redirection(ref e) => e.description(),
            RuntimeError::Command(ref e)     => e.description(),
            RuntimeError::Custom(ref e)      => e.description(),
            RuntimeError::Unimplemented(s)   => s,
        }
    }

    fn cause(&self) -> Option<&Error> {
        match *self {
            RuntimeError::Io(ref e, _)       => Some(e),
            RuntimeError::Expansion(ref e)   => Some(e),
            RuntimeError::Redirection(ref e) => Some(e),
            RuntimeError::Command(ref e)     => Some(e),
            RuntimeError::Custom(ref e)      => e.cause(),
            RuntimeError::Unimplemented(_)   => None,
        }
    }
}

impl Display for RuntimeError {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        match *self {
            RuntimeError::Expansion(ref e)    => e.fmt(fmt),
            RuntimeError::Redirection(ref e)  => e.fmt(fmt),
            RuntimeError::Command(ref e)      => e.fmt(fmt),
            RuntimeError::Custom(ref e)       => e.fmt(fmt),
            RuntimeError::Io(ref e, ref path) => write!(fmt, "{}: {}", e, path),
            RuntimeError::Unimplemented(e)    => write!(fmt, "{}", e),
        }
    }
}

impl From<ExpansionError> for RuntimeError {
    fn from(err: ExpansionError) -> Self {
        RuntimeError::Expansion(err)
    }
}

impl From<RedirectionError> for RuntimeError {
    fn from(err: RedirectionError) -> Self {
        RuntimeError::Redirection(err)
    }
}

impl From<CommandError> for RuntimeError {
    fn from(err: CommandError) -> Self {
        RuntimeError::Command(err)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ensure_runtime_errors_are_send_and_sync() {
        fn send_and_sync<T: Send + Sync>() {}

        send_and_sync::<ExpansionError>();
        send_and_sync::<RedirectionError>();
        send_and_sync::<CommandError>();
        send_and_sync::<RuntimeError>();
    }
}
