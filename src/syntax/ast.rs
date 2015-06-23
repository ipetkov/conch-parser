//! Defines abstract representations of the shell source.
use std::fmt::{Display, Formatter, Result};

/// Represents reading a parameter (or variable) value, e.g. `$foo`.
#[derive(PartialEq, Eq, Debug)]
pub enum Parameter {
    /// $@
    At,
    /// $*
    Star,
    /// $#
    Pound,
    /// $?
    Question,
    /// $-
    Dash,
    /// $$
    Dollar,
    /// $!
    Bang,
    /// $0, $1, ..., $9
    Positional(u8),
    /// $foo
    Var(String),
}

impl Display for Parameter {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        use self::Parameter::*;

        match *self {
            At       => fmt.write_str("$@"),
            Star     => fmt.write_str("$*"),
            Pound    => fmt.write_str("$#"),
            Question => fmt.write_str("$?"),
            Dash     => fmt.write_str("$-"),
            Dollar   => fmt.write_str("$$"),
            Bang     => fmt.write_str("$!"),

            Var(ref p)    => write!(fmt, "${}", p),
            Positional(p) => write!(fmt, "${}", p),
        }
    }
}

/// Represents whitespace delimited text.
#[derive(PartialEq, Eq, Debug)]
pub enum Word {
    /// A non-special literal word, or single quoted string.
    Literal(String),
    /// Concat of several distinct words concatenated together.
    Concat(Vec<Word>),
    /// List of words concatenated within double quotes.
    DoubleQuoted(Vec<Word>),
    /// Access of a value inside a parameter, e.g. `$foo` or `$$`.
    Param(Parameter),

}

impl Display for Word {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        use self::Word::*;

        match *self {
            Literal(ref s) => fmt.write_str(s),
            Param(ref p) => write!(fmt, "{}", p),

            DoubleQuoted(ref words) => {
                try!(fmt.write_str("\""));
                for w in words { try!(write!(fmt, "{}", w)); }
                fmt.write_str("\"")
            },

            Concat(ref words) => {
                for w in words {
                    try!(write!(fmt, "{}", w));
                }

                Ok(())
            },
        }
    }
}

/// Represents redirecting a command's file descriptors.
#[derive(PartialEq, Eq, Debug)]
pub enum Redirect {
    /// Open a file for reading, e.g. [n]< file
    Read(Option<u32>, Word),
    /// Open a file for writing after truncating, e.g. [n]> file
    Write(Option<u32>, Word),
    /// Open a file for reading and writing, e.g. [n]<> file
    ReadWrite(Option<u32>, Word),
    /// Open a file for writing, appending to the end, e.g. [n]>> file
    Append(Option<u32>, Word),
    /// Open a file for writing, failing if the `noclobber` shell option is set, e.g.[n]>| file
    Clobber(Option<u32>, Word),

    /// Duplicate a file descriptor for reading, e.g. [n]<& n
    DupRead(Option<u32>, u32),
    /// Duplicate a file descriptor for writing, e.g. [n]>& n
    DupWrite(Option<u32>, u32),

    /// Close a file descriptor for reading, e.g. [n]<&-
    CloseRead(Option<u32>),
    /// Close a file descriptor for writing, e.g. [n]>&-
    CloseWrite(Option<u32>),
}

/// Represents a parsed newline, more specifically, the presense of a comment
/// immediately preceeding the newline.
///
/// Since shell comments are usually treated as a newline, they can be present
/// anywhere a newline can be as well. Thus if it is desired to retain comments
/// they can be optionally attached to a parsed newline.
#[derive(PartialEq, Eq, Debug)]
pub struct Newline(pub Option<String>);

/// Represents any valid shell command.
#[derive(PartialEq, Eq, Debug)]
pub enum Command {
    /// A compound command which runs the second if the first succeeds,
    /// e.g. `foo && bar`.
    And(Box<Command>, Box<Command>),
    /// A compound command which runs the second if the first fails,
    /// e.g. `foo || bar`.
    Or(Box<Command>, Box<Command>),
    /// A chain of concurrent commands where the standard output of the
    /// previous becomes the standard input of the next, e.g.
    /// `[!] foo | bar | baz`.
    ///
    /// The bool indicates if a logical negation of the last command's status
    /// should be returned.
    Pipe(bool, Vec<Command>),
    /// A command that runs asynchronously, that is, the shell will not wait
    /// for it to exit before running the next command, e.g. `foo &`.
    Job(Box<Command>),
    /// A class of commands where redirection is applied to a command group.
    Compound(Box<CompoundCommand>, Vec<Redirect>),
    /// The simplest possible command: an executable with arguments,
    /// environment variable assignments, and redirections.
    Simple(Box<SimpleCommand>),
}

/// A class of commands where redirection is applied to a command group.
#[derive(PartialEq, Eq, Debug)]
pub enum CompoundCommand {
    /// A group of commands that should be executed in the current environment.
    Brace(Vec<Command>),
    /// A group of commands that should be executed in a subshell environment.
    Subshell(Vec<Command>),
    /// A command that represents a `while` or `until` loop, executing a body
    /// of commands based on the exit status of another command (the guard).
    ///
    /// The bool indicates an `until` loop, that is, execute the loop until the guard
    /// returns successfully, otherwise, loop while the guard exits successfully.
    /// Variant structure: `Loop(is_until, guard, body)`.
    Loop(bool, Vec<Command>, Vec<Command>),
    /// A conditional command that runs the respective command branch when a
    /// certain of the first condition that exits successfully.
    ///
    /// Variant structure: `If( (guard, branch)+, else_branch )`.
    If(Vec<(Vec<Command>, Vec<Command>)>, Option<Vec<Command>>),
    /// A command that binds a variable to a number of provided words and runs
    /// its body once for each binding.
    ///
    /// Variant structure: `For(var_name, words, body)`.
    For(String, Option<Vec<Word>>, Vec<Command>),
}

/// The simplest possible command: an executable with arguments,
/// environment variable assignments, and redirections.
#[derive(PartialEq, Eq, Debug)]
pub struct SimpleCommand {
    /// Name or path of the executable. It's possible to have to have a
    /// command that is only an assigment which would set a value in the
    /// global environment, making the executable optional.
    pub cmd: Option<Word>,
    /// Arguments supplied to the executable.
    pub args: Vec<Word>,
    /// Environment variable assignments for this command, bound as
    /// tuples of (var name, value).
    pub vars: Vec<(String, Word)>,
    /// All redirections that should be applied before running the command.
    pub io: Vec<Redirect>,
}
