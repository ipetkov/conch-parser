//! Defines abstract representations of the shell source.
use std::fmt::{Display, Formatter, Result};

pub mod builder;
pub use syntax::ast::builder::{Builder, CommandBuilder};

/// Represents reading a parameter (or variable) value, e.g. `$foo`.
#[derive(Debug, PartialEq, Eq, Clone)]
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
    /// $0, $1, ..., $9, ${100}
    Positional(u32),
    /// $foo
    Var(String),
}

/// Represents whitespace delimited text.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Word {
    /// A non-special literal word.
    Literal(String),
    /// Several distinct words concatenated together.
    Concat(Vec<Word>),
    /// List of words concatenated within single quotes. Virtually
    /// identical to `Literal`, but makes the distinction if needed.
    SingleQuoted(String),
    /// List of words concatenated within double quotes.
    DoubleQuoted(Vec<Word>),
    /// Access of a value inside a parameter, e.g. `$foo` or `$$`.
    Param(Parameter),
    /// Represents `*`, useful for handling pattern expansions.
    Star,
    /// Represents `?`, useful for handling pattern expansions.
    Question,
    /// Represents `~`, useful for handling tilde expansions.
    Tilde,
}

/// Represents redirecting a command's file descriptors.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Redirect {
    /// Open a file for reading, e.g. [n]< file
    Read(Option<Word>, Word),
    /// Open a file for writing after truncating, e.g. [n]> file
    Write(Option<Word>, Word),
    /// Open a file for reading and writing, e.g. [n]<> file
    ReadWrite(Option<Word>, Word),
    /// Open a file for writing, appending to the end, e.g. [n]>> file
    Append(Option<Word>, Word),
    /// Open a file for writing, failing if the `noclobber` shell option is set, e.g.[n]>| file
    Clobber(Option<Word>, Word),

    /// Duplicate a file descriptor for reading, e.g. [n]<& n
    DupRead(Option<Word>, Word),
    /// Duplicate a file descriptor for writing, e.g. [n]>& n
    DupWrite(Option<Word>, Word),

    /// Close a file descriptor for reading, e.g. [n]<&-
    CloseRead(Option<Word>),
    /// Close a file descriptor for writing, e.g. [n]>&-
    CloseWrite(Option<Word>),
}

/// Represents a parsed newline, more specifically, the presense of a comment
/// immediately preceeding the newline.
///
/// Since shell comments are usually treated as a newline, they can be present
/// anywhere a newline can be as well. Thus if it is desired to retain comments
/// they can be optionally attached to a parsed newline.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Newline(pub Option<String>);

/// Represents any valid shell command.
#[derive(Debug, PartialEq, Eq, Clone)]
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
    /// A function declaration, associating a name with a group of commands,
    /// e.g. `function foo() { echo foo function; }`.
    Function(String, Box<Command>),
    /// The simplest possible command: an executable with arguments,
    /// environment variable assignments, and redirections.
    Simple(Box<SimpleCommand>),
}

/// A class of commands where redirection is applied to a command group.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CompoundCommand {
    /// A group of commands that should be executed in the current environment.
    Brace(Vec<Command>),
    /// A group of commands that should be executed in a subshell environment.
    Subshell(Vec<Command>),
    /// A command that executes its body as long as its guard exits successfully.
    ///
    /// Variant structure: `While(guard, body)`.
    While(Vec<Command>, Vec<Command>),
    /// A command that executes its body as until as its guard exits unsuccessfully.
    ///
    /// Variant structure: `Until(guard, body)`.
    Until(Vec<Command>, Vec<Command>),
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
    /// A command that behaves much like a `match` statment in Rust, running
    /// a branch of commands if a specified word matches another literal or
    /// glob pattern.
    ///
    /// Variant structure: `Case( to_match, (pattern_alternative+, commands*)* )`
    Case(Word, Vec<(Vec<Word>, Vec<Command>)>),
}

/// The simplest possible command: an executable with arguments,
/// environment variable assignments, and redirections.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SimpleCommand {
    /// Name or path of the executable. It's possible to have to have a
    /// command that is only an assigment which would set a value in the
    /// global environment, making the executable optional.
    pub cmd: Option<Word>,
    /// Arguments supplied to the executable.
    pub args: Vec<Word>,
    /// Environment variable assignments for this command, bound as
    /// tuples of (var name, value).
    pub vars: Vec<(String, Option<Word>)>,
    /// All redirections that should be applied before running the command.
    pub io: Vec<Redirect>,
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

impl Display for Word {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        use self::Word::*;

        match *self {
            Star           => fmt.write_str("*"),
            Question       => fmt.write_str("?"),
            Tilde          => fmt.write_str("~"),
            Literal(ref s) => fmt.write_str(s),

            Param(ref p)        => write!(fmt, "{}", p),
            SingleQuoted(ref w) => write!(fmt, "'{}'", w),

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
