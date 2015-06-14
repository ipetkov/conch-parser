//! Defines abstract representations of the shell source.

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

    /// The simplest possible command: an executable with arguments.
    Simple {
        /// Name or path of the executable.
        cmd: Word,
        /// Arguments supplied to the executable.
        args: Vec<Word>,
    },
}
