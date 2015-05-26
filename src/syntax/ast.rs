//! Defines abstract representations of the shell source.

/// Represents whitespace delimited text.
#[derive(PartialEq, Eq, Debug)]
pub enum Word {
    /// A non-special literal word, or single quoted string.
    Literal(String),
    /// Concat of several distinct words concatenated together.
    Concat(Vec<Word>),
    /// List of words concatenated within double quotes.
    DoubleQuoted(Vec<Word>),

}

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

    /// The simplest possible command: an executable with arguments.
    Simple {
        /// Name or path of the executable.
        cmd: Word,
        /// Arguments supplied to the executable.
        args: Vec<Word>,
    },
}
