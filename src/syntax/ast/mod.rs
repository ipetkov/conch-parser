//! Defines abstract representations of the shell source.

pub mod builder;
pub use syntax::ast::builder::Builder;

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

/// A parameter substitution, e.g. `${param-word}`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParameterSubstitution {
    /// Returns the standard output of running a command, e.g. `$(cmd)`
    Command(Vec<Command>),
    /// Returns the length of the value of a parameter, e.g. `${#param}`
    Len(Parameter),
    /// Use a provided value if the parameter is null or unset, e.g.
    /// `${param:-[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Default(bool, Parameter, Option<Box<Word>>),
    /// Assign a provided value to the parameter if it is null or unset,
    /// e.g. `${param:=[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Assign(bool, Parameter, Option<Box<Word>>),
    /// If the parameter is null or unset, an error should result with the provided
    /// message, e.g. `${param:?[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Error(bool, Parameter, Option<Box<Word>>),
    /// If the parameter is NOT null or unset, a provided word will be used,
    /// e.g. `${param:+[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Alternative(bool, Parameter, Option<Box<Word>>),
    /// Remove smallest suffix pattern from a parameter's value, e.g. `${param%pattern}`
    RemoveSmallestSuffix(Parameter, Option<Box<Word>>),
    /// Remove largest suffix pattern from a parameter's value, e.g. `${param%%pattern}`
    RemoveLargestSuffix(Parameter, Option<Box<Word>>),
    /// Remove smallest prefix pattern from a parameter's value, e.g. `${param#pattern}`
    RemoveSmallestPrefix(Parameter, Option<Box<Word>>),
    /// Remove largest prefix pattern from a parameter's value, e.g. `${param##pattern}`
    RemoveLargestPrefix(Parameter, Option<Box<Word>>),
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
    /// A parameter substitution, e.g. `${param-word}`.
    Subst(Box<ParameterSubstitution>),
    /// A token which normally has a special meaning is treated as a literal
    /// because it was escaped, typically with a backslash, e.g. `\"`.
    Escaped(String),
    /// Represents `*`, useful for handling pattern expansions.
    Star,
    /// Represents `?`, useful for handling pattern expansions.
    Question,
    /// Represents `[`, useful for handling pattern expansions.
    SquareOpen,
    /// Represents `]`, useful for handling pattern expansions.
    SquareClose,
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
    /// Lines contained in the source that should be provided by as input to a file descriptor.
    Heredoc(Option<Word>, Word),

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
