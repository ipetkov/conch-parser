//! Defines abstract representations of the shell source.
use std::{fmt, ops};
use std::rc::Rc;

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
/// Generic over the top-level representation of a shell word and command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParameterSubstitution<W, C> {
    /// Returns the standard output of running a command, e.g. `$(cmd)`
    Command(Vec<C>),
    /// Returns the length of the value of a parameter, e.g. `${#param}`
    Len(Parameter),
    /// Returns the resulting value of an arithmetic subsitution, e.g. `$(( x++ ))`
    Arith(Option<Arithmetic>),
    /// Use a provided value if the parameter is null or unset, e.g.
    /// `${param:-[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Default(bool, Parameter, Option<W>),
    /// Assign a provided value to the parameter if it is null or unset,
    /// e.g. `${param:=[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Assign(bool, Parameter, Option<W>),
    /// If the parameter is null or unset, an error should result with the provided
    /// message, e.g. `${param:?[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Error(bool, Parameter, Option<W>),
    /// If the parameter is NOT null or unset, a provided word will be used,
    /// e.g. `${param:+[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Alternative(bool, Parameter, Option<W>),
    /// Remove smallest suffix pattern from a parameter's value, e.g. `${param%pattern}`
    RemoveSmallestSuffix(Parameter, Option<W>),
    /// Remove largest suffix pattern from a parameter's value, e.g. `${param%%pattern}`
    RemoveLargestSuffix(Parameter, Option<W>),
    /// Remove smallest prefix pattern from a parameter's value, e.g. `${param#pattern}`
    RemoveSmallestPrefix(Parameter, Option<W>),
    /// Remove largest prefix pattern from a parameter's value, e.g. `${param##pattern}`
    RemoveLargestPrefix(Parameter, Option<W>),
}

/// A top-level representation of a shell word. This wrapper unifies the provided
/// top-level word representation, `ComplexWord`, and the top-level command
/// representation, `Command`, while allowing them to be generic on their own.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TopLevelWord(pub ComplexWord<TopLevelWord, Command<TopLevelWord>>);

/// Represents whitespace delimited text.
/// Generic over the top-level representation of a shell word and command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ComplexWord<W, C> {
    /// Several distinct words concatenated together.
    Concat(Vec<Word<W, C>>),
    /// A regular word.
    Single(Word<W, C>),
}

/// Represents whitespace delimited text.
/// Generic over the top-level representation of a shell word and command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Word<W, C> {
    /// A regular word.
    Simple(Box<SimpleWord<W, C>>),
    /// List of words concatenated within double quotes.
    DoubleQuoted(Vec<SimpleWord<W, C>>),
    /// List of words concatenated within single quotes. Virtually
    /// identical as a literal, but makes a distinction between the two.
    SingleQuoted(String),
}

/// Represents whitespace delimited text.
/// Generic over the top-level representation of a shell word and command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SimpleWord<W, C> {
    /// A non-special literal word.
    Literal(String),
    /// Access of a value inside a parameter, e.g. `$foo` or `$$`.
    Param(Parameter),
    /// A parameter substitution, e.g. `${param-word}`.
    Subst(Box<ParameterSubstitution<W, C>>),
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
    /// Represents `:`, useful for handling tilde expansions.
    Colon,
}

/// Represents redirecting a command's file descriptors.
/// Generic over the top-level representation of a shell word.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Redirect<W> {
    /// Open a file for reading, e.g. `[n]< file`.
    Read(Option<u16>, W),
    /// Open a file for writing after truncating, e.g. `[n]> file`.
    Write(Option<u16>, W),
    /// Open a file for reading and writing, e.g. `[n]<> file`.
    ReadWrite(Option<u16>, W),
    /// Open a file for writing, appending to the end, e.g. `[n]>> file`.
    Append(Option<u16>, W),
    /// Open a file for writing, failing if the `noclobber` shell option is set, e.g. `[n]>| file`.
    Clobber(Option<u16>, W),
    /// Lines contained in the source that should be provided by as input to a file descriptor.
    Heredoc(Option<u16>, W),
    /// Duplicate a file descriptor for reading, e.g. `[n]<& [n|-]`.
    DupRead(Option<u16>, W),
    /// Duplicate a file descriptor for writing, e.g. `[n]>& [n|-]`.
    DupWrite(Option<u16>, W),
}

/// A grouping of guard and body commands.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct GuardBodyPair<C> {
    /// The guard commands, which if successful, should lead to the
    /// execution of the body commands.
    pub guard: Vec<C>,
    /// The body commands to execute if the guard is successful.
    pub body: Vec<C>,
}

/// Represents any valid shell command.
/// Generic over the top-level representation of a shell word.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Command<W> {
    /// A compound command which runs the second if the first succeeds,
    /// e.g. `foo && bar`.
    And(Box<Command<W>>, Box<Command<W>>),
    /// A compound command which runs the second if the first fails,
    /// e.g. `foo || bar`.
    Or(Box<Command<W>>, Box<Command<W>>),
    /// A chain of concurrent commands where the standard output of the
    /// previous becomes the standard input of the next, e.g.
    /// `[!] foo | bar | baz`.
    ///
    /// The bool indicates if a logical negation of the last command's status
    /// should be returned.
    Pipe(bool, Vec<Command<W>>),
    /// A command that runs asynchronously, that is, the shell will not wait
    /// for it to exit before running the next command, e.g. `foo &`.
    Job(Box<Command<W>>),
    /// A class of commands where redirection is applied to a command group.
    Compound(Box<CompoundCommand<W, Command<W>>>, Vec<Redirect<W>>),
    /// A function declaration, associating a name with a group of commands,
    /// e.g. `function foo() { echo foo function; }`.
    Function(String, Rc<Command<W>>),
    /// The simplest possible command: an executable with arguments,
    /// environment variable assignments, and redirections.
    Simple(Box<SimpleCommand<W>>),
}

/// A class of commands where redirection is applied to a command group.
/// Generic over the top-level representation of a shell word and command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CompoundCommand<W, C> {
    /// A group of commands that should be executed in the current environment.
    Brace(Vec<C>),
    /// A group of commands that should be executed in a subshell environment.
    Subshell(Vec<C>),
    /// A command that executes its body as long as its guard exits successfully.
    While(GuardBodyPair<C>),
    /// A command that executes its body as until as its guard exits unsuccessfully.
    Until(GuardBodyPair<C>),
    /// A conditional command that runs the respective command branch when a
    /// certain of the first condition that exits successfully.
    ///
    /// Variant structure: `If( conditional+, else_branch )`.
    If(Vec<GuardBodyPair<C>>, Option<Vec<C>>),
    /// A command that binds a variable to a number of provided words and runs
    /// its body once for each binding.
    ///
    /// Variant structure: `For(var_name, words, body)`.
    For(String, Option<Vec<W>>, Vec<C>),
    /// A command that behaves much like a `match` statment in Rust, running
    /// a branch of commands if a specified word matches another literal or
    /// glob pattern.
    ///
    /// Variant structure: `Case( to_match, (pattern_alternative+, commands*)* )`
    Case(W, Vec<(Vec<W>, Vec<C>)>),
}

/// The simplest possible command: an executable with arguments,
/// environment variable assignments, and redirections.
/// Generic over the top-level representation of a shell word.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SimpleCommand<W> {
    /// Name or path of the executable along with any arguments. It's possible to
    /// have to have a command that is only an assigment which would set a value
    /// in the global environment, making the executable optional.
    pub cmd: Option<(W, Vec<W>)>,
    /// Environment variable assignments for this command, bound as
    /// tuples of (var name, value).
    pub vars: Vec<(String, Option<W>)>,
    /// All redirections that should be applied before running the command.
    pub io: Vec<Redirect<W>>,
}

/// Represents an expression within an arithmetic subsitution.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Arithmetic {
    /// The value of a variable, e.g. `$var` or `var`.
    Var(String),
    /// A numeric literal such as `42` or `0xdeadbeef`.
    Literal(isize),
    /// `left ** right`.
    Pow(Box<Arithmetic>, Box<Arithmetic>),
    /// Returns the current value of a variable,
    /// and then increments its value immediately after, e.g. `var++`
    PostIncr(String),
    /// Returns the current value of a variable,
    /// and then decrements its value immediately after, e.g. `var--`
    PostDecr(String),
    /// Increments the value of a variable and returns the new value, e.g. `++var`.
    PreIncr(String),
    /// Decrements the value of a variable and returns the new value, e.g. `--var`.
    PreDecr(String),
    /// Ensures the sign of the underlying result is positive, e.g. `+(1-2)`.
    UnaryPlus(Box<Arithmetic>),
    /// Ensures the sign of the underlying result is negative, e.g. `-(1+2)`.
    UnaryMinus(Box<Arithmetic>),
    /// Returns one if the underlying result is zero, or zero otherwise, e.g. `!expr`.
    LogicalNot(Box<Arithmetic>),
    /// Flips all bits from the underlying result, e.g. `~expr`.
    BitwiseNot(Box<Arithmetic>),
    /// `left * right`
    Mult(Box<Arithmetic>, Box<Arithmetic>),
    /// `left / right`
    Div(Box<Arithmetic>, Box<Arithmetic>),
    /// `left % right`
    Modulo(Box<Arithmetic>, Box<Arithmetic>),
    /// `left + right`
    Add(Box<Arithmetic>, Box<Arithmetic>),
    /// `left - right`
    Sub(Box<Arithmetic>, Box<Arithmetic>),
    /// `left << right`
    ShiftLeft(Box<Arithmetic>, Box<Arithmetic>),
    /// `left >> right`
    ShiftRight(Box<Arithmetic>, Box<Arithmetic>),
    /// `left < right`
    Less(Box<Arithmetic>, Box<Arithmetic>),
    /// `left <= right`
    LessEq(Box<Arithmetic>, Box<Arithmetic>),
    /// `left > right`
    Great(Box<Arithmetic>, Box<Arithmetic>),
    /// `left >= right`
    GreatEq(Box<Arithmetic>, Box<Arithmetic>),
    /// `left == right`
    Eq(Box<Arithmetic>, Box<Arithmetic>),
    /// `left != right`
    NotEq(Box<Arithmetic>, Box<Arithmetic>),
    /// `left & right`
    BitwiseAnd(Box<Arithmetic>, Box<Arithmetic>),
    /// `left ^ right`
    BitwiseXor(Box<Arithmetic>, Box<Arithmetic>),
    /// `left | right`
    BitwiseOr(Box<Arithmetic>, Box<Arithmetic>),
    /// `left && right`
    LogicalAnd(Box<Arithmetic>, Box<Arithmetic>),
    /// `left || right`
    LogicalOr(Box<Arithmetic>, Box<Arithmetic>),
    /// `first ? second : third`
    Ternary(Box<Arithmetic>, Box<Arithmetic>, Box<Arithmetic>),
    /// Assigns the value of an underlying expression to a
    /// variable and returns the value, e.g. `x = 5`, or `x += 2`.
    Assign(String, Box<Arithmetic>),
    /// `expr[, expr[, ...]]`
    Sequence(Vec<Arithmetic>),
}

impl ops::Deref for TopLevelWord {
    type Target = ComplexWord<TopLevelWord, Command<TopLevelWord>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ops::DerefMut for TopLevelWord {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl ::std::cmp::PartialEq<ComplexWord<TopLevelWord, Command<TopLevelWord>>> for TopLevelWord {
    fn eq(&self, other: &ComplexWord<TopLevelWord, Command<TopLevelWord>>) -> bool {
        &self.0 == other
    }
}

impl fmt::Display for Parameter {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        use self::Parameter::*;

        match *self {
            At       => fmt.write_str("$@"),
            Star     => fmt.write_str("$*"),
            Pound    => fmt.write_str("$#"),
            Question => fmt.write_str("$?"),
            Dash     => fmt.write_str("$-"),
            Dollar   => fmt.write_str("$$"),
            Bang     => fmt.write_str("$!"),

            Var(ref p)    => write!(fmt, "${{{}}}", p),
            Positional(p) => if p <= 9 {
                write!(fmt, "${}", p)
            } else {
                write!(fmt, "${{{}}}", p)
            },
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_display_parameter() {
        use super::Parameter::*;
        use super::ComplexWord::Single;
        use super::SimpleWord::Param;
        use super::TopLevelWord;
        use super::Word::Simple;
        use syntax::parse::test::make_parser;

        let params = vec!(
            At,
            Star,
            Pound,
            Question,
            Dash,
            Dollar,
            Bang,
            Positional(0),
            Positional(10),
            Positional(100),
            Var(String::from("foo_bar123")),
        );

        for p in params {
            let src = p.to_string();
            let correct = TopLevelWord(Single(Simple(Box::new(Param(p)))));

            let parsed = match make_parser(&src).word() {
                Ok(Some(w)) => w,
                Ok(None) => panic!("The source \"{}\" generated from the command `{:#?}` failed to parse as anything", src, correct),
                Err(e) => panic!("The source \"{}\" generated from the command `{:#?}` failed to parse: {}", src, correct, e),
            };

            if correct != parsed {
                panic!("The source \"{}\" generated from the command `{:#?}` was parsed as `{:#?}`", src, correct, parsed);
            }
        }
    }
}
