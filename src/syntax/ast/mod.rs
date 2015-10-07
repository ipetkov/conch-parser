//! Defines abstract representations of the shell source.
use std::fmt;
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
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParameterSubstitution {
    /// Returns the standard output of running a command, e.g. `$(cmd)`
    Command(Vec<Command>),
    /// Returns the length of the value of a parameter, e.g. `${#param}`
    Len(Parameter),
    /// Returns the resulting value of an arithmetic subsitution, e.g. `$(( x++ ))`
    Arithmetic(Option<Arith>),
    /// Use a provided value if the parameter is null or unset, e.g.
    /// `${param:-[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Default(bool, Parameter, Option<Word>),
    /// Assign a provided value to the parameter if it is null or unset,
    /// e.g. `${param:=[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Assign(bool, Parameter, Option<Word>),
    /// If the parameter is null or unset, an error should result with the provided
    /// message, e.g. `${param:?[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Error(bool, Parameter, Option<Word>),
    /// If the parameter is NOT null or unset, a provided word will be used,
    /// e.g. `${param:+[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Alternative(bool, Parameter, Option<Word>),
    /// Remove smallest suffix pattern from a parameter's value, e.g. `${param%pattern}`
    RemoveSmallestSuffix(Parameter, Option<Word>),
    /// Remove largest suffix pattern from a parameter's value, e.g. `${param%%pattern}`
    RemoveLargestSuffix(Parameter, Option<Word>),
    /// Remove smallest prefix pattern from a parameter's value, e.g. `${param#pattern}`
    RemoveSmallestPrefix(Parameter, Option<Word>),
    /// Remove largest prefix pattern from a parameter's value, e.g. `${param##pattern}`
    RemoveLargestPrefix(Parameter, Option<Word>),
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
    /// Open a file for reading, e.g. `[n]< file`.
    Read(Option<u16>, Word),
    /// Open a file for writing after truncating, e.g. `[n]> file`.
    Write(Option<u16>, Word),
    /// Open a file for reading and writing, e.g. `[n]<> file`.
    ReadWrite(Option<u16>, Word),
    /// Open a file for writing, appending to the end, e.g. `[n]>> file`.
    Append(Option<u16>, Word),
    /// Open a file for writing, failing if the `noclobber` shell option is set, e.g. `[n]>| file`.
    Clobber(Option<u16>, Word),
    /// Lines contained in the source that should be provided by as input to a file descriptor.
    Heredoc(Option<u16>, Word),
    /// Duplicate a file descriptor for reading, e.g. `[n]<& [n|-]`.
    DupRead(Option<u16>, Word),
    /// Duplicate a file descriptor for writing, e.g. `[n]>& [n|-]`.
    DupWrite(Option<u16>, Word),
}

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
    Function(String, Rc<Command>),
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
    /// Name or path of the executable along with any arguments. It's possible to
    /// have to have a command that is only an assigment which would set a value
    /// in the global environment, making the executable optional.
    pub cmd: Option<(Word, Vec<Word>)>,
    /// Environment variable assignments for this command, bound as
    /// tuples of (var name, value).
    pub vars: Vec<(String, Option<Word>)>,
    /// All redirections that should be applied before running the command.
    pub io: Vec<Redirect>,
}

/// Represents an expression within an arithmetic subsitution.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Arith {
    /// The value of a variable, e.g. `$var` or `var`.
    Var(String),
    /// A numeric literal such as `42` or `0xdeadbeef`.
    Literal(isize),
    /// `left ** right`.
    Pow(Box<Arith>, Box<Arith>),
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
    UnaryPlus(Box<Arith>),
    /// Ensures the sign of the underlying result is negative, e.g. `-(1+2)`.
    UnaryMinus(Box<Arith>),
    /// Returns one if the underlying result is zero, or zero otherwise, e.g. `!expr`.
    LogicalNot(Box<Arith>),
    /// Flips all bits from the underlying result, e.g. `~expr`.
    BitwiseNot(Box<Arith>),
    /// `left * right`
    Mult(Box<Arith>, Box<Arith>),
    /// `left / right`
    Div(Box<Arith>, Box<Arith>),
    /// `left % right`
    Modulo(Box<Arith>, Box<Arith>),
    /// `left + right`
    Add(Box<Arith>, Box<Arith>),
    /// `left - right`
    Sub(Box<Arith>, Box<Arith>),
    /// `left << right`
    ShiftLeft(Box<Arith>, Box<Arith>),
    /// `left >> right`
    ShiftRight(Box<Arith>, Box<Arith>),
    /// `left < right`
    Less(Box<Arith>, Box<Arith>),
    /// `left <= right`
    LessEq(Box<Arith>, Box<Arith>),
    /// `left > right`
    Great(Box<Arith>, Box<Arith>),
    /// `left >= right`
    GreatEq(Box<Arith>, Box<Arith>),
    /// `left == right`
    Eq(Box<Arith>, Box<Arith>),
    /// `left != right`
    NotEq(Box<Arith>, Box<Arith>),
    /// `left & right`
    BitwiseAnd(Box<Arith>, Box<Arith>),
    /// `left ^ right`
    BitwiseXor(Box<Arith>, Box<Arith>),
    /// `left | right`
    BitwiseOr(Box<Arith>, Box<Arith>),
    /// `left && right`
    LogicalAnd(Box<Arith>, Box<Arith>),
    /// `left || right`
    LogicalOr(Box<Arith>, Box<Arith>),
    /// `first ? second : third`
    Ternary(Box<Arith>, Box<Arith>, Box<Arith>),
    /// Assigns the value of an underlying expression to a
    /// variable and returns the value, e.g. `x = 5`, or `x += 2`.
    Assign(String, Box<Arith>),
    /// `expr[, expr[, ...]]`
    Sequence(Vec<Arith>),
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
        use super::Word;
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
            let correct = Word::Param(p);

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
