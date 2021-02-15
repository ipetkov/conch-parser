//! Defines an interfaces to receive parse data and construct ASTs.
//!
//! This allows the parser to remain agnostic of the required source
//! representation, and frees up the library user to substitute their own.
//! If one does not require a custom AST representation, this module offers
//! a reasonable default builder implementation.
//!
//! If a custom AST representation is required you will need to implement
//! the `Builder` trait for your AST. Otherwise you can provide the `DefaultBuilder`
//! struct to the parser if you wish to use the default AST implementation.

use crate::ast::{
    AndOrList, DefaultArithmetic, DefaultParameter, ListableCommand, Redirect, RedirectOrCmdWord,
    RedirectOrEnvVar,
};

mod default_builder;

pub use self::default_builder::*;

/// An indicator to the builder of how complete commands are separated.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SeparatorKind {
    /// A semicolon appears between commands, normally indicating a sequence.
    Semi,
    /// An ampersand appears between commands, normally indicating an asyncronous job.
    Amp,
    /// A newline (and possibly a comment) appears at the end of a command before the next.
    Newline,
    /// The command was delimited by a token (e.g. a compound command delimiter) or
    /// the end of input, but is *not* followed by another sequential command.
    Other,
}

/// An indicator to the builder whether a `while` or `until` command was parsed.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum LoopKind {
    /// A `while` command was parsed, normally indicating the loop's body should be run
    /// while the guard's exit status is successful.
    While,
    /// An `until` command was parsed, normally indicating the loop's body should be run
    /// until the guard's exit status becomes successful.
    Until,
}

/// A grouping of a list of commands and any comments trailing after the commands.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CommandGroup<C> {
    /// The sequential list of commands.
    pub commands: Vec<C>,
    /// Any trailing comments appearing on the next line after the last command.
    pub trailing_comments: Vec<Newline>,
}

/// A grouping of guard and body commands, and any comments they may have.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct GuardBodyPairGroup<C> {
    /// The guard commands, which if successful, should lead to the
    /// execution of the body commands.
    pub guard: CommandGroup<C>,
    /// The body commands to execute if the guard is successful.
    pub body: CommandGroup<C>,
}

/// Parsed fragments relating to a shell `if` command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IfFragments<C> {
    /// A list of conditionals branches.
    pub conditionals: Vec<GuardBodyPairGroup<C>>,
    /// The `else` branch, if any,
    pub else_branch: Option<CommandGroup<C>>,
}

/// Parsed fragments relating to a shell `for` command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ForFragments<W, C> {
    /// The name of the variable to which each of the words will be bound.
    pub var: String,
    /// A comment that begins on the same line as the variable declaration.
    pub var_comment: Option<Newline>,
    /// Any comments after the variable declaration, a group of words to
    /// iterator over, and comment defined on the same line as the words.
    pub words: Option<(Vec<Newline>, Vec<W>, Option<Newline>)>,
    /// Any comments that appear after the `words` declaration (if it exists),
    /// but before the body of commands.
    pub pre_body_comments: Vec<Newline>,
    /// The body to be invoked for every iteration.
    pub body: CommandGroup<C>,
}

/// Parsed fragments relating to a shell `case` command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CaseFragments<W, C> {
    /// The word to be matched against.
    pub word: W,
    /// The comments appearing after the word to match but before the `in` reserved word.
    pub post_word_comments: Vec<Newline>,
    /// A comment appearing immediately after the `in` reserved word,
    /// yet still on the same line.
    pub in_comment: Option<Newline>,
    /// All the possible branches of the `case` command.
    pub arms: Vec<CaseArm<W, C>>,
    /// The comments appearing after the last arm but before the `esac` reserved word.
    pub post_arms_comments: Vec<Newline>,
}

/// An individual "unit of execution" within a `case` command.
///
/// Each arm has a number of pattern alternatives, and a body
/// of commands to run if any pattern matches.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CaseArm<W, C> {
    /// The patterns which correspond to this case arm.
    pub patterns: CasePatternFragments<W>,
    /// The body of commands to run if any pattern matches.
    pub body: CommandGroup<C>,
    /// A comment appearing at the end of the arm declaration,
    /// i.e. after `;;` but on the same line.
    pub arm_comment: Option<Newline>,
}

/// Parsed fragments relating to patterns in a shell `case` command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CasePatternFragments<W> {
    /// Comments appearing after a previous arm, but before the start of a pattern.
    pub pre_pattern_comments: Vec<Newline>,
    /// Pattern alternatives which all correspond to the same case arm.
    pub pattern_alternatives: Vec<W>,
    /// A comment appearing at the end of the pattern declaration on the same line.
    pub pattern_comment: Option<Newline>,
}

/// An indicator to the builder what kind of complex word was parsed.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ComplexWordKind<C> {
    /// Several distinct words concatenated together.
    Concat(Vec<WordKind<C>>),
    /// A regular word.
    Single(WordKind<C>),
}

/// An indicator to the builder what kind of word was parsed.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum WordKind<C> {
    /// A regular word.
    Simple(SimpleWordKind<C>),
    /// List of words concatenated within double quotes.
    DoubleQuoted(Vec<SimpleWordKind<C>>),
    /// List of words concatenated within single quotes. Virtually
    /// identical as a literal, but makes a distinction between the two.
    SingleQuoted(String),
}

/// An indicator to the builder what kind of simple word was parsed.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SimpleWordKind<C> {
    /// A non-special literal word.
    Literal(String),
    /// Access of a value inside a parameter, e.g. `$foo` or `$$`.
    Param(DefaultParameter),
    /// A parameter substitution, e.g. `${param-word}`.
    Subst(Box<ParameterSubstitutionKind<ComplexWordKind<C>, C>>),
    /// Represents the standard output of some command, e.g. \`echo foo\`.
    CommandSubst(CommandGroup<C>),
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

/// Represents the type of parameter that was parsed
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParameterSubstitutionKind<W, C> {
    /// Returns the standard output of running a command, e.g. `$(cmd)`
    Command(CommandGroup<C>),
    /// Returns the length of the value of a parameter, e.g. ${#param}
    Len(DefaultParameter),
    /// Returns the resulting value of an arithmetic subsitution, e.g. `$(( x++ ))`
    Arith(Option<DefaultArithmetic>),
    /// Use a provided value if the parameter is null or unset, e.g.
    /// `${param:-[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Default(bool, DefaultParameter, Option<W>),
    /// Assign a provided value to the parameter if it is null or unset,
    /// e.g. `${param:=[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Assign(bool, DefaultParameter, Option<W>),
    /// If the parameter is null or unset, an error should result with the provided
    /// message, e.g. `${param:?[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Error(bool, DefaultParameter, Option<W>),
    /// If the parameter is NOT null or unset, a provided word will be used,
    /// e.g. `${param:+[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Alternative(bool, DefaultParameter, Option<W>),
    /// Remove smallest suffix pattern, e.g. `${param%pattern}`
    RemoveSmallestSuffix(DefaultParameter, Option<W>),
    /// Remove largest suffix pattern, e.g. `${param%%pattern}`
    RemoveLargestSuffix(DefaultParameter, Option<W>),
    /// Remove smallest prefix pattern, e.g. `${param#pattern}`
    RemoveSmallestPrefix(DefaultParameter, Option<W>),
    /// Remove largest prefix pattern, e.g. `${param##pattern}`
    RemoveLargestPrefix(DefaultParameter, Option<W>),
}

/// Represents a parsed newline, more specifically, the presense of a comment
/// immediately preceeding the newline.
///
/// Since shell comments are usually treated as a newline, they can be present
/// anywhere a newline can be as well. Thus if it is desired to retain comments
/// they can be optionally attached to a parsed newline.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Newline(pub Option<String>);

/// A trait which defines an interface which the parser defined in the `parse` module
/// uses to delegate Abstract Syntax Tree creation. The methods defined here correspond
/// to their respectively named methods on the parser, and accept the relevant data for
/// each shell command type.
pub trait Builder {
    /// The type which represents a complete, top-level command.
    type Command;
    /// The type which represents a command that can be used in a pipeline.
    type PipeableCommand;
    /// The type which represents compound commands like `if`, `case`, `for`, etc.
    type CompoundCommand;
    /// The type which represents shell words, which can be command names or arguments.
    type Word;

    /// Invoked once a complete command is found. That is, a command delimited by a
    /// newline, semicolon, ampersand, or the end of input.
    ///
    /// # Arguments
    /// * pre_cmd_comments: any comments that appear before the start of the command
    /// * list: an and/or list of commands previously generated by the same builder
    /// * separator: indicates how the command was delimited
    /// * cmd_comment: a comment that appears at the end of the command
    fn complete_command(
        &mut self,
        pre_cmd_comments: Vec<Newline>,
        list: AndOrList<ListableCommand<Self::PipeableCommand>>,
        separator: SeparatorKind,
        cmd_comment: Option<Newline>,
    ) -> Self::Command;

    /// Invoked when the "simplest" possible command is parsed: an executable with arguments.
    ///
    /// # Arguments
    /// * redirects_or_env_vars: redirections or environment variables that occur before any command
    /// * redirects_or_cmd_words: redirections or any command or argument
    fn simple_command(
        &mut self,
        redirects_or_env_vars: Vec<RedirectOrEnvVar<Redirect<Self::Word>, String, Self::Word>>,
        redirects_or_cmd_words: Vec<RedirectOrCmdWord<Redirect<Self::Word>, Self::Word>>,
    ) -> Self::PipeableCommand;

    /// Invoked when a non-zero number of commands were parsed between balanced curly braces.
    /// Typically these commands should run within the current shell environment.
    ///
    /// # Arguments
    /// * cmds: the commands that were parsed between braces
    /// * redirects: any redirects to be applied over the **entire** group of commands
    fn brace_group(
        &mut self,
        cmds: CommandGroup<Self::Command>,
        redirects: Vec<Redirect<Self::Word>>,
    ) -> Self::CompoundCommand;

    /// Invoked when a non-zero number of commands were parsed between balanced parentheses.
    /// Typically these commands should run within their own environment without affecting
    /// the shell's global environment.
    ///
    /// # Arguments
    /// * cmds: the commands that were parsed between parens
    /// * redirects: any redirects to be applied over the **entire** group of commands
    fn subshell(
        &mut self,
        cmds: CommandGroup<Self::Command>,
        redirects: Vec<Redirect<Self::Word>>,
    ) -> Self::CompoundCommand;

    /// Invoked when a loop command like `while` or `until` is parsed.
    /// Typically these commands will execute their body based on the exit status of their guard.
    ///
    /// # Arguments
    /// * kind: the type of the loop: `while` or `until`
    /// * guard: commands that determine how long the loop will run for
    /// * body: commands to be run every iteration of the loop
    /// * redirects: any redirects to be applied over **all** commands part of the loop
    fn loop_command(
        &mut self,
        kind: LoopKind,
        guard_body_pair: GuardBodyPairGroup<Self::Command>,
        redirects: Vec<Redirect<Self::Word>>,
    ) -> Self::CompoundCommand;

    /// Invoked when an `if` conditional command is parsed.
    /// Typically an `if` command is made up of one or more guard-body pairs, where the body
    /// of the first successful corresponding guard is executed. There can also be an optional
    /// `else` part to be run if no guard is successful.
    ///
    /// # Arguments
    /// * fragments: parsed fragments relating to a shell `if` command.
    /// * redirects: any redirects to be applied over **all** commands within the `if` command
    fn if_command(
        &mut self,
        fragments: IfFragments<Self::Command>,
        redirects: Vec<Redirect<Self::Word>>,
    ) -> Self::CompoundCommand;

    /// Invoked when a `for` command is parsed.
    /// Typically a `for` command binds a variable to each member in a group of words and
    /// invokes its body with that variable present in the environment. If no words are
    /// specified, the command will iterate over the arguments to the script or enclosing function.
    ///
    /// # Arguments
    /// * fragments: parsed fragments relating to a shell `for` command.
    /// * redirects: any redirects to be applied over **all** commands within the `for` command
    fn for_command(
        &mut self,
        fragments: ForFragments<Self::Word, Self::Command>,
        redirects: Vec<Redirect<Self::Word>>,
    ) -> Self::CompoundCommand;

    /// Invoked when a `case` command is parsed.
    /// Typically this command will execute certain commands when a given word matches a pattern.
    ///
    /// # Arguments
    /// * fragments: parsed fragments relating to a shell `case` command.
    /// * redirects: any redirects to be applied over **all** commands part of the `case` block
    fn case_command(
        &mut self,
        fragments: CaseFragments<Self::Word, Self::Command>,
        redirects: Vec<Redirect<Self::Word>>,
    ) -> Self::CompoundCommand;

    /// Bridges the gap between a `PipeableCommand` and a `CompoundCommand` since
    /// `CompoundCommand`s are typically `PipeableCommand`s as well.
    ///
    /// # Arguments
    /// cmd: The `CompoundCommand` to convert into a `PipeableCommand`
    fn compound_command_into_pipeable(
        &mut self,
        cmd: Self::CompoundCommand,
    ) -> Self::PipeableCommand;

    /// Invoked when a function declaration is parsed.
    /// Typically a function declaration overwrites any previously defined function
    /// within the current environment.
    ///
    /// # Arguments
    /// * name: the name of the function to be created
    /// * post_name_comments: any comments appearing after the function name but before the body
    /// * body: commands to be run when the function is invoked
    fn function_declaration(
        &mut self,
        name: String,
        post_name_comments: Vec<Newline>,
        body: Self::CompoundCommand,
    ) -> Self::PipeableCommand;

    /// Invoked when a word is parsed.
    ///
    /// # Arguments
    /// * kind: the type of word that was parsed
    fn word(&mut self, kind: ComplexWordKind<Self::Command>) -> Self::Word;
}

macro_rules! impl_builder_body {
    ($T:ident) => {
        type Command = $T::Command;
        type PipeableCommand = $T::PipeableCommand;
        type CompoundCommand = $T::CompoundCommand;
        type Word = $T::Word;

        fn complete_command(
            &mut self,
            pre_cmd_comments: Vec<Newline>,
            list: AndOrList<ListableCommand<Self::PipeableCommand>>,
            separator: SeparatorKind,
            cmd_comment: Option<Newline>,
        ) -> Self::Command {
            (**self).complete_command(pre_cmd_comments, list, separator, cmd_comment)
        }

        fn simple_command(
            &mut self,
            redirects_or_env_vars: Vec<RedirectOrEnvVar<Redirect<Self::Word>, String, Self::Word>>,
            redirects_or_cmd_words: Vec<RedirectOrCmdWord<Redirect<Self::Word>, Self::Word>>,
        ) -> Self::PipeableCommand {
            (**self).simple_command(redirects_or_env_vars, redirects_or_cmd_words)
        }

        fn brace_group(
            &mut self,
            cmds: CommandGroup<Self::Command>,
            redirects: Vec<Redirect<Self::Word>>,
        ) -> Self::CompoundCommand {
            (**self).brace_group(cmds, redirects)
        }

        fn subshell(
            &mut self,
            cmds: CommandGroup<Self::Command>,
            redirects: Vec<Redirect<Self::Word>>,
        ) -> Self::CompoundCommand {
            (**self).subshell(cmds, redirects)
        }

        fn loop_command(
            &mut self,
            kind: LoopKind,
            guard_body_pair: GuardBodyPairGroup<Self::Command>,
            redirects: Vec<Redirect<Self::Word>>,
        ) -> Self::CompoundCommand {
            (**self).loop_command(kind, guard_body_pair, redirects)
        }

        fn if_command(
            &mut self,
            fragments: IfFragments<Self::Command>,
            redirects: Vec<Redirect<Self::Word>>,
        ) -> Self::CompoundCommand {
            (**self).if_command(fragments, redirects)
        }

        fn for_command(
            &mut self,
            fragments: ForFragments<Self::Word, Self::Command>,
            redirects: Vec<Redirect<Self::Word>>,
        ) -> Self::CompoundCommand {
            (**self).for_command(fragments, redirects)
        }

        fn case_command(
            &mut self,
            fragments: CaseFragments<Self::Word, Self::Command>,
            redirects: Vec<Redirect<Self::Word>>,
        ) -> Self::CompoundCommand {
            (**self).case_command(fragments, redirects)
        }

        fn compound_command_into_pipeable(
            &mut self,
            cmd: Self::CompoundCommand,
        ) -> Self::PipeableCommand {
            (**self).compound_command_into_pipeable(cmd)
        }

        fn function_declaration(
            &mut self,
            name: String,
            post_name_comments: Vec<Newline>,
            body: Self::CompoundCommand,
        ) -> Self::PipeableCommand {
            (**self).function_declaration(name, post_name_comments, body)
        }

        fn word(&mut self, kind: ComplexWordKind<Self::Command>) -> Self::Word {
            (**self).word(kind)
        }
    };
}

impl<'a, T: Builder + ?Sized> Builder for &'a mut T {
    impl_builder_body!(T);
}

impl<T: Builder + ?Sized> Builder for Box<T> {
    impl_builder_body!(T);
}
