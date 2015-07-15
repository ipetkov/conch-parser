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

use std::cmp::{PartialEq, Eq};
use std::error::Error;
use syntax::ast::{self, Command, CompoundCommand, Parameter, ParameterSubstitution, SimpleCommand, Redirect, Word};

/// An indicator to the builder of how complete commands are separated.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SeparatorKind {
    /// A semicolon appears between commands, normally indicating a sequence.
    Semi,
    /// An ampersand appears between commands, normally indicating an asyncronous job.
    Amp,
    /// A newline (and possibly a comment) appears at the end of a command before the next.
    Newline(ast::Newline),
    /// The command was delimited by a token (e.g. a compound command delimiter) or
    /// the end of input, but is *not* followed by another sequential command.
    Other,
}

/// An indicator to the builder whether an `AND` or `OR` command was parsed.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AndOrKind {
    /// An `AND` command was parsed, normally indicating the second should run if the first succeeds.
    /// Corresponds to the `&&` command separator.
    And,
    /// An `OR` command was parsed, normally indicating the second should run if the first fails.
    /// Corresponds to the `||` command separator.
    Or,
}

/// An indicator to the builder whether a `while` or `until` command was parsed.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LoopKind {
    /// A `while` command was parsed, normally indicating the loop's body should be run
    /// while the guard's exit status is successful.
    While,
    /// An `until` command was parsed, normally indicating the loop's body should be run
    /// until the guard's exit status becomes successful.
    Until,
}

/// An indicator to the builder what kind of word was parsed.
#[derive(Debug)]
pub enum WordKind<C> {
    /// A non-special literal word.
    Literal(String),
    /// Several distinct words concatenated together.
    Concat(Vec<WordKind<C>>),
    /// List of words concatenated within single quotes. Virtually
    /// identical to `Literal`, but makes the distinction if needed.
    SingleQuoted(String),
    /// List of words concatenated within double quotes.
    DoubleQuoted(Vec<WordKind<C>>),
    /// Access of a value inside a parameter, e.g. `$foo` or `$$`.
    Param(Parameter),
    /// A parameter substitution, e.g. `${param-word}`.
    Subst(ParameterSubstitutionKind<C, WordKind<C>>),
    /// Represents the standard output of some command, e.g. \`echo foo\`.
    CommandSubst(Vec<C>),
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
#[derive(Debug)]
pub enum RedirectKind<W> {
    /// Open a file for reading, e.g. [n]< file
    Read(Option<W>, W),
    /// Open a file for writing after truncating, e.g. [n]> file
    Write(Option<W>, W),
    /// Open a file for reading and writing, e.g. [n]<> file
    ReadWrite(Option<W>, W),
    /// Open a file for writing, appending to the end, e.g. [n]>> file
    Append(Option<W>, W),
    /// Open a file for writing, failing if the `noclobber` shell option is set, e.g.[n]>| file
    Clobber(Option<W>, W),

    /// Duplicate a file descriptor for reading, e.g. [n]<& n
    DupRead(Option<W>, W),
    /// Duplicate a file descriptor for writing, e.g. [n]>& n
    DupWrite(Option<W>, W),

    /// Close a file descriptor for reading, e.g. [n]<&-
    CloseRead(Option<W>),
    /// Close a file descriptor for writing, e.g. [n]>&-
    CloseWrite(Option<W>),
}

/// Represents the type of parameter that was parsed
#[derive(Debug)]
pub enum ParameterSubstitutionKind<C, W> {
    /// Returns the standard output of running a command, e.g. `$(cmd)`
    Command(Vec<C>),
    /// Returns the length of the value of a parameter, e.g. ${#param}
    Len(Parameter),
    /// Use a provided value if the parameter is null or unset, e.g.
    /// `${param:-[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Default(bool, Parameter, Option<Box<W>>),
    /// Assign a provided value to the parameter if it is null or unset,
    /// e.g. `${param:=[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Assign(bool, Parameter, Option<Box<W>>),
    /// If the parameter is null or unset, an error should result with the provided
    /// message, e.g. `${param:?[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Error(bool, Parameter, Option<Box<W>>),
    /// If the parameter is NOT null or unset, a provided word will be used,
    /// e.g. `${param:+[word]}`.
    /// The boolean indicates the presence of a `:`, and that if the parameter has
    /// a null value, that situation should be treated as if the parameter is unset.
    Alternative(bool, Parameter, Option<Box<W>>),
    /// Remove smallest suffix pattern, e.g. `${param%pattern}`
    RemoveSmallestSuffix(Parameter, Option<Box<W>>),
    /// Remove largest suffix pattern, e.g. `${param%%pattern}`
    RemoveLargestSuffix(Parameter, Option<Box<W>>),
    /// Remove smallest prefix pattern, e.g. `${param#pattern}`
    RemoveSmallestPrefix(Parameter, Option<Box<W>>),
    /// Remove largest prefix pattern, e.g. `${param##pattern}`
    RemoveLargestPrefix(Parameter, Option<Box<W>>),
}

/// A trait which defines an interface which the parser defined in the `parse` module
/// uses to delegate Abstract Syntax Tree creation. The methods defined here correspond
/// to their respectively named methods on the parser, and accept the relevant data for
/// each shell command type.
pub trait Builder {
    /// The type which represents the different shell commands.
    type Command;
    /// The type which represents shell words, which can be command names or arguments.
    type Word;
    /// The type which represents a file descriptor redirection.
    type Redirect;
    /// An error type that the builder may want to return.
    type Err: Error;

    /// Invoked once a complete command is found. That is, a command delimited by a
    /// newline, semicolon, ampersand, or the end of input.
    ///
    /// # Arguments
    /// * pre_cmd_comments: any comments that appear before the start of the command
    /// * cmd: the command itself, previously generated by the same builder
    /// * separator: indicates how the command was delimited
    /// * post_cmd_comments: any comments that appear after the end of the command
    fn complete_command(&mut self,
                        pre_cmd_comments: Vec<ast::Newline>,
                        cmd: Self::Command,
                        separator: SeparatorKind,
                        pos_cmd_comments: Vec<ast::Newline>)
        -> Result<Self::Command, Self::Err>;

    /// Invoked once two pipeline commands are parsed, which are separated by '&&' or '||'.
    /// Typically the second command is run based on the exit status of the first, running
    /// if the first succeeds for an AND command, or if the first fails for an OR command.
    ///
    /// # Arguments
    /// * first: the command on the left side of the separator
    /// * kind: the type of command parsed, AND or OR
    /// * post_separator_comments: comments appearing between the AND/OR separator and the
    /// start of the second command
    /// * second: the command on the right side of the separator
    fn and_or(&mut self,
              first: Self::Command,
              kind: AndOrKind,
              post_separator_comments: Vec<ast::Newline>,
              second: Self::Command)
        -> Result<Self::Command, Self::Err>;

    /// Invoked when a pipeline of commands is parsed.
    /// A pipeline is one or more commands where the standard output of the previous
    /// typically becomes the standard input of the next.
    ///
    /// # Arguments
    /// * bang: the presence of a `!` at the start of the pipeline, typically indicating
    /// that the pipeline's exit status should be logically inverted.
    /// * cmds: a collection of tuples which are any comments appearing after a pipe token, followed
    /// by the command itself, all in the order they were parsed
    fn pipeline(&mut self,
                bang: bool,
                cmds: Vec<(Vec<ast::Newline>, Self::Command)>)
        -> Result<Self::Command, Self::Err>;

    /// Invoked when the "simplest" possible command is parsed: an executable with arguments.
    ///
    /// # Arguments
    /// * env_vars: environment variables to be defined only for the command before it is run.
    /// * cmd: the name of the command to be run. This value is optional since the shell grammar
    /// permits that a simple command be made up of only env var definitions or redirects (or both).
    /// * args: arguments to the command
    /// * redirects: redirection of any file descriptors to/from other file descriptors or files.
    fn simple_command(&mut self,
                      env_vars: Vec<(String, Option<Self::Word>)>,
                      cmd: Option<Self::Word>,
                      args: Vec<Self::Word>,
                      redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>;

    /// Invoked when a non-zero number of commands were parsed between balanced curly braces.
    /// Typically these commands should run within the current shell environment.
    ///
    /// # Arguments
    /// * cmds: the commands that were parsed between braces
    /// * redirects: any redirects to be applied over the **entire** group of commands
    fn brace_group(&mut self,
                   cmds: Vec<Self::Command>,
                   redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>;

    /// Invoked when a non-zero number of commands were parsed between balanced parentheses.
    /// Typically these commands should run within their own environment without affecting
    /// the shell's global environment.
    ///
    /// # Arguments
    /// * cmds: the commands that were parsed between parens
    /// * redirects: any redirects to be applied over the **entire** group of commands
    fn subshell(&mut self,
                cmds: Vec<Self::Command>,
                redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>;

    /// Invoked when a loop command like `while` or `until` is parsed.
    /// Typically these commands will execute their body based on the exit status of their guard.
    ///
    /// # Arguments
    /// * kind: the type of the loop: `while` or `until`
    /// * guard: commands that determine how long the loop will run for
    /// * body: commands to be run every iteration of the loop
    /// * redirects: any redirects to be applied over **all** commands part of the loop
    fn loop_command(&mut self,
                    kind: LoopKind,
                    guard: Vec<Self::Command>,
                    body: Vec<Self::Command>,
                    redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>;

    /// Invoked when an `if` conditional command is parsed.
    /// Typically an `if` command is made up of one or more guard-body pairs, where the body
    /// of the first successful corresponding guard is executed. There can also be an optional
    /// `else` part to be run if no guard is successful.
    ///
    /// # Arguments
    /// * branches: a collection of (guard, body) command groups
    /// * else_part: optional group of commands to be run if no guard exited successfully
    /// * redirects: any redirects to be applied over **all** commands within the `if` command
    fn if_command(&mut self,
                  branches: Vec<(Vec<Self::Command>, Vec<Self::Command>)>,
                  else_part: Option<Vec<Self::Command>>,
                  redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>;

    /// Invoked when a `for` command is parsed.
    /// Typically a `for` command binds a variable to each member in a group of words and
    /// invokes its body with that variable present in the environment. If no words are
    /// specified, the command will iterate over the arguments to the script or enclosing function.
    ///
    /// # Arguments
    /// * var: the name of the variable to which each of the words will be bound
    /// * post_var_comments: any comments that appear after the variable declaration
    /// * in_words: a group of words to iterate over if present
    /// * post_word_comments: any comments that appear after the `in_words` declaration (if it exists)
    /// * body: the body to be invoked for every iteration
    /// * redirects: any redirects to be applied over **all** commands within the `for` command
    fn for_command(&mut self,
                   var: String,
                   post_var_comments: Vec<ast::Newline>,
                   in_words: Option<Vec<Self::Word>>,
                   post_word_comments: Option<Vec<ast::Newline>>,
                   body: Vec<Self::Command>,
                   redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>;

    /// Invoked when a `case` command is parsed.
    /// Typically this command will execute certain commands when a given word matches a pattern.
    ///
    /// # Arguments
    /// * word: the word to be matched against
    /// * post_word_comments: the comments appearing after the word to match but before the `in` reserved word
    /// * branches: the various alternatives that the `case` command can take. The first part of the tuple
    /// is a list of alternative patterns, while the second is the group of commands to be run in case
    /// any of the alternative patterns is matched. The patterns are wrapped in an internal tuple which
    /// holds all comments appearing before and after the pattern (but before the command start).
    /// * post_branch_comments: the comments appearing after the last arm but before the `esac` reserved word
    /// * redirects: any redirects to be applied over **all** commands part of the `case` block
    fn case_command(&mut self,
                    word: Self::Word,
                    post_word_comments: Vec<ast::Newline>,
                    branches: Vec<( (Vec<ast::Newline>, Vec<Self::Word>, Vec<ast::Newline>), Vec<Self::Command>)>,
                    post_branch_comments: Vec<ast::Newline>,
                    redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>;

    /// Invoked when a function declaration is parsed.
    /// Typically a function declaration overwrites any previously defined function
    /// within the current environment.
    ///
    /// # Arguments
    /// * name: the name of the function to be created
    /// * body: commands to be run when the function is invoked
    fn function_declaration(&mut self,
                            name: String,
                            body: Self::Command)
        -> Result<Self::Command, Self::Err>;

    /// Invoked when only comments are parsed with no commands following.
    /// This can occur if an entire shell script is commented out or if there
    /// are comments present at the end of the script.
    ///
    /// # Arguments
    /// * comments: the parsed comments
    fn comments(&mut self,
                comments: Vec<ast::Newline>)
        -> Result<(), Self::Err>;

    /// Invoked when a word is parsed.
    ///
    /// # Arguments
    /// * kind: the type of word that was parsed
    fn word(&mut self,
            kind: WordKind<Self::Command>)
        -> Result<Self::Word, Self::Err>;

    /// Invoked when a redirect is parsed.
    ///
    /// # Arguments
    /// * kind: the type of redirect that was parsed
    fn redirect(&mut self,
                kind: RedirectKind<Self::Word>)
        -> Result<Self::Redirect, Self::Err>;
}

impl Builder for DefaultBuilder {
    type Command  = Command;
    type Word     = Word;
    type Redirect = Redirect;
    type Err      = DummyError;

    /// Constructs a `Command::Job` node with the provided inputs if the command
    /// was delimited by an ampersand or the command itself otherwise.
    fn complete_command(&mut self,
                        _pre_cmd_comments: Vec<ast::Newline>,
                        cmd: Command,
                        separator: SeparatorKind,
                        _pos_cmd_comments: Vec<ast::Newline>)
        -> Result<Command, Self::Err>
    {
        match separator {
            SeparatorKind::Semi  |
            SeparatorKind::Other |
            SeparatorKind::Newline(_) => Ok(cmd),
            SeparatorKind::Amp => Ok(Command::Job(Box::new(cmd))),
        }
    }

    /// Constructs a `Command::And` or `Command::Or` node with the provided inputs.
    fn and_or(&mut self,
              first: Command,
              kind: AndOrKind,
              _post_separator_comments: Vec<ast::Newline>,
              second: Command)
        -> Result<Command, Self::Err>
    {
        match kind {
            AndOrKind::And => Ok(Command::And(Box::new(first), Box::new(second))),
            AndOrKind::Or  => Ok(Command::Or(Box::new(first), Box::new(second))),
        }
    }

    /// Constructs a `Command::Pipe` node with the provided inputs or a `Command::Simple`
    /// node if only a single command with no status inversion is supplied.
    fn pipeline(&mut self,
                bang: bool,
                cmds: Vec<(Vec<ast::Newline>, Command)>)
        -> Result<Command, Self::Err>
    {
        debug_assert_eq!(cmds.is_empty(), false);
        let mut cmds: Vec<Command> = cmds.into_iter().map(|(_, c)| c).collect();

        // Command::Pipe is the only AST node which allows for a status
        // negation, so we are forced to use it even if we have a single
        // command. Otherwise there is no need to wrap it further.
        if bang || cmds.len() > 1 {
            cmds.shrink_to_fit();
            Ok(Command::Pipe(bang, cmds))
        } else {
            Ok(cmds.pop().unwrap())
        }
    }

    /// Constructs a `Command::Simple` node with the provided inputs.
    fn simple_command(&mut self,
                      mut env_vars: Vec<(String, Option<Word>)>,
                      cmd: Option<Word>,
                      mut args: Vec<Word>,
                      mut redirects: Vec<Redirect>)
        -> Result<Command, Self::Err>
    {
        env_vars.shrink_to_fit();
        args.shrink_to_fit();
        redirects.shrink_to_fit();

        Ok(Command::Simple(Box::new(SimpleCommand {
            cmd: cmd,
            vars: env_vars,
            args: args,
            io: redirects,
        })))
    }

    /// Constructs a `Command::Compound(Brace)` node with the provided inputs.
    fn brace_group(&mut self,
                   mut cmds: Vec<Command>,
                   mut redirects: Vec<Redirect>)
        -> Result<Command, Self::Err>
    {
        cmds.shrink_to_fit();
        redirects.shrink_to_fit();
        Ok(Command::Compound(Box::new(CompoundCommand::Brace(cmds)), redirects))
    }

    /// Constructs a `Command::Compound(Subshell)` node with the provided inputs.
    fn subshell(&mut self,
                mut cmds: Vec<Command>,
                mut redirects: Vec<Redirect>)
        -> Result<Command, Self::Err>
    {
        cmds.shrink_to_fit();
        redirects.shrink_to_fit();
        Ok(Command::Compound(Box::new(CompoundCommand::Subshell(cmds)), redirects))
    }

    /// Constructs a `Command::Compound(Loop)` node with the provided inputs.
    fn loop_command(&mut self,
                    kind: LoopKind,
                    mut guard: Vec<Command>,
                    mut body: Vec<Command>,
                    mut redirects: Vec<Redirect>)
        -> Result<Command, Self::Err>
    {
        guard.shrink_to_fit();
        body.shrink_to_fit();
        redirects.shrink_to_fit();

        let loop_cmd = match kind {
            LoopKind::While => CompoundCommand::While(guard, body),
            LoopKind::Until => CompoundCommand::Until(guard, body),
        };

        Ok(Command::Compound(Box::new(loop_cmd), redirects))
    }

    /// Constructs a `Command::Compound(If)` node with the provided inputs.
    fn if_command(&mut self,
                  mut branches: Vec<(Vec<Command>, Vec<Command>)>,
                  mut else_part: Option<Vec<Command>>,
                  mut redirects: Vec<Redirect>)
        -> Result<Command, Self::Err>
    {
        for &mut (ref mut guard, ref mut body) in branches.iter_mut() {
            guard.shrink_to_fit();
            body.shrink_to_fit();
        }

        for els in else_part.iter_mut() { els.shrink_to_fit(); }
        redirects.shrink_to_fit();

        Ok(Command::Compound(Box::new(CompoundCommand::If(branches, else_part)), redirects))
    }

    /// Constructs a `Command::Compound(For)` node with the provided inputs.
    fn for_command(&mut self,
                   var: String,
                   _post_var_comments: Vec<ast::Newline>,
                   mut in_words: Option<Vec<Word>>,
                   _post_word_comments: Option<Vec<ast::Newline>>,
                   mut body: Vec<Command>,
                   mut redirects: Vec<Redirect>)
        -> Result<Command, Self::Err>
    {
        for word in in_words.iter_mut() { word.shrink_to_fit(); }
        body.shrink_to_fit();
        redirects.shrink_to_fit();
        Ok(Command::Compound(Box::new(CompoundCommand::For(var, in_words, body)), redirects))
    }

    /// Constructs a `Command::Compound(Case)` node with the provided inputs.
    fn case_command(&mut self,
                    word: Word,
                    _post_word_comments: Vec<ast::Newline>,
                    branches: Vec<( (Vec<ast::Newline>, Vec<Word>, Vec<ast::Newline>), Vec<Command>)>,
                    _post_branch_comments: Vec<ast::Newline>,
                    mut redirects: Vec<Redirect>)
        -> Result<Command, Self::Err>
    {
        let branches = branches.into_iter().map(|((_, mut pats, _), mut cmds)| {
            pats.shrink_to_fit();
            cmds.shrink_to_fit();
            (pats, cmds)
        }).collect();

        redirects.shrink_to_fit();
        Ok(Command::Compound(Box::new(CompoundCommand::Case(word, branches)), redirects))
    }

    /// Constructs a `Command::Function` node with the provided inputs.
    fn function_declaration(&mut self,
                            name: String,
                            body: Command)
        -> Result<Command, Self::Err>
    {
        Ok(Command::Function(name, Box::new(body)))
    }

    /// Ignored by the builder.
    fn comments(&mut self,
                _comments: Vec<ast::Newline>)
        -> Result<(), Self::Err>
    {
        Ok(())
    }

    /// Constructs a `ast::Word` from the provided input.
    fn word(&mut self,
            kind: WordKind<Command>)
        -> Result<Word, Self::Err>
    {
        use self::ParameterSubstitutionKind::*;

        macro_rules! map {
            ($pat:expr) => {
                match $pat {
                    Some(w) => Some(Box::new(try!(self.word(*w)))),
                    None => None,
                }
            }
        }

        let word = match kind {
            WordKind::Literal(s)      => Word::Literal(s),
            WordKind::SingleQuoted(s) => Word::SingleQuoted(s),
            WordKind::Param(p)        => Word::Param(p),
            WordKind::Escaped(s)      => Word::Escaped(s),
            WordKind::Star            => Word::Star,
            WordKind::Question        => Word::Question,
            WordKind::SquareOpen      => Word::SquareOpen,
            WordKind::SquareClose     => Word::SquareClose,
            WordKind::Tilde           => Word::Tilde,

            WordKind::CommandSubst(c) => Word::Subst(ParameterSubstitution::Command(c)),

            WordKind::Subst(s) => match s {
                Len(p)     => Word::Subst(ParameterSubstitution::Len(p)),
                Command(c) => Word::Subst(ParameterSubstitution::Command(c)),
                Default(c, p, w)           => Word::Subst(ParameterSubstitution::Default(c, p, map!(w))),
                Assign(c, p, w)            => Word::Subst(ParameterSubstitution::Assign(c, p, map!(w))),
                Error(c, p, w)             => Word::Subst(ParameterSubstitution::Error(c, p, map!(w))),
                Alternative(c, p, w)       => Word::Subst(ParameterSubstitution::Alternative(c, p, map!(w))),
                RemoveSmallestSuffix(p, w) => Word::Subst(ParameterSubstitution::RemoveSmallestSuffix(p, map!(w))),
                RemoveLargestSuffix(p, w)  => Word::Subst(ParameterSubstitution::RemoveLargestSuffix(p, map!(w))),
                RemoveSmallestPrefix(p, w) => Word::Subst(ParameterSubstitution::RemoveSmallestPrefix(p, map!(w))),
                RemoveLargestPrefix(p, w)  => Word::Subst(ParameterSubstitution::RemoveLargestPrefix(p, map!(w))),
            },

            WordKind::Concat(words) => Word::Concat(
                try!(words.into_iter().map(|w| self.word(w)).collect())
            ),

            WordKind::DoubleQuoted(words) => Word::DoubleQuoted(
                try!(words.into_iter().map(|w| self.word(w)).collect())
            ),
        };

        Ok(word)
    }

    /// Constructs a `ast::Redirect` from the provided input.
    fn redirect(&mut self,
                kind: RedirectKind<Word>)
        -> Result<Redirect, Self::Err>
    {
        let io = match kind {
            RedirectKind::Read(fd, path)      => Redirect::Read(fd, path),
            RedirectKind::Write(fd, path)     => Redirect::Write(fd, path),
            RedirectKind::ReadWrite(fd, path) => Redirect::ReadWrite(fd, path),
            RedirectKind::Append(fd, path)    => Redirect::Append(fd, path),
            RedirectKind::Clobber(fd, path)   => Redirect::Clobber(fd, path),
            RedirectKind::DupRead(src, dst)   => Redirect::DupRead(src, dst),
            RedirectKind::DupWrite(src, dst)  => Redirect::DupWrite(src, dst),
            RedirectKind::CloseRead(src)      => Redirect::CloseRead(src),
            RedirectKind::CloseWrite(src)     => Redirect::CloseWrite(src),
        };

        Ok(io)
    }
}

impl<'a, T: Builder> Builder for &'a mut T {
    type Command = T::Command;
    type Word = T::Word;
    type Redirect = T::Redirect;
    type Err = T::Err;

    fn complete_command(&mut self,
                        pre_cmd_comments: Vec<ast::Newline>,
                        cmd: Self::Command,
                        separator: SeparatorKind,
                        post_cmd_comments: Vec<ast::Newline>)
        -> Result<Self::Command, Self::Err>
    {
        (**self).complete_command(pre_cmd_comments, cmd, separator, post_cmd_comments)
    }

    fn and_or(&mut self,
              first: Self::Command,
              kind: AndOrKind,
              post_separator_comments: Vec<ast::Newline>,
              second: Self::Command)
        -> Result<Self::Command, Self::Err>
    {
        (**self).and_or(first, kind, post_separator_comments, second)
    }

    fn pipeline(&mut self,
                bang: bool,
                cmds: Vec<(Vec<ast::Newline>, Self::Command)>)
        -> Result<Self::Command, Self::Err>
    {
        (**self).pipeline(bang, cmds)
    }

    fn simple_command(&mut self,
                      env_vars: Vec<(String, Option<Self::Word>)>,
                      cmd: Option<Self::Word>,
                      args: Vec<Self::Word>,
                      redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>
    {
        (**self).simple_command(env_vars, cmd, args, redirects)
    }

    fn brace_group(&mut self,
                   cmds: Vec<Self::Command>,
                   redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>
    {
        (**self).brace_group(cmds, redirects)
    }

    fn subshell(&mut self,
                cmds: Vec<Self::Command>,
                redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>
    {
        (**self).subshell(cmds, redirects)
    }

    fn loop_command(&mut self,
                    kind: LoopKind,
                    guard: Vec<Self::Command>,
                    body: Vec<Self::Command>,
                    redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>
    {
        (**self).loop_command(kind, guard, body, redirects)
    }

    fn if_command(&mut self,
                  branches: Vec<(Vec<Self::Command>, Vec<Self::Command>)>,
                  else_part: Option<Vec<Self::Command>>,
                  redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>
    {
        (**self).if_command(branches, else_part, redirects)
    }

    fn for_command(&mut self,
                   var: String,
                   post_var_comments: Vec<ast::Newline>,
                   in_words: Option<Vec<Self::Word>>,
                   post_word_comments: Option<Vec<ast::Newline>>,
                   body: Vec<Self::Command>,
                   redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>
    {
        (**self).for_command(var, post_var_comments, in_words, post_word_comments, body, redirects)
    }

    fn case_command(&mut self,
                    word: Self::Word,
                    post_word_comments: Vec<ast::Newline>,
                    branches: Vec<( (Vec<ast::Newline>, Vec<Self::Word>, Vec<ast::Newline>), Vec<Self::Command>)>,
                    post_branch_comments: Vec<ast::Newline>,
                    redirects: Vec<Self::Redirect>)
        -> Result<Self::Command, Self::Err>
    {
        (**self).case_command(word, post_word_comments, branches, post_branch_comments, redirects)
    }

    fn function_declaration(&mut self,
                            name: String,
                            body: Self::Command)
        -> Result<Self::Command, Self::Err>
    {
        (**self).function_declaration(name, body)
    }

    fn comments(&mut self,
                comments: Vec<ast::Newline>)
        -> Result<(), Self::Err>
    {
        (**self).comments(comments)
    }

    fn word(&mut self,
            kind: WordKind<Self::Command>)
        -> Result<Self::Word, Self::Err>
    {
        (**self).word(kind)
    }

    fn redirect(&mut self,
                kind: RedirectKind<Self::Word>)
        -> Result<Self::Redirect, Self::Err>
    {
        (**self).redirect(kind)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
/// A dummy error which implements the `Error` trait.
pub struct DummyError;

impl ::std::fmt::Display for DummyError {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        fmt.write_str("dummy error")
    }
}

impl Error for DummyError {
    fn description(&self) -> &str {
        "dummy error"
    }
}

/// A `Builder` implementation which builds shell commands using the AST definitions in the `ast` module.
pub struct DefaultBuilder;

impl ::std::default::Default for DefaultBuilder {
    fn default() -> DefaultBuilder {
        DefaultBuilder
    }
}

impl<W> Eq for RedirectKind<W> where W: Eq {}
impl<W> PartialEq<RedirectKind<W>> for RedirectKind<W> where W: PartialEq<W> {
    fn eq(&self, other: &Self) -> bool {
        use self::RedirectKind::*;
        match (self, other) {
            (&Read(ref fd1, ref w1),      &Read(ref fd2, ref w2))      => fd1 == fd2 && w1 == w2,
            (&Write(ref fd1, ref w1),     &Write(ref fd2, ref w2))     => fd1 == fd2 && w1 == w2,
            (&ReadWrite(ref fd1, ref w1), &ReadWrite(ref fd2, ref w2)) => fd1 == fd2 && w1 == w2,
            (&Append(ref fd1, ref w1),    &Append(ref fd2, ref w2))    => fd1 == fd2 && w1 == w2,
            (&Clobber(ref fd1, ref w1),   &Clobber(ref fd2, ref w2))   => fd1 == fd2 && w1 == w2,
            (&DupRead(ref fd1, ref w1),   &DupRead(ref fd2, ref w2))   => fd1 == fd2 && w1 == w2,
            (&DupWrite(ref fd1, ref w1),  &DupWrite(ref fd2, ref w2))  => fd1 == fd2 && w1 == w2,
            (&CloseRead(ref fd1),         &CloseRead(ref fd2))         => fd1 == fd2,
            (&CloseWrite(ref fd1),        &CloseWrite(ref fd2))        => fd1 == fd2,
            _ => false,
        }
    }
}

impl<W> Clone for RedirectKind<W> where W: Clone {
    fn clone(&self) -> Self {
        use self::RedirectKind::*;
        match *self {
            Read(ref fd, ref w)      => Read(fd.clone(), w.clone()),
            Write(ref fd, ref w)     => Write(fd.clone(), w.clone()),
            ReadWrite(ref fd, ref w) => ReadWrite(fd.clone(), w.clone()),
            Append(ref fd, ref w)    => Append(fd.clone(), w.clone()),
            Clobber(ref fd, ref w)   => Clobber(fd.clone(), w.clone()),
            DupRead(ref fd, ref w)   => DupRead(fd.clone(), w.clone()),
            DupWrite(ref fd, ref w)  => DupWrite(fd.clone(), w.clone()),
            CloseRead(ref fd)        => CloseRead(fd.clone()),
            CloseWrite(ref fd)       => CloseWrite(fd.clone()),
        }
    }
}

impl<C> Eq for WordKind<C> where C: Eq {}
impl<C> PartialEq<WordKind<C>> for WordKind<C> where C: PartialEq {
    fn eq(&self, other: &Self) -> bool {
        use self::WordKind::*;
        match (self, other) {
            (&Literal(ref s1),      &Literal(ref s2))      if s1 == s2 => true,
            (&Concat(ref v1),       &Concat(ref v2))       if v1 == v2 => true,
            (&SingleQuoted(ref s1), &SingleQuoted(ref s2)) if s1 == s2 => true,
            (&DoubleQuoted(ref v1), &DoubleQuoted(ref v2)) if v1 == v2 => true,
            (&Escaped(ref s1),      &Escaped(ref s2))      if s1 == s2 => true,
            (&Param(ref p1),        &Param(ref p2))        if p1 == p2 => true,
            (&Subst(ref p1),        &Subst(ref p2))        if p1 == p2 => true,
            (&CommandSubst(ref c1), &CommandSubst(ref c2)) if c1 == c2 => true,
            (&Star,                 &Star)                             => true,
            (&Question,             &Question)                         => true,
            (&SquareOpen,           &SquareOpen)                       => true,
            (&SquareClose,          &SquareClose)                      => true,
            (&Tilde,                &Tilde)                            => true,
            _ => false,
        }
    }
}

impl<C> Clone for WordKind<C> where C: Clone {
    fn clone(&self) -> Self {
        use self::WordKind::*;

        match *self {
            Literal(ref s)      => Literal(s.clone()),
            Concat(ref v)       => Concat(v.clone()),
            SingleQuoted(ref s) => SingleQuoted(s.clone()),
            DoubleQuoted(ref v) => DoubleQuoted(v.clone()),
            Escaped(ref s)      => Escaped(s.clone()),
            Param(ref p)        => Param(p.clone()),
            Subst(ref p)        => Subst(p.clone()),
            CommandSubst(ref c) => CommandSubst(c.clone()),
            Star                => Star,
            Question            => Question,
            SquareOpen          => SquareOpen,
            SquareClose         => SquareClose,
            Tilde               => Tilde,
        }
    }
}

impl<C, W> Eq for ParameterSubstitutionKind<C, W> where C: Eq, W: Eq {}
impl<C, W> PartialEq<ParameterSubstitutionKind<C, W>> for ParameterSubstitutionKind<C, W>
where C: PartialEq, W: PartialEq {
    fn eq(&self, other: &Self) -> bool {
        use self::ParameterSubstitutionKind::*;
        match (self, other) {
            (&Command(ref v1), &Command(ref v2)) if v1 == v2 => true,
            (&Len(ref s1),     &Len(ref s2))     if s1 == s2 => true,

            (&RemoveSmallestSuffix(ref p1, ref w1), &RemoveSmallestSuffix(ref p2, ref w2)) |
            (&RemoveLargestSuffix(ref p1, ref w1),  &RemoveLargestSuffix(ref p2, ref w2))  |
            (&RemoveSmallestPrefix(ref p1, ref w1), &RemoveSmallestPrefix(ref p2, ref w2)) |
            (&RemoveLargestPrefix(ref p1, ref w1),  &RemoveLargestPrefix(ref p2, ref w2))
                if p1 == p2 && w1 == w2 => true,

            (&Default(c1, ref p1, ref w1),     &Default(c2, ref p2, ref w2))     |
            (&Assign(c1, ref p1, ref w1),      &Assign(c2, ref p2, ref w2))      |
            (&Error(c1, ref p1, ref w1),       &Error(c2, ref p2, ref w2))       |
            (&Alternative(c1, ref p1, ref w1), &Alternative(c2, ref p2, ref w2))
                if c1 == c2 && p1 == p2 && w1 == w2 => true,

            _ => false,
        }
    }
}

impl<C, W> Clone for ParameterSubstitutionKind<C, W> where C: Clone, W: Clone {
    fn clone(&self) -> Self {
        use self::ParameterSubstitutionKind::*;

        match *self {
            Command(ref v) => Command(v.clone()),
            Len(ref s)     => Len(s.clone()),

            Default(c, ref p, ref w)     => Default(c, p.clone(), w.clone()),
            Assign(c, ref p, ref w)      => Assign(c, p.clone(), w.clone()),
            Error(c, ref p, ref w)       => Error(c, p.clone(), w.clone()),
            Alternative(c, ref p, ref w) => Alternative(c, p.clone(), w.clone()),

            RemoveSmallestSuffix(ref p, ref w) => RemoveSmallestSuffix(p.clone(), w.clone()),
            RemoveLargestSuffix(ref p, ref w)  => RemoveLargestSuffix(p.clone(), w.clone()),
            RemoveSmallestPrefix(ref p, ref w) => RemoveSmallestPrefix(p.clone(), w.clone()),
            RemoveLargestPrefix(ref p, ref w)  => RemoveLargestPrefix(p.clone(), w.clone()),
        }
    }
}
