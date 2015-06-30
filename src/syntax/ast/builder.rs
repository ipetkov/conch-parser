use syntax::ast::{self, Command, CompoundCommand, SimpleCommand, Redirect, Word};

pub enum SeparatorKind {
    Semi,
    Amp,
    EOF,
    Newline(ast::Newline),
}

pub enum AndOrKind {
    And,
    Or,
}

pub struct CommandBuilder;

pub trait Builder {
    type Output;
    type Err;

    fn complete_command(&mut self,
                        separator: SeparatorKind,
                        cmd: Self::Output)
        -> Result<Self::Output, Self::Err>;

    fn and_or(&mut self,
              kind: AndOrKind,
              first: Self::Output,
              second: Self::Output)
        -> Result<Self::Output, Self::Err>;

    fn pipeline(&mut self,
                bang: bool,
                cmds: Vec<Self::Output>)
        -> Result<Self::Output, Self::Err>;

    fn simple_command(&mut self,
                      env_vars: Vec<(String, Word)>,
                      cmd: Option<Word>,
                      args: Vec<Word>,
                      redirections: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>;

    fn brace_group(&mut self,
                   cmds: Vec<Self::Output>,
                   redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>;

    fn subshell(&mut self,
                cmds: Vec<Self::Output>,
                redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>;

    fn loop_command(&mut self,
                    until: bool,
                    guard: Vec<Self::Output>,
                    body: Vec<Self::Output>,
                    redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>;

    fn if_command(&mut self,
                  branches: Vec<(Vec<Self::Output>, Vec<Self::Output>)>,
                  else_part: Option<Vec<Self::Output>>,
                  redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>;

    fn for_command(&mut self,
                   var: String,
                   in_words: Option<Vec<Word>>,
                   body: Vec<Self::Output>,
                   redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>;

    fn case_command(&mut self,
                    match_word: Word,
                    arms: Vec<(Vec<Word>, Vec<Self::Output>)>,
                    redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>;

    fn function_declaration(&mut self,
                            fn_name: String,
                            body: Self::Output)
        -> Result<Self::Output, Self::Err>;
}

impl Builder for CommandBuilder {
    type Output = Command;
    type Err = ();

    fn complete_command(&mut self,
                        separator: SeparatorKind,
                        cmd: Self::Output)
        -> Result<Self::Output, Self::Err>
    {
        match separator {
            SeparatorKind::Semi |
            SeparatorKind::EOF  |
            SeparatorKind::Newline(_) => Ok(cmd),
            SeparatorKind::Amp => Ok(Command::Job(Box::new(cmd))),
        }
    }

    fn and_or(&mut self,
              kind: AndOrKind,
              first: Self::Output,
              second: Self::Output)
        -> Result<Self::Output, Self::Err>
    {
        match kind {
            AndOrKind::And => Ok(Command::And(Box::new(first), Box::new(second))),
            AndOrKind::Or  => Ok(Command::Or(Box::new(first), Box::new(second))),
        }
    }

    fn pipeline(&mut self,
                bang: bool,
                mut cmds: Vec<Self::Output>)
        -> Result<Self::Output, Self::Err>
    {
        debug_assert_eq!(cmds.is_empty(), false);

        // Command::Pipe is the only AST node which allows for a status
        // negation, so we are forced to use it even if we have a single
        // command. Otherwise there is no need to wrap it further.
        if bang || cmds.len() > 1 {
            Ok(Command::Pipe(bang, cmds))
        } else {
            Ok(cmds.pop().unwrap())
        }
    }

    fn simple_command(&mut self,
                      env_vars: Vec<(String, Word)>,
                      cmd: Option<Word>,
                      args: Vec<Word>,
                      redirections: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>
    {
        Ok(Command::Simple(Box::new(SimpleCommand {
            cmd: cmd,
            vars: env_vars,
            args: args,
            io: redirections,
        })))
    }

    fn brace_group(&mut self,
                   cmds: Vec<Self::Output>,
                   redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>
    {
        Ok(Command::Compound(Box::new(CompoundCommand::Brace(cmds)), redirects))
    }

    fn subshell(&mut self,
                cmds: Vec<Self::Output>,
                redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>
    {
        Ok(Command::Compound(Box::new(CompoundCommand::Subshell(cmds)), redirects))
    }

    fn loop_command(&mut self,
                    until: bool,
                    guard: Vec<Self::Output>,
                    body: Vec<Self::Output>,
                    redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>
    {
        Ok(Command::Compound(Box::new(CompoundCommand::Loop(until, guard, body)), redirects))
    }

    fn if_command(&mut self,
                  branches: Vec<(Vec<Self::Output>, Vec<Self::Output>)>,
                  else_part: Option<Vec<Self::Output>>,
                  redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>
    {
        Ok(Command::Compound(Box::new(CompoundCommand::If(branches, else_part)), redirects))
    }

    fn for_command(&mut self,
                   var: String,
                   in_words: Option<Vec<Word>>,
                   body: Vec<Self::Output>,
                   redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>
    {
        Ok(Command::Compound(Box::new(CompoundCommand::For(var, in_words, body)), redirects))
    }

    fn case_command(&mut self,
                    match_word: Word,
                    arms: Vec<(Vec<Word>, Vec<Self::Output>)>,
                    redirects: Vec<Redirect>)
        -> Result<Self::Output, Self::Err>
    {
        Ok(Command::Compound(Box::new(CompoundCommand::Case(match_word, arms)), redirects))
    }

    fn function_declaration(&mut self,
                            fn_name: String,
                            body: Self::Output)
        -> Result<Self::Output, Self::Err>
    {
        Ok(Command::Function(fn_name, Box::new(body)))
    }
}

impl ::std::default::Default for CommandBuilder {
    fn default() -> CommandBuilder {
        CommandBuilder
    }
}
