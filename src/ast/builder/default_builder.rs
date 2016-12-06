use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::Arc;
use ast::{self, AndOr, AndOrList, Arithmetic, Command, CompoundCommand,
          CompoundCommandKind, ComplexWord, DefaultPipeableCommand, ListableCommand, Parameter,
          ParameterSubstitution, PipeableCommand, Redirect, SimpleCommand, SimpleWord,
          TopLevelCommand, TopLevelWord, Word};
use ast::builder::*;
use parse::ParseResult;
use void::Void;

/// A `Builder` implementation which builds shell commands using the AST definitions in the `ast` module.
#[derive(Debug, Copy, Clone)]
pub struct DefaultBuilder<T>(PhantomData<T>);

/// A `DefaultBuilder` implementation which uses regular `String`s when
/// representing shell words.
pub type StringBuilder = DefaultBuilder<String>;

/// A `DefaultBuilder` implementation which uses `Rc<String>`s when
/// representing shell words.
pub type RcBuilder = DefaultBuilder<Rc<String>>;

/// A `DefaultBuilder` implementation which uses `Arc<String>`s when
/// representing shell words.
pub type ArcBuilder = DefaultBuilder<Arc<String>>;

impl<T> ::std::default::Default for DefaultBuilder<T> {
    fn default() -> Self {
        DefaultBuilder::new()
    }
}

impl<T> DefaultBuilder<T> {
    /// Constructs a builder.
    pub fn new() -> Self {
        DefaultBuilder(PhantomData)
    }
}

impl<T: From<String>> Builder for DefaultBuilder<T> {
    type Command         = TopLevelCommand<T>;
    type CommandList     = AndOrList<Self::ListableCommand>;
    type ListableCommand = ListableCommand<Self::PipeableCommand>;
    type PipeableCommand = DefaultPipeableCommand<T, Self::Word, Self::Command>;
    type CompoundCommand = CompoundCommand<CompoundCommandKind<T, Self::Word, Self::Command>, Self::Redirect>;
    type Word            = TopLevelWord<T>;
    type Redirect        = Redirect<Self::Word>;
    type Error           = Void;

    /// Constructs a `Command::Job` node with the provided inputs if the command
    /// was delimited by an ampersand or the command itself otherwise.
    fn complete_command(&mut self,
                        _pre_cmd_comments: Vec<Newline>,
                        list: Self::CommandList,
                        separator: SeparatorKind,
                        _cmd_comment: Option<Newline>)
        -> ParseResult<Self::Command, Self::Error>
    {
        let cmd = match separator {
            SeparatorKind::Semi  |
            SeparatorKind::Other |
            SeparatorKind::Newline => Command::List(list),
            SeparatorKind::Amp => Command::Job(list),
        };

        Ok(TopLevelCommand(cmd))
    }

    /// Constructs a `Command::List` node with the provided inputs.
    fn and_or_list(&mut self,
              first: Self::ListableCommand,
              rest: Vec<(Vec<Newline>, AndOr<Self::ListableCommand>)>)
        -> ParseResult<Self::CommandList, Self::Error>
    {
        Ok(AndOrList {
            first: first,
            rest: rest.into_iter().map(|(_, c)| c).collect(),
        })
    }

    /// Constructs a `Command::Pipe` node with the provided inputs or a `Command::Simple`
    /// node if only a single command with no status inversion is supplied.
    fn pipeline(&mut self,
                bang: bool,
                cmds: Vec<(Vec<Newline>, Self::PipeableCommand)>)
        -> ParseResult<Self::ListableCommand, Self::Error>
    {
        debug_assert_eq!(cmds.is_empty(), false);
        let mut cmds: Vec<_> = cmds.into_iter().map(|(_, c)| c).collect();

        // Pipe is the only AST node which allows for a status
        // negation, so we are forced to use it even if we have a single
        // command. Otherwise there is no need to wrap it further.
        if bang || cmds.len() > 1 {
            cmds.shrink_to_fit();
            Ok(ListableCommand::Pipe(bang, cmds))
        } else {
            Ok(ListableCommand::Single(cmds.pop().unwrap()))
        }
    }

    /// Constructs a `Command::Simple` node with the provided inputs.
    fn simple_command(&mut self,
                      env_vars: Vec<(String, Option<Self::Word>)>,
                      mut cmd: Option<(Self::Word, Vec<Self::Word>)>,
                      mut redirects: Vec<Self::Redirect>)
        -> ParseResult<Self::PipeableCommand, Self::Error>
    {
        redirects.shrink_to_fit();

        if let Some(&mut (_, ref mut args)) = cmd.as_mut() {
            args.shrink_to_fit();
        }

        Ok(PipeableCommand::Simple(Box::new(SimpleCommand {
            cmd: cmd,
            vars: env_vars.into_iter().map(|(k, v)| (k.into(), v)).collect(),
            io: redirects,
        })))
    }

    /// Constructs a `CompoundCommand::Brace` node with the provided inputs.
    fn brace_group(&mut self,
                   cmd_group: CommandGroup<Self::Command>,
                   mut redirects: Vec<Self::Redirect>)
        -> ParseResult<Self::CompoundCommand, Self::Error>
    {
        let mut cmds = cmd_group.commands;
        cmds.shrink_to_fit();
        redirects.shrink_to_fit();
        Ok(CompoundCommand {
            kind: CompoundCommandKind::Brace(cmds),
            io: redirects,
        })
    }

    /// Constructs a `CompoundCommand::Subshell` node with the provided inputs.
    fn subshell(&mut self,
                cmd_group: CommandGroup<Self::Command>,
                mut redirects: Vec<Self::Redirect>)
        -> ParseResult<Self::CompoundCommand, Self::Error>
    {
        let mut cmds = cmd_group.commands;
        cmds.shrink_to_fit();
        redirects.shrink_to_fit();
        Ok(CompoundCommand {
            kind: CompoundCommandKind::Subshell(cmds),
            io: redirects,
        })
    }

    /// Constructs a `CompoundCommand::Loop` node with the provided inputs.
    fn loop_command(&mut self,
                    kind: LoopKind,
                    guard_body_pair: GuardBodyPairGroup<Self::Command>,
                    mut redirects: Vec<Self::Redirect>)
        -> ParseResult<Self::CompoundCommand, Self::Error>
    {
        let mut guard = guard_body_pair.guard.commands;
        let mut body = guard_body_pair.body.commands;

        guard.shrink_to_fit();
        body.shrink_to_fit();
        redirects.shrink_to_fit();

        let guard_body_pair = ast::GuardBodyPair {
            guard: guard,
            body: body,
        };

        let loop_cmd = match kind {
            LoopKind::While => CompoundCommandKind::While(guard_body_pair),
            LoopKind::Until => CompoundCommandKind::Until(guard_body_pair),
        };

        Ok(CompoundCommand {
            kind: loop_cmd,
            io: redirects,
        })
    }

    /// Constructs a `CompoundCommand::If` node with the provided inputs.
    fn if_command(&mut self,
                  fragments: IfFragments<Self::Command>,
                  mut redirects: Vec<Self::Redirect>)
        -> ParseResult<Self::CompoundCommand, Self::Error>
    {
        let IfFragments { conditionals, else_branch } = fragments;

        let conditionals = conditionals.into_iter()
            .map(|gbp| {
                let mut guard = gbp.guard.commands;
                let mut body = gbp.body.commands;

                guard.shrink_to_fit();
                body.shrink_to_fit();

                ast::GuardBodyPair {
                    guard: guard,
                    body: body,
                }
            })
            .collect();

        let else_branch = else_branch.map(|CommandGroup { commands: mut els, .. }| {
            els.shrink_to_fit();
            els
        });

        redirects.shrink_to_fit();

        Ok(CompoundCommand {
            kind: CompoundCommandKind::If {
                conditionals: conditionals,
                else_branch: else_branch,
            },
            io: redirects,
        })
    }

    /// Constructs a `CompoundCommand::For` node with the provided inputs.
    fn for_command(&mut self,
                   fragments: ForFragments<Self::Word, Self::Command>,
                   mut redirects: Vec<Self::Redirect>)
        -> ParseResult<Self::CompoundCommand, Self::Error>
    {
        let words = fragments.words.map(|(_, mut words, _)| {
            words.shrink_to_fit();
            words
        });

        let mut body = fragments.body.commands;
        body.shrink_to_fit();
        redirects.shrink_to_fit();

        Ok(CompoundCommand {
            kind: CompoundCommandKind::For {
                var: fragments.var.into(),
                words: words,
                body: body,
            },
            io: redirects
        })
    }

    /// Constructs a `CompoundCommand::Case` node with the provided inputs.
    fn case_command(&mut self,
                    fragments: CaseFragments<Self::Word, Self::Command>,
                    mut redirects: Vec<Self::Redirect>)
        -> ParseResult<Self::CompoundCommand, Self::Error>
    {
        use ast::PatternBodyPair;

        let arms = fragments.arms.into_iter().map(|arm| {
            let mut patterns = arm.patterns.pattern_alternatives;
            patterns.shrink_to_fit();

            let mut body = arm.body.commands;
            body.shrink_to_fit();

            PatternBodyPair {
                patterns: patterns,
                body: body,
            }
        }).collect();

        redirects.shrink_to_fit();
        Ok(CompoundCommand {
            kind: CompoundCommandKind::Case {
                word: fragments.word,
                arms: arms,
            },
            io: redirects,
        })
    }

    /// Converts a `CompoundCommand` into a `PipeableCommand`.
    fn compound_command_as_pipeable(&mut self,
                                    cmd: Self::CompoundCommand)
        -> ParseResult<Self::PipeableCommand, Self::Error>
    {
        Ok(PipeableCommand::Compound(Box::new(cmd)))
    }

    /// Constructs a `Command::FunctionDef` node with the provided inputs.
    fn function_declaration(&mut self,
                            name: String,
                            _post_name_comments: Vec<Newline>,
                            body: Self::CompoundCommand)
        -> ParseResult<Self::PipeableCommand, Self::Error>
    {
        Ok(PipeableCommand::FunctionDef(name.into(), Rc::new(body)))
    }

    /// Ignored by the builder.
    fn comments(&mut self, _comments: Vec<Newline>) -> ParseResult<(), Self::Error> {
        Ok(())
    }

    /// Constructs a `ast::Word` from the provided input.
    fn word(&mut self, kind: ComplexWordKind<Self::Command>) -> ParseResult<Self::Word, Self::Error> {
        use ast::builder::ParameterSubstitutionKind::*;

        macro_rules! map {
            ($pat:expr) => {
                match $pat {
                    Some(w) => Some(try!(self.word(w))),
                    None => None,
                }
            }
        }

        fn map_arith<T: From<String>>(kind: Arithmetic) -> Arithmetic<T> {
            use ast::Arithmetic::*;
            match kind {
                Var(v)           => Var(v.into()),
                Literal(l)       => Literal(l.into()),
                Pow(a, b)        => Pow(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                PostIncr(p)      => PostIncr(p.into()),
                PostDecr(p)      => PostDecr(p.into()),
                PreIncr(p)       => PreIncr(p.into()),
                PreDecr(p)       => PreDecr(p.into()),
                UnaryPlus(a)     => UnaryPlus(Box::new(map_arith(*a))),
                UnaryMinus(a)    => UnaryMinus(Box::new(map_arith(*a))),
                LogicalNot(a)    => LogicalNot(Box::new(map_arith(*a))),
                BitwiseNot(a)    => BitwiseNot(Box::new(map_arith(*a))),
                Mult(a, b)       => Mult(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                Div(a, b)        => Div(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                Modulo(a, b)     => Modulo(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                Add(a, b)        => Add(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                Sub(a, b)        => Sub(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                ShiftLeft(a, b)  => ShiftLeft(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                ShiftRight(a, b) => ShiftRight(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                Less(a, b)       => Less(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                LessEq(a, b)     => LessEq(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                Great(a, b)      => Great(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                GreatEq(a, b)    => GreatEq(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                Eq(a, b)         => Eq(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                NotEq(a, b)      => NotEq(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                BitwiseAnd(a, b) => BitwiseAnd(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                BitwiseXor(a, b) => BitwiseXor(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                BitwiseOr(a, b)  => BitwiseOr(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                LogicalAnd(a, b) => LogicalAnd(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                LogicalOr(a, b)  => LogicalOr(Box::new(map_arith(*a)), Box::new(map_arith(*b))),
                Ternary(a, b, c) =>
                    Ternary(Box::new(map_arith(*a)), Box::new(map_arith(*b)), Box::new(map_arith(*c))),
                Assign(v, a) => Assign(v.into(), Box::new(map_arith(*a))),
                Sequence(ariths) => Sequence(ariths.into_iter().map(map_arith).collect()),
            }
        }

        let map_param = |kind: Parameter| -> Parameter<T> {
            use ast::Parameter::*;
            match kind {
                At            => At,
                Star          => Star,
                Pound         => Pound,
                Question      => Question,
                Dash          => Dash,
                Dollar        => Dollar,
                Bang          => Bang,
                Positional(p) => Positional(p),
                Var(v)        => Var(v.into()),
            }
        };

        let mut map_simple = |kind| {
            let simple = match kind {
                SimpleWordKind::Literal(s)      => SimpleWord::Literal(s.into()),
                SimpleWordKind::Escaped(s)      => SimpleWord::Escaped(s.into()),
                SimpleWordKind::Param(p)        => SimpleWord::Param(map_param(p)),
                SimpleWordKind::Star            => SimpleWord::Star,
                SimpleWordKind::Question        => SimpleWord::Question,
                SimpleWordKind::SquareOpen      => SimpleWord::SquareOpen,
                SimpleWordKind::SquareClose     => SimpleWord::SquareClose,
                SimpleWordKind::Tilde           => SimpleWord::Tilde,
                SimpleWordKind::Colon           => SimpleWord::Colon,

                SimpleWordKind::CommandSubst(c) => SimpleWord::Subst(
                    Box::new(ParameterSubstitution::Command(c.commands))
                ),

                SimpleWordKind::Subst(s) => {
                    // Force a move out of the boxed substitution. For some reason doing
                    // the deref in the match statment gives a strange borrow failure
                    let s = *s;
                    let subst = match s {
                        Len(p) => ParameterSubstitution::Len(map_param(p)),
                        Command(c) => ParameterSubstitution::Command(c.commands),
                        Arith(a) => ParameterSubstitution::Arith(a.map(map_arith)),
                        Default(c, p, w) =>
                            ParameterSubstitution::Default(c, map_param(p), map!(w)),
                        Assign(c, p, w) =>
                            ParameterSubstitution::Assign(c, map_param(p), map!(w)),
                        Error(c, p, w) =>
                            ParameterSubstitution::Error(c, map_param(p), map!(w)),
                        Alternative(c, p, w) =>
                            ParameterSubstitution::Alternative(c, map_param(p), map!(w)),
                        RemoveSmallestSuffix(p, w) =>
                            ParameterSubstitution::RemoveSmallestSuffix(map_param(p), map!(w)),
                        RemoveLargestSuffix(p, w)  =>
                            ParameterSubstitution::RemoveLargestSuffix(map_param(p), map!(w)),
                        RemoveSmallestPrefix(p, w) =>
                            ParameterSubstitution::RemoveSmallestPrefix(map_param(p), map!(w)),
                        RemoveLargestPrefix(p, w)  =>
                            ParameterSubstitution::RemoveLargestPrefix(map_param(p), map!(w)),
                    };
                    SimpleWord::Subst(Box::new(subst))
                },
            };
            Ok(simple)
        };

        let mut map_word = |kind| {
            let word = match kind {
                WordKind::Simple(s)       => Word::Simple(try!(map_simple(s))),
                WordKind::SingleQuoted(s) => Word::SingleQuoted(s.into()),
                WordKind::DoubleQuoted(v) => Word::DoubleQuoted(try!(
                    v.into_iter()
                     .map(&mut map_simple)
                     .collect::<ParseResult<Vec<_>, _>>()
                )),
            };
            Ok(word)
        };

        let word = match compress(kind) {
            ComplexWordKind::Single(s)     => ComplexWord::Single(try!(map_word(s))),
            ComplexWordKind::Concat(words) => ComplexWord::Concat(try!(
                    words.into_iter()
                         .map(map_word)
                         .collect::<ParseResult<Vec<_>, _>>()
            )),
        };

        Ok(TopLevelWord(word))
    }

    /// Constructs a `ast::Redirect` from the provided input.
    fn redirect(&mut self,
                kind: RedirectKind<Self::Word>)
        -> ParseResult<Self::Redirect, Self::Error>
    {
        let io = match kind {
            RedirectKind::Read(fd, path)      => Redirect::Read(fd, path),
            RedirectKind::Write(fd, path)     => Redirect::Write(fd, path),
            RedirectKind::ReadWrite(fd, path) => Redirect::ReadWrite(fd, path),
            RedirectKind::Append(fd, path)    => Redirect::Append(fd, path),
            RedirectKind::Clobber(fd, path)   => Redirect::Clobber(fd, path),
            RedirectKind::Heredoc(fd, body)   => Redirect::Heredoc(fd, body),
            RedirectKind::DupRead(src, dst)   => Redirect::DupRead(src, dst),
            RedirectKind::DupWrite(src, dst)  => Redirect::DupWrite(src, dst),
        };

        Ok(io)
    }
}

struct Coalesce<I: Iterator, F> {
    iter: I,
    cur: Option<I::Item>,
    func: F,
}

impl<I: Iterator, F> Coalesce<I, F> {
    fn new(iter: I, func: F) -> Self {
        Coalesce {
            iter: iter,
            cur: None,
            func: func,
        }
    }
}

type CoalesceResult<T> = Result<T, (T, T)>;
impl<I, F> Iterator for Coalesce<I, F>
    where I: Iterator,
          F: FnMut(I::Item, I::Item) -> CoalesceResult<I::Item>
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.cur.take().or_else(|| self.iter.next());
        let (mut left, mut right) = match (cur, self.iter.next()) {
            (Some(l), Some(r)) => (l, r),
            (Some(l), None) |
            (None, Some(l)) => return Some(l),
            (None, None) => return None,
        };

        loop {
            match (self.func)(left, right) {
                Ok(combined) => match self.iter.next() {
                    Some(next) => {
                        left = combined;
                        right = next;
                    },
                    None => return Some(combined),
                },

                Err((left, right)) => {
                    debug_assert!(self.cur.is_none());
                    self.cur = Some(right);
                    return Some(left);
                },
            }
        }
    }
}

fn compress<C>(word: ComplexWordKind<C>) -> ComplexWordKind<C> {
    use ast::builder::ComplexWordKind::*;
    use ast::builder::SimpleWordKind::*;
    use ast::builder::WordKind::*;

    fn coalesce_simple<C>(a: SimpleWordKind<C>, b: SimpleWordKind<C>)
        -> CoalesceResult<SimpleWordKind<C>>
    {
        match (a, b) {
            (Literal(mut a), Literal(b)) => {
                a.push_str(&b);
                Ok(Literal(a))
            },
            (a, b) => Err((a, b)),
        }
    }

    fn coalesce_word<C>(a: WordKind<C>, b: WordKind<C>) -> CoalesceResult<WordKind<C>> {
        match (a, b) {
            (Simple(a), Simple(b)) => coalesce_simple(a, b).map(Simple)
                                                           .map_err(|(a, b)| (Simple(a), Simple(b))),
            (SingleQuoted(mut a), SingleQuoted(b)) => {
                a.push_str(&b);
                Ok(SingleQuoted(a))
            },
            (DoubleQuoted(a), DoubleQuoted(b)) => {
                let quoted = Coalesce::new(a.into_iter().chain(b), coalesce_simple).collect();
                Ok(DoubleQuoted(quoted))
            },
            (a, b) => Err((a, b)),
        }
    }

    match word {
        Single(s) => Single(match s {
            s@Simple(_) |
            s@SingleQuoted(_) => s,
            DoubleQuoted(v) => DoubleQuoted(Coalesce::new(v.into_iter(), coalesce_simple).collect()),
        }),
        Concat(v) => {
            let mut body: Vec<_> = Coalesce::new(v.into_iter(), coalesce_word).collect();
            if body.len() == 1 {
                Single(body.pop().unwrap())
            } else {
                Concat(body)
            }
        }
    }
}

