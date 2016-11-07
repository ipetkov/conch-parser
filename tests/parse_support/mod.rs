// Certain helpers may only be used by specific tests,
// suppress dead_code warnings since the compiler can't
// see our intent
#![allow(dead_code)]

use shell_lang::ast::*;
use shell_lang::ast::Command::*;
use shell_lang::ast::ComplexWord::*;
use shell_lang::ast::PipeableCommand::*;
use shell_lang::ast::SimpleWord::*;
use shell_lang::lexer::Lexer;
use shell_lang::parse::*;
use shell_lang::token::Token;

pub fn lit(s: &str) -> Word {
    Word::Simple(Literal(String::from(s)))
}

pub fn escaped(s: &str) -> Word {
    Word::Simple(Escaped(String::from(s)))
}

pub fn subst(s: ParameterSubstitution) -> Word {
    Word::Simple(Subst(Box::new(s)))
}

pub fn single_quoted(s: &str) -> TopLevelWord {
    TopLevelWord(Single(Word::SingleQuoted(String::from(s))))
}

pub fn double_quoted(s: &str) -> TopLevelWord {
    TopLevelWord(Single(Word::DoubleQuoted(vec!(Literal(String::from(s))))))
}

pub fn word(s: &str) -> TopLevelWord {
    TopLevelWord(Single(lit(s)))
}

pub fn word_escaped(s: &str) -> TopLevelWord {
    TopLevelWord(Single(escaped(s)))
}

pub fn word_subst(s: ParameterSubstitution) -> TopLevelWord {
    TopLevelWord(Single(subst(s)))
}

pub fn word_param(p: Parameter) -> TopLevelWord {
    TopLevelWord(Single(Word::Simple(Param(p))))
}

pub fn make_parser(src: &str) -> DefaultParser<Lexer<::std::str::Chars>> {
    DefaultParser::new(Lexer::new(src.chars()))
}

pub fn make_parser_from_tokens(src: Vec<Token>) -> DefaultParser<::std::vec::IntoIter<Token>> {
    DefaultParser::new(src.into_iter())
}

pub fn cmd_args_simple(cmd: &str, args: &[&str]) -> Box<SimpleCommand> {
    let cmd = word(cmd);
    let args = args.iter().map(|&a| word(a)).collect();

    Box::new(SimpleCommand {
        cmd: Some((cmd, args)),
        vars: vec!(),
        io: vec!(),
    })
}

pub fn cmd_simple(cmd: &str) -> Box<SimpleCommand> {
    cmd_args_simple(cmd, &[])
}

pub fn cmd_args(cmd: &str, args: &[&str]) -> TopLevelCommand {
    TopLevelCommand(List(CommandList {
        first: ListableCommand::Single(Simple(cmd_args_simple(cmd, args))),
        rest: vec!(),
    }))
}

pub fn cmd(cmd: &str) -> TopLevelCommand {
    cmd_args(cmd, &[])
}

pub fn cmd_from_simple(cmd: SimpleCommand) -> TopLevelCommand {
    TopLevelCommand(List(CommandList {
        first: ListableCommand::Single(Simple(Box::new(cmd))),
        rest: vec!(),
    }))
}

pub fn src(byte: usize, line: usize, col: usize) -> SourcePos {
    SourcePos {
        byte: byte,
        line: line,
        col: col,
    }
}
