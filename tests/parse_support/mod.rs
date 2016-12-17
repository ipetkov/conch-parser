// Certain helpers may only be used by specific tests,
// suppress dead_code warnings since the compiler can't
// see our intent
#![allow(dead_code)]

use conch_parser::ast::*;
use conch_parser::ast::Command::*;
use conch_parser::ast::ComplexWord::*;
use conch_parser::ast::PipeableCommand::*;
use conch_parser::ast::SimpleWord::*;
use conch_parser::lexer::Lexer;
use conch_parser::parse::*;
use conch_parser::token::Token;

pub fn lit(s: &str) -> DefaultWord {
    Word::Simple(Literal(String::from(s)))
}

pub fn escaped(s: &str) -> DefaultWord {
    Word::Simple(Escaped(String::from(s)))
}

pub fn subst(s: DefaultParameterSubstitution) -> DefaultWord {
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

pub fn word_subst(s: DefaultParameterSubstitution) -> TopLevelWord {
    TopLevelWord(Single(subst(s)))
}

pub fn word_param(p: DefaultParameter) -> TopLevelWord {
    TopLevelWord(Single(Word::Simple(Param(p))))
}

pub fn make_parser(src: &str) -> DefaultParser<Lexer<::std::str::Chars>> {
    DefaultParser::new(Lexer::new(src.chars()))
}

pub fn make_parser_from_tokens(src: Vec<Token>) -> DefaultParser<::std::vec::IntoIter<Token>> {
    DefaultParser::new(src.into_iter())
}

pub fn cmd_args_simple(cmd: &str, args: &[&str]) -> Box<DefaultSimpleCommand> {
    let cmd = word(cmd);
    let args = args.iter().map(|&a| word(a)).collect();

    Box::new(SimpleCommand {
        cmd: Some((cmd, args)),
        vars: vec!(),
        io: vec!(),
    })
}

pub fn cmd_simple(cmd: &str) -> Box<DefaultSimpleCommand> {
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

pub fn cmd_from_simple(cmd: DefaultSimpleCommand) -> TopLevelCommand {
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
