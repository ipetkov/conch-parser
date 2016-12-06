extern crate conch_parser;

use conch_parser::ast::*;
use conch_parser::ast::PipeableCommand::*;
use conch_parser::ast::Redirect::*;

mod parse_support;
use parse_support::*;

pub struct SimpleCommandFragments {
    cmd: Option<(TopLevelWord, Vec<TopLevelWord>)>,
    vars: Vec<(String, Option<TopLevelWord>)>,
    io: Vec<Redirect>,
}

pub fn sample_simple_command() -> SimpleCommandFragments {
    SimpleCommandFragments {
        cmd: Some((word("foo"), vec!(
            word("bar"),
            word("baz"),
        ))),
        vars: vec!(
            (String::from("var"), Some(word("val"))),
            (String::from("ENV"), Some(word("true"))),
            (String::from("BLANK"), None),
        ),
        io: vec!(
            Clobber(Some(2), word("clob")),
            ReadWrite(Some(3), word("rw")),
            Read(None, word("in")),
        ),
    }
}

#[test]
fn test_simple_command_valid_assignments_at_start_of_command() {
    let mut p = make_parser("var=val ENV=true BLANK= foo bar baz");
    let SimpleCommandFragments { cmd, vars, ..} = sample_simple_command();
    let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: vec!() }));
    assert_eq!(correct, p.simple_command().unwrap());
}

#[test]
fn test_simple_command_assignments_after_start_of_command_should_be_args() {
    let mut p = make_parser("var=val ENV=true BLANK= foo var2=val2 bar baz var3=val3");
    let SimpleCommandFragments { cmd, vars, ..} = sample_simple_command();
    let (cmd, mut args) = cmd.unwrap();
    args.insert(0, word("var2=val2"));
    args.push(word("var3=val3"));
    let correct = Simple(Box::new(SimpleCommand { cmd: Some((cmd, args)), vars: vars, io: vec!() }));
    assert_eq!(correct, p.simple_command().unwrap());
}

#[test]
fn test_simple_command_redirections_at_start_of_command() {
    let mut p = make_parser("2>|clob 3<>rw <in var=val ENV=true BLANK= foo bar baz");
    let SimpleCommandFragments { cmd, vars, io } = sample_simple_command();
    let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: io }));
    assert_eq!(correct, p.simple_command().unwrap());
}

#[test]
fn test_simple_command_redirections_at_end_of_command() {
    let mut p = make_parser("var=val ENV=true BLANK= foo bar baz 2>|clob 3<>rw <in");
    let SimpleCommandFragments { cmd, vars, io } = sample_simple_command();
    let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: io }));
    assert_eq!(correct, p.simple_command().unwrap());
}

#[test]
fn test_simple_command_redirections_throughout_the_command() {
    let mut p = make_parser("2>|clob var=val 3<>rw ENV=true BLANK= foo bar <in baz 4>&-");
    let SimpleCommandFragments { cmd, vars, mut io } = sample_simple_command();
    io.push(DupWrite(Some(4), word("-")));
    let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: io }));
    assert_eq!(correct, p.simple_command().unwrap());
}

