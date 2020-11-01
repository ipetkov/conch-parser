#![deny(rust_2018_idioms)]
#![recursion_limit = "128"]

use conch_parser::ast::builder::*;
use conch_parser::parse::*;

mod parse_support;
use crate::parse_support::*;

#[test]
fn test_parser_should_yield_none_after_error() {
    let mut iter = make_parser("foo && ||").into_iter();
    let _ = iter.next().expect("failed to get error").unwrap_err();
    assert_eq!(iter.next(), None);
}

#[test]
fn test_comment_cannot_start_mid_whitespace_delimited_word() {
    let mut p = make_parser("hello#world");
    let w = p.word().unwrap().expect("no valid word was discovered");
    assert_eq!(w, word("hello#world"));
}

#[test]
fn test_braces_literal_unless_brace_group_expected() {
    let source = "echo {} } {";
    let mut p = make_parser(source);
    assert_eq!(p.word().unwrap().unwrap(), word("echo"));
    assert_eq!(p.word().unwrap().unwrap(), word("{}"));
    assert_eq!(p.word().unwrap().unwrap(), word("}"));
    assert_eq!(p.word().unwrap().unwrap(), word("{"));

    let correct = Some(cmd_args("echo", &["{}", "}", "{"]));
    assert_eq!(correct, make_parser(source).complete_command().unwrap());
}

#[test]
fn ensure_parser_could_be_send_and_sync() {
    use conch_parser::token::Token;

    fn send_and_sync<T: Send + Sync>() {}
    send_and_sync::<Parser<std::vec::IntoIter<Token>, ArcBuilder>>();
}
