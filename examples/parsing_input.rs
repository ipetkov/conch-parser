#![cfg_attr(feature = "nightly", feature(io))]

extern crate conch_parser;

use conch_parser::lexer::Lexer;
use conch_parser::parse::DefaultParser;

use std::io::{self, Read};

#[cfg(feature = "nightly")]
fn run_with_stdin<F>(f: F) where F: FnOnce(&mut Iterator<Item = char>) {
    // Read::chars is currently feature gated
    let mut stdin = io::stdin().chars().map(Result::unwrap);
    f(&mut stdin);
}

#[cfg(not(feature = "nightly"))]
fn run_with_stdin<F>(f: F) where F: FnOnce(&mut Iterator<Item = char>) {
    // There's no "easy" way to convert stdin into a char iterator on stable
    // (and by easy I mean without writing our own iterator wrapper) so
    // we'll just read all input into memory at once to get the point across.
    println!("Note: buffering in all input before parsing");
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut stdin = input.chars();
    f(&mut stdin);
}


fn main() {
    run_with_stdin(|stdin| {
        // Initialize our token lexer and shell parser with the program's input
        let lex = Lexer::new(stdin);
        let parser = DefaultParser::new(lex);

        // Parse our input!
        for t in parser {
            println!("{:?}", t);
        }
    });
}
