use conch_parser::lexer::Lexer;
use conch_parser::parse::DefaultParser;
use owned_chars::OwnedCharsExt;

use std::io::{stdin, BufRead, BufReader};

fn main() {
    let stdin = BufReader::new(stdin())
        .lines()
        .map(Result::unwrap)
        .flat_map(|mut line| {
            line.push('\n'); // BufRead::lines unfortunately strips \n and \r\n
            line.into_chars()
        });

    // Initialize our token lexer and shell parser with the program's input
    let lex = Lexer::new(stdin);
    let parser = DefaultParser::new(lex);

    // Parse our input!
    for t in parser {
        println!("{:?}", t);
    }
}
