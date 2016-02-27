//! A module for anything related to shell syntax, such as tokenizing,
//! lexing, and parsing source into Abstract Syntax Trees.

#![forbid(unsafe_code)]
#![forbid(unstable_features)]

pub mod ast;
pub mod lexer;
pub mod parse;
pub mod token;
