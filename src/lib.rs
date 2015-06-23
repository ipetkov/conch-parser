//! A library for parsing, executing, and analyzing programs
//! written in the shell programming language.

#![feature(slice_patterns)]

#![cfg_attr(test, feature(box_patterns))]
#![cfg_attr(test, feature(slice_patterns))]

pub mod syntax;
