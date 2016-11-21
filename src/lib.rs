//! A library for parsing programs written in the shell programming language.
#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]

#![cfg_attr(all(not(test), feature = "clippy"), deny(print_stdout))]
#![cfg_attr(feature = "clippy", deny(wrong_self_convention))]

#![deny(missing_copy_implementations)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(trivial_casts)]
#![deny(trivial_numeric_casts)]
#![deny(unused_import_braces)]
#![deny(unused_qualifications)]

#![forbid(unsafe_code)]

// Nightly optimizations that don't need their own feature
#![cfg_attr(feature = "nightly", feature(fused))]

macro_rules! if_nightly {
    ($($i:item)*) => ($(
        #[cfg(feature = "nightly")]
        $i
    )*)
}

extern crate void;

pub mod ast;
pub mod lexer;
pub mod parse;
pub mod token;
