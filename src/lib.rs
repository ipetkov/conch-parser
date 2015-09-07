//! A library for parsing, executing, and analyzing programs
//! written in the shell programming language.

#![cfg_attr(feature = "runtime", feature(into_raw_os))]
#![cfg_attr(feature = "runtime", feature(zero_one))]

#[cfg(feature = "runtime")] extern crate glob;
extern crate itertools;
#[cfg(feature = "runtime")] extern crate libc;
extern crate void;

#[cfg(feature = "runtime")]
pub mod runtime;
pub mod syntax;
