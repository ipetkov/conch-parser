//! A library for parsing, executing, and analyzing programs
//! written in the shell programming language.

#![deny(unused_import_braces)]
#![deny(unused_qualifications)]

#![cfg_attr(feature = "runtime", feature(zero_one))]
#![cfg_attr(all(windows, feature = "runtime"), feature(unique))]

// Windows only libs
#[cfg(all(windows, feature = "runtime"))] extern crate kernel32;
#[cfg(all(windows, feature = "runtime"))] extern crate winapi;

#[cfg(feature = "runtime")] extern crate glob;
#[cfg(feature = "runtime")] extern crate libc;
extern crate void;

#[cfg(feature = "runtime")]
pub mod runtime;
pub mod syntax;
