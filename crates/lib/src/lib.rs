#![deny(clippy::match_same_arms)]

pub mod environment;
pub mod functions;
pub mod interpreter;
pub mod lexer;
pub mod parser;
pub mod types;

pub use environment::*;
pub use interpreter::*;
pub use lexer::*;
pub use parser::*;
pub use types::*;
