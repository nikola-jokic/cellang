#![deny(clippy::match_same_arms)]

pub mod ast;
mod builtins;
mod derive;
pub mod env;
pub mod error;
pub mod interpreter;
pub mod lexer;
pub mod macros;
pub mod parser;
pub mod runtime;
pub mod types;
pub mod value;
#[cfg(all(feature = "wasm", target_arch = "wasm32"))]
pub mod wasm;

pub use crate::env::*;
pub use ast::*;
pub use derive::CelType;
pub use error::*;
pub use interpreter::*;
pub use lexer::*;
pub use macros::*;
pub use parser::*;
pub use runtime::*;
pub use types::*;
pub use value::*;
#[cfg(all(feature = "wasm", target_arch = "wasm32"))]
pub use wasm::*;

#[cfg(feature = "derive")]
pub use cellang_macros::CelStruct;
