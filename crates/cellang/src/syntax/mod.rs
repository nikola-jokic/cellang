//! Concrete Syntax Tree (CST) layer: Lossless Rowan-based parsing.
//!
//! This module forms the **first stage** of the CEL pipeline:
//! CST (this module) → HIR (`crate::hir`) → Type Check (`crate::ast`) → Eval (`crate::interpreter`)
//!
//! The CST preserves all source information (whitespace, comments, error tokens) making it ideal
//! for IDE/LSP tooling and error recovery. The Rowan tree structure supports incremental parsing
//! and exact source location tracking for diagnostics.
//!
//! **Module boundary**: This module is internal to the parser pipeline. External code should use
//! the public API facade at `crate::parser::parse` rather than importing directly from this module.

pub mod ast;
pub mod bridge;
pub mod error;
pub mod inspection;
pub mod kind;
pub mod language;
pub mod parse;
pub mod parser;

#[cfg(test)]
mod parity_tests;

pub use self::ast::*;
pub use self::error::Error;
pub use self::inspection::*;
pub use self::kind::SyntaxKind;
pub use self::language::CelLanguage;
pub use self::parse::ParseResult;
