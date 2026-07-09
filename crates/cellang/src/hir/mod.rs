//! High-level Intermediate Representation (HIR) layer: Semantic lowering from CST.
//!
//! This module forms the **second stage** of the CEL pipeline:
//! CST (`crate::syntax`) → HIR (this module) → Type Check (`crate::ast`) → Eval (`crate::interpreter`)
//!
//! The HIR strips away syntactic noise (grouping parentheses, whitespace, etc.) from the CST
//! and produces a clean, owned data structure suitable for semantic analysis and type checking.
//! Unlike the CST, the HIR does not maintain parser lifetimes, making it ideal for persistent
//! intermediate representations.
//!
//! **Module boundary**: This module is internal to the parser pipeline. External code should use
//! the public API facade at `crate::parser::lower` or `crate::parser::lower_source` rather than
//! importing directly from this module.

pub mod expr;
pub mod lower;

pub use expr::{Atom, BinaryOp, Expr, UnaryOp};
pub use lower::{LowerError, LowerErrorKind, lower, lower_source};
