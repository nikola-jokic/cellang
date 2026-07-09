//! # Cellang Parser Facade API Contract
//!
//! ## Canonical API Contract
//!
//! The following functions define the **canonical** parser facade surface:
//!
//! | **Stage**         | **Canonical Path**              | **Function Signature**                                                    | **Description**                                          |
//! |-------------------|---------------------------------|---------------------------------------------------------------------------|----------------------------------------------------------|
//! | Parse             | `cellang::parser::parse`        | `fn parse(input: &str) -> Result<ParseResult, Error>`                    | Parse source text into Rowan CST (concrete syntax tree) |
//! | Lower to HIR      | `cellang::parser::lower`        | `fn lower(parse_result: &ParseResult) -> Result<Expr, LowerError>`       | Lower CST to HIR (high-level intermediate representation)|
//! | Lower from source | `cellang::parser::lower_source` | `fn lower_source(source: &str) -> Result<Expr, LowerError>`              | Parse + lower in one step                                |
//! | Type-check        | `cellang::parser::type_check`   | `fn type_check(env: &Env, expr: &Expr) -> Result<TypedExpr, RuntimeError>` | Type-check HIR expression against environment          |
//! | Eval from source  | `cellang::parser::eval`         | `fn eval(runtime: &Runtime, source: &str) -> Result<Value, RuntimeError>`| Parse, lower, type-check, and evaluate source string     |
//! | Eval HIR AST      | `cellang::parser::eval_ast`     | `fn eval_ast(runtime: &Runtime, expr: &Expr) -> Result<Value, RuntimeError>` | Evaluate HIR expression directly                    |

pub mod ast;
mod builtins;
mod derive;
pub mod env;
pub mod error;
pub mod hir;
pub mod interpreter;
pub mod lexer;
pub mod macros;
pub mod runtime;
pub mod syntax;
pub mod types;
pub mod value;
#[cfg(all(feature = "wasm", target_arch = "wasm32"))]
pub mod wasm;

/// Canonical parser facade providing intuitive access to the full parsing pipeline.
///
/// This module re-exports the complete parse → lower → type-check → eval pipeline
/// as a unified API surface. New code should prefer these canonical paths over
/// the nested module paths (e.g., `cellang::parser::parse` instead of
/// `cellang::syntax::parser::parse`).
///
/// ## Pipeline Overview
///
/// The CEL parsing pipeline consists of these stages:
///
/// 1. **Parse** ([`parse`]) - Tokenize and build concrete syntax tree (CST)
/// 2. **Lower** ([`lower`], [`lower_source`]) - Convert CST to high-level IR (HIR)
/// 3. **Type-check** ([`type_check`]) - Validate types and build typed expression
/// 4. **Evaluate** ([`eval`], [`eval_ast`]) - Execute the expression
///
/// ## Quick Start
///
/// ```rust
/// use cellang::parser::{eval, lower_source};
/// use cellang::Runtime;
///
/// // Direct evaluation (parse + lower + type-check + eval in one step)
/// let runtime = Runtime::builder().build();
/// let result = eval(&runtime, "1 + 2").unwrap();
///
/// // Manual pipeline control (parse and lower separately)
/// let hir_expr = lower_source("users.size() > 0").unwrap();
/// // ... inspect or transform HIR before evaluation
/// ```
pub mod parser {
    pub use crate::ast::type_check;
    pub use crate::hir::{Atom, BinaryOp, Expr, UnaryOp, lower, lower_source};
    pub use crate::interpreter::{eval, eval_ast};
    pub use crate::syntax::ast::CelNode;
    pub use crate::syntax::parse::ParseResult;
    pub use crate::syntax::parser::parse;
}

pub use crate::env::*;
pub use ast::*;
pub use derive::CelType;
pub use error::*;
pub use interpreter::*;
pub use lexer::*;
pub use macros::*;
pub use runtime::*;
pub use syntax::*;
pub use types::*;
pub use value::*;
#[cfg(all(feature = "wasm", target_arch = "wasm32"))]
pub use wasm::*;

#[cfg(feature = "derive")]
pub use cellang_macros::CelStruct;
