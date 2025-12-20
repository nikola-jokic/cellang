use crate::value::ValueError;
use miette::{Diagnostic, SourceSpan};
use std::error::Error as StdError;
use thiserror::Error;

#[derive(Debug, Error, Diagnostic, Clone)]
#[error("ParserError: {message}")]
#[diagnostic(code(cellang::syntax_error))]
pub struct SyntaxError {
    #[source_code]
    pub source_code: String,

    #[label("this")]
    pub span: SourceSpan,

    pub message: String,

    #[help]
    pub help: Option<String>,
}

#[derive(Debug, Error, Diagnostic, Clone)]
#[error("EnvError: {message}")]
#[diagnostic(code(cellang::env_error))]
pub struct EnvError {
    message: String,
}

impl EnvError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

#[derive(Debug, Error, Diagnostic)]
#[error("RuntimeError: {message}")]
#[diagnostic(code(cellang::runtime_error))]
pub struct RuntimeError {
    message: String,
    #[source]
    source: Option<Box<dyn StdError + Send + Sync>>, 
}

impl RuntimeError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            source: None,
        }
    }

    pub fn with_source<E>(message: impl Into<String>, source: E) -> Self
    where
        E: StdError + Send + Sync + 'static,
    {
        Self {
            message: message.into(),
            source: Some(Box::new(source)),
        }
    }

    pub fn wrong_arity(
        name: &str,
        expected: usize,
        actual: usize,
    ) -> Self {
        RuntimeError::new(format!(
            "Function '{name}' expected {expected} arguments but received {actual}"
        ))
    }

    pub fn missing_identifier(name: &str) -> Self {
        RuntimeError::new(format!("Identifier '{name}' is not defined"))
    }

    pub fn argument(
        name: &str,
        position: usize,
        err: ValueError,
    ) -> Self {
        RuntimeError::with_source(
            format!("Invalid argument {position} for function '{name}'"),
            err,
        )
    }
}

impl From<ValueError> for RuntimeError {
    fn from(value: ValueError) -> Self {
        RuntimeError::with_source(value.to_string(), value)
    }
}

impl From<SyntaxError> for RuntimeError {
    fn from(error: SyntaxError) -> Self {
        RuntimeError::with_source(error.to_string(), error)
    }
}
