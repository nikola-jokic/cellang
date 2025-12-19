use miette::{Diagnostic, SourceSpan};
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
