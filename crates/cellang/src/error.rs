use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

#[derive(Debug, Error, Diagnostic, Clone)]
#[error("ParserError: {message}")]
#[diagnostic(
    code(workflow_parser::parser_error),
    help(
        "Learn more about workflow syntax on https://docs.bountyhub.org/workflows/syntax-reference"
    )
)]
pub struct SyntaxError {
    #[source_code]
    pub source_code: String,

    #[label("this")]
    pub span: SourceSpan,

    pub message: String,

    pub help: Option<String>,
}
