/// Error represents parse errors in the CEL syntax tree.
/// Preserves source spans for precise LSP diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    /// Human-readable error message
    pub message: String,
    /// Optional source span (byte offset, length) for diagnostics
    pub span: Option<(usize, usize)>,
}

impl Error {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: None,
        }
    }

    pub fn with_span(
        message: impl Into<String>,
        offset: usize,
        length: usize,
    ) -> Self {
        Self {
            message: message.into(),
            span: Some((offset, length)),
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for Error {}
