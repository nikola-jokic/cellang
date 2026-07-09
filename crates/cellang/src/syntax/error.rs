/// Error represents parse errors in the CEL syntax tree.
/// This is a scaffolding stub; error reporting with source spans and diagnostics
/// will be implemented in subsequent tasks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    /// Human-readable error message
    pub message: String,
}

impl Error {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for Error {}
