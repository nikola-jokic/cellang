use cellang::{CompileError, RuntimeError, SyntaxError};
use lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range};

use crate::position::byte_range_to_lsp_range;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NormalizedSeverity {
    Error,
    Warning,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalizedDiagnostic {
    pub severity: NormalizedSeverity,
    pub message: String,
    pub range: Option<(usize, usize)>,
    pub source: Option<&'static str>,
}

impl NormalizedDiagnostic {
    #[must_use]
    pub fn new(
        severity: NormalizedSeverity,
        message: impl Into<String>,
        range: Option<(usize, usize)>,
        source: Option<&'static str>,
    ) -> Self {
        Self {
            severity,
            message: message.into(),
            range,
            source,
        }
    }

    #[must_use]
    pub fn to_lsp(&self, text: &str) -> Diagnostic {
        let range = match self.range {
            Some((start, end)) => byte_range_to_lsp_range(text, start, end),
            None => Range::new(Position::new(0, 0), Position::new(0, 0)),
        };

        Diagnostic {
            range,
            severity: Some(match self.severity {
                NormalizedSeverity::Error => DiagnosticSeverity::ERROR,
                NormalizedSeverity::Warning => DiagnosticSeverity::WARNING,
            }),
            code: None,
            code_description: None,
            source: self.source.map(str::to_string),
            message: self.message.clone(),
            related_information: None,
            tags: None,
            data: None,
        }
    }
}

impl From<&SyntaxError> for NormalizedDiagnostic {
    fn from(error: &SyntaxError) -> Self {
        let span = error.span();
        let start = span.offset();
        let end = start.saturating_add(span.len());
        Self::new(
            NormalizedSeverity::Error,
            error.message(),
            Some((start, end)),
            Some("parser"),
        )
    }
}

impl From<&RuntimeError> for NormalizedDiagnostic {
    fn from(error: &RuntimeError) -> Self {
        Self::new(
            NormalizedSeverity::Error,
            error.to_string(),
            None,
            Some("type-check/runtime"),
        )
    }
}

impl From<SyntaxError> for NormalizedDiagnostic {
    fn from(error: SyntaxError) -> Self {
        Self::from(&error)
    }
}

impl From<RuntimeError> for NormalizedDiagnostic {
    fn from(error: RuntimeError) -> Self {
        Self::from(&error)
    }
}

impl From<&CompileError> for NormalizedDiagnostic {
    fn from(error: &CompileError) -> Self {
        match error {
            CompileError::Syntax(syntax) => Self::from(syntax),
            CompileError::Type(runtime) => Self::from(runtime),
            CompileError::Lower(lower) => Self::new(
                NormalizedSeverity::Error,
                lower.message.clone(),
                lower.span,
                Some("lowering"),
            ),
        }
    }
}

impl From<CompileError> for NormalizedDiagnostic {
    fn from(error: CompileError) -> Self {
        Self::from(&error)
    }
}

#[cfg(test)]
mod normalize {
    use super::*;
    use cellang::SyntaxKind;
    use lsp_types::{Position, Range};
    use rowan::GreenNodeBuilder;

    #[test]
    fn syntax_error_with_span_preserves_range() {
        let error = SyntaxError::new(
            "abc +",
            (4usize, 1usize).into(),
            "unexpected token",
        );

        let diagnostic = NormalizedDiagnostic::from(&error);

        assert_eq!(diagnostic.severity, NormalizedSeverity::Error);
        assert_eq!(diagnostic.message, "unexpected token");
        assert_eq!(diagnostic.range, Some((4, 5)));
        assert_eq!(diagnostic.source, Some("parser"));
    }

    #[test]
    fn lower_error_with_span_preserves_range() {
        let error = unsupported_root_lower_compile_error();

        let diagnostic = NormalizedDiagnostic::from(&error);

        assert_eq!(diagnostic.severity, NormalizedSeverity::Error);
        assert!(diagnostic.message.contains("unsupported syntax node kind"));
        assert_eq!(diagnostic.range, Some((0, 0)));
        assert_eq!(diagnostic.source, Some("lowering"));
    }

    #[test]
    fn lower_error_without_span_keeps_absent_range() {
        let error = CompileError::from(
            cellang::parser::lower_source("foo(")
                .expect_err("expected parse failure in lowering"),
        );

        let diagnostic = NormalizedDiagnostic::from(&error);

        assert_eq!(diagnostic.severity, NormalizedSeverity::Error);
        assert!(diagnostic.message.contains("continuing argument list"));
        assert_eq!(diagnostic.range, None);
        assert_eq!(diagnostic.source, Some("lowering"));
    }

    #[test]
    fn runtime_error_falls_back_without_range() {
        let error = RuntimeError::new("type mismatch");

        let diagnostic = NormalizedDiagnostic::from(&error);

        assert_eq!(diagnostic.severity, NormalizedSeverity::Error);
        assert_eq!(diagnostic.message, "RuntimeError: type mismatch");
        assert_eq!(diagnostic.range, None);
        assert_eq!(diagnostic.source, Some("type-check/runtime"));
    }

    #[test]
    fn mapping_is_deterministic_for_same_error() {
        let error = unsupported_root_lower_compile_error();

        let first = NormalizedDiagnostic::from(&error);
        let second = NormalizedDiagnostic::from(&error);

        assert_eq!(first, second);
    }

    #[test]
    fn lsp_conversion_maps_severity_and_range() {
        let diagnostic = NormalizedDiagnostic::new(
            NormalizedSeverity::Warning,
            "suspicious",
            Some((1, 5)),
            Some("parser"),
        );

        let lsp = diagnostic.to_lsp("a🦀b");

        assert_eq!(lsp.severity, Some(DiagnosticSeverity::WARNING));
        assert_eq!(lsp.message, "suspicious");
        assert_eq!(lsp.source.as_deref(), Some("parser"));
        assert_eq!(
            lsp.range,
            Range::new(Position::new(0, 1), Position::new(0, 3))
        );
    }

    #[test]
    fn lsp_conversion_without_span_defaults_to_zero_range() {
        let diagnostic = NormalizedDiagnostic::new(
            NormalizedSeverity::Error,
            "boom",
            None,
            None,
        );

        let lsp = diagnostic.to_lsp("anything");

        assert_eq!(lsp.severity, Some(DiagnosticSeverity::ERROR));
        assert_eq!(
            lsp.range,
            Range::new(Position::new(0, 0), Position::new(0, 0))
        );
    }

    fn unsupported_root_lower_compile_error() -> CompileError {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(SyntaxKind::Root.into());
        builder.start_node(SyntaxKind::Expr.into());
        builder.start_node(SyntaxKind::Root.into());
        builder.finish_node();
        builder.finish_node();
        builder.finish_node();
        let tree = builder.finish();

        CompileError::from(
            cellang::parser::lower(tree).expect_err(
                "expected lower to fail for unsupported root child",
            ),
        )
    }
}
