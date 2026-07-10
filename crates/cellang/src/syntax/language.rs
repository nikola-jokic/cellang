use crate::syntax::SyntaxKind;
use rowan::Language;

/// CelLanguage implements the Rowan Language trait for CEL syntax trees.
/// This allows Rowan to understand CEL's syntax structure and node representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CelLanguage;

impl Language for CelLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        SyntaxKind::from_raw(raw.0)
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}
