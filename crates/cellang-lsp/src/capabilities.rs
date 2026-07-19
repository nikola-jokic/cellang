use lsp_types::{
    CompletionOptions, HoverProviderCapability, OneOf, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind,
};

pub const MVP_FEATURE_DIAGNOSTICS: &str = "textDocument/publishDiagnostics";
pub const MVP_FEATURE_HOVER: &str = "textDocument/hover";
pub const MVP_FEATURE_DEFINITION: &str = "textDocument/definition";
pub const MVP_FEATURE_REFERENCES: &str = "textDocument/references";
pub const MVP_FEATURE_COMPLETION: &str = "textDocument/completion";
pub const MVP_FEATURE_DOCUMENT_SYMBOLS: &str = "textDocument/documentSymbol";
pub const MVP_FEATURE_FORMATTING: &str = "textDocument/formatting";

#[must_use]
pub fn mvp_server_capabilities() -> ServerCapabilities {
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(
            TextDocumentSyncKind::FULL,
        )),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        references_provider: Some(OneOf::Left(true)),
        completion_provider: Some(CompletionOptions::default()),
        document_symbol_provider: Some(OneOf::Left(true)),
        document_formatting_provider: Some(OneOf::Left(true)),
        ..ServerCapabilities::default()
    }
}
