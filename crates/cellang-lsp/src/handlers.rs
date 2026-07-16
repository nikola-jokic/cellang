use cellang::Env;
use lsp_types::{
    CompletionParams, CompletionResponse, DocumentFormattingParams,
    DocumentSymbol, DocumentSymbolParams, DocumentSymbolResponse,
    GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverParams, Location,
    ReferenceParams, Uri, WorkspaceEdit,
};
use serde_json::{Value, json};

use crate::embedded::{
    completions_for_text_with_env, diagnostics_for_text_with_env,
    document_symbols_for_text, hover_for_text_at_position,
};
use crate::formatter::FormatterError;
use crate::formatter::format_document;
use crate::position::byte_range_to_lsp_range;
use crate::state::DocumentStore;
use crate::symbols::SymbolIndex;

pub trait FeatureHandlers {
    fn publish_diagnostics(
        &self,
        uri: &Uri,
        documents: &DocumentStore,
    ) -> Option<Value> {
        publish_diagnostics_with_env(uri, documents, &Env::default())
    }

    fn hover(
        &self,
        params: HoverParams,
        documents: &DocumentStore,
    ) -> Option<Hover> {
        hover_with_env(params, documents, &Env::default())
    }

    fn definition(
        &self,
        params: GotoDefinitionParams,
        documents: &DocumentStore,
    ) -> Option<GotoDefinitionResponse> {
        definition_with_env(params, documents, &Env::default())
    }

    fn references(
        &self,
        params: ReferenceParams,
        documents: &DocumentStore,
    ) -> Vec<Location> {
        references_with_env(params, documents, &Env::default())
    }

    fn completion(
        &self,
        params: CompletionParams,
        documents: &DocumentStore,
    ) -> Option<CompletionResponse> {
        completion_with_env(params, documents, &Env::default())
    }

    fn document_symbols(
        &self,
        params: DocumentSymbolParams,
        documents: &DocumentStore,
    ) -> Option<DocumentSymbolResponse> {
        let uri = &params.text_document.uri;
        let document = documents.get(uri)?;

        let symbols = extract_document_symbols(&document.text);
        if symbols.is_empty() {
            return None;
        }

        Some(DocumentSymbolResponse::Nested(symbols))
    }

    fn formatting(
        &self,
        params: DocumentFormattingParams,
        documents: &DocumentStore,
    ) -> Result<Option<Vec<lsp_types::TextEdit>>, FormatterError> {
        let uri = &params.text_document.uri;
        let Some(document) = documents.get(uri) else {
            return Ok(None);
        };

        let new_text = format_document(&document.text)?;
        let full_range =
            byte_range_to_lsp_range(&document.text, 0, document.text.len());
        Ok(Some(vec![lsp_types::TextEdit {
            range: full_range,
            new_text,
        }]))
    }
}

#[derive(Debug, Default)]
pub struct MethodNotSupportedHandler;

impl FeatureHandlers for MethodNotSupportedHandler {}

#[derive(Debug, Clone)]
pub struct EnvFeatureHandler {
    env: Env,
}

impl EnvFeatureHandler {
    #[must_use]
    pub fn new(env: Env) -> Self {
        Self { env }
    }

    #[must_use]
    pub fn env(&self) -> &Env {
        &self.env
    }
}

impl FeatureHandlers for EnvFeatureHandler {
    fn publish_diagnostics(
        &self,
        uri: &Uri,
        documents: &DocumentStore,
    ) -> Option<Value> {
        publish_diagnostics_with_env(uri, documents, &self.env)
    }

    fn hover(
        &self,
        params: HoverParams,
        documents: &DocumentStore,
    ) -> Option<Hover> {
        hover_with_env(params, documents, &self.env)
    }

    fn definition(
        &self,
        params: GotoDefinitionParams,
        documents: &DocumentStore,
    ) -> Option<GotoDefinitionResponse> {
        definition_with_env(params, documents, &self.env)
    }

    fn references(
        &self,
        params: ReferenceParams,
        documents: &DocumentStore,
    ) -> Vec<Location> {
        references_with_env(params, documents, &self.env)
    }

    fn completion(
        &self,
        params: CompletionParams,
        documents: &DocumentStore,
    ) -> Option<CompletionResponse> {
        completion_with_env(params, documents, &self.env)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SupportedRequest {
    Hover,
    Definition,
    References,
    Completion,
    DocumentSymbols,
    Formatting,
}

impl SupportedRequest {
    #[must_use]
    pub fn from_method(method: &str) -> Option<Self> {
        match method {
            "textDocument/hover" => Some(Self::Hover),
            "textDocument/definition" => Some(Self::Definition),
            "textDocument/references" => Some(Self::References),
            "textDocument/completion" => Some(Self::Completion),
            "textDocument/documentSymbol" => Some(Self::DocumentSymbols),
            "textDocument/formatting" => Some(Self::Formatting),
            _ => None,
        }
    }
}

fn publish_diagnostics_with_env(
    uri: &Uri,
    documents: &DocumentStore,
    env: &Env,
) -> Option<Value> {
    let document = documents.get(uri)?;
    let diagnostics = diagnostics_for_text_with_env(&document.text, env)
        .into_iter()
        .map(|diagnostic| diagnostic.to_lsp(&document.text))
        .collect::<Vec<_>>();

    Some(json!({
        "jsonrpc": "2.0",
        "method": "textDocument/publishDiagnostics",
        "params": {
            "uri": uri,
            "version": document.version,
            "diagnostics": diagnostics,
        }
    }))
}

fn hover_with_env(
    params: HoverParams,
    documents: &DocumentStore,
    env: &Env,
) -> Option<Hover> {
    let uri = &params.text_document_position_params.text_document.uri;
    let position = params.text_document_position_params.position;

    let document = documents.get(uri)?;
    hover_for_text_at_position(&document.text, position, env)
}

fn definition_with_env(
    params: GotoDefinitionParams,
    documents: &DocumentStore,
    env: &Env,
) -> Option<GotoDefinitionResponse> {
    let uri = &params.text_document_position_params.text_document.uri;
    let position = params.text_document_position_params.position;
    let document = documents.get(uri)?;
    let range =
        SymbolIndex::with_env(&document.text, env).definition_at(position)?;

    Some(GotoDefinitionResponse::Scalar(Location {
        uri: uri.clone(),
        range,
    }))
}

fn references_with_env(
    params: ReferenceParams,
    documents: &DocumentStore,
    env: &Env,
) -> Vec<Location> {
    let uri = &params.text_document_position.text_document.uri;
    let position = params.text_document_position.position;
    let Some(document) = documents.get(uri) else {
        return Vec::new();
    };

    let mut ranges =
        SymbolIndex::with_env(&document.text, env).references_at(position);
    ranges.sort_by_key(|range| {
        (
            range.start.line,
            range.start.character,
            range.end.line,
            range.end.character,
        )
    });

    ranges
        .into_iter()
        .map(|range| Location {
            uri: uri.clone(),
            range,
        })
        .collect()
}

fn completion_with_env(
    params: CompletionParams,
    documents: &DocumentStore,
    env: &Env,
) -> Option<CompletionResponse> {
    let uri = &params.text_document_position.text_document.uri;
    let document = documents.get(uri)?;

    Some(CompletionResponse::Array(completions_for_text_with_env(
        &document.text,
        env,
    )))
}

fn extract_document_symbols(text: &str) -> Vec<DocumentSymbol> {
    document_symbols_for_text(text)
}

#[allow(dead_code)]
fn _ignore_workspace_edit(_: WorkspaceEdit) {}
