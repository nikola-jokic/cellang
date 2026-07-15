use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionParams, CompletionResponse,
    DocumentFormattingParams, DocumentSymbol, DocumentSymbolParams,
    DocumentSymbolResponse, Documentation, GotoDefinitionParams,
    GotoDefinitionResponse, Hover, HoverContents, HoverParams, Location,
    MarkupContent, MarkupKind, ReferenceParams, SymbolKind, Uri, WorkspaceEdit,
};
use serde_json::{Value, json};

use crate::diagnostics::{NormalizedDiagnostic, NormalizedSeverity};
use crate::formatter::FormatterError;
use crate::formatter::format_document;
use crate::position::byte_range_to_lsp_range;
use crate::position::position_to_byte_offset;
use crate::state::DocumentStore;
use crate::symbols::SymbolIndex;

pub trait FeatureHandlers {
    fn publish_diagnostics(
        &self,
        uri: &Uri,
        documents: &DocumentStore,
    ) -> Option<Value> {
        let document = documents.get(uri)?;
        let diagnostics = collect_diagnostics(&document.text)
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

    fn hover(
        &self,
        params: HoverParams,
        documents: &DocumentStore,
    ) -> Option<Hover> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let document = documents.get(uri)?;
        let offset = position_to_byte_offset(&document.text, position);

        if !is_identifier_byte(&document.text, offset) {
            return None;
        }

        let index = SymbolIndex::new(&document.text);
        let symbol_record = index.symbol_at(position)?;

        let parsed = document.parsed.as_ref()?;
        let root = cellang::parser::CelNode::new_root(parsed.clone());
        let token_text =
            cellang::inspection::text_at_offset(&root, (offset as u32).into())?;

        let content = build_hover_content(&token_text, &symbol_record);

        Some(Hover {
            contents: HoverContents::Markup(content),
            range: symbol_record
                .declaration
                .or_else(|| symbol_record.references.first().copied()),
        })
    }

    fn definition(
        &self,
        params: GotoDefinitionParams,
        documents: &DocumentStore,
    ) -> Option<GotoDefinitionResponse> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let document = documents.get(uri)?;
        let range = SymbolIndex::new(&document.text).definition_at(position)?;

        Some(GotoDefinitionResponse::Scalar(Location {
            uri: uri.clone(),
            range,
        }))
    }

    fn references(
        &self,
        params: ReferenceParams,
        documents: &DocumentStore,
    ) -> Vec<Location> {
        let uri = &params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some(document) = documents.get(uri) else {
            return Vec::new();
        };

        let mut ranges =
            SymbolIndex::new(&document.text).references_at(position);
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

    fn completion(
        &self,
        params: CompletionParams,
        documents: &DocumentStore,
    ) -> Option<CompletionResponse> {
        let uri = &params.text_document_position.text_document.uri;
        let document = documents.get(uri)?;
        let env = cellang::Env::default();

        let mut items =
            Vec::with_capacity(env.idents().len() + env.functions().len());

        for (name, decl) in env.idents() {
            items.push(CompletionItem {
                label: name.clone(),
                kind: Some(CompletionItemKind::VARIABLE),
                documentation: decl.doc.clone().map(Documentation::String),
                ..Default::default()
            });
        }

        for (name, decl) in env.functions() {
            items.push(CompletionItem {
                label: name.clone(),
                kind: Some(CompletionItemKind::FUNCTION),
                documentation: decl.doc.clone().map(Documentation::String),
                ..Default::default()
            });
        }

        let local_symbols = collect_local_symbols(&document.text);
        for name in local_symbols {
            if env.lookup_ident(&name).is_none()
                && env.lookup_function(&name).is_none()
            {
                items.push(CompletionItem {
                    label: name,
                    kind: Some(CompletionItemKind::VARIABLE),
                    ..Default::default()
                });
            }
        }

        items.sort_by(|a, b| a.label.cmp(&b.label));

        Some(CompletionResponse::Array(items))
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

fn collect_diagnostics(text: &str) -> Vec<NormalizedDiagnostic> {
    let parsed = match cellang::parser::parse(text) {
        Ok(parsed) => parsed,
        Err(error) => {
            return vec![NormalizedDiagnostic::new(
                NormalizedSeverity::Error,
                error.message,
                error
                    .span
                    .map(|(start, len)| (start, start.saturating_add(len))),
                Some("parser"),
            )];
        }
    };

    let lowered = match cellang::parser::lower(parsed) {
        Ok(lowered) => lowered,
        Err(error) => {
            return vec![NormalizedDiagnostic::from(
                cellang::CompileError::from(error),
            )];
        }
    };

    if let Err(error) =
        cellang::parser::type_check(&cellang::Env::default(), &lowered)
    {
        return vec![NormalizedDiagnostic::from(cellang::CompileError::from(
            error,
        ))];
    }

    Vec::new()
}

#[derive(Debug, Default)]
pub struct MethodNotSupportedHandler;

impl FeatureHandlers for MethodNotSupportedHandler {}

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

fn collect_local_symbols(text: &str) -> Vec<String> {
    let Ok(parsed) = cellang::parser::parse(text) else {
        return Vec::new();
    };
    let root = cellang::parser::CelNode::new_root(parsed);

    let mut symbols = Vec::new();
    collect_identifiers_recursive(&root, &mut symbols);

    let mut seen = std::collections::HashSet::new();
    symbols.retain(|name| seen.insert(name.clone()));

    symbols
}

fn collect_identifiers_recursive(
    node: &cellang::parser::CelNode,
    symbols: &mut Vec<String>,
) {
    use cellang::SyntaxKind;

    for child in node.children_with_tokens() {
        if let Some(token) = child.as_token() {
            if token.kind() == SyntaxKind::Ident {
                symbols.push(token.text().to_string());
            }
        } else if let Some(child_node) = child.as_node() {
            collect_identifiers_recursive(child_node, symbols);
        }
    }
}

fn extract_document_symbols(text: &str) -> Vec<DocumentSymbol> {
    let Ok(parsed) = cellang::parser::parse(text) else {
        return Vec::new();
    };
    let root = cellang::parser::CelNode::new_root(parsed);

    let mut symbols = Vec::new();
    extract_symbols_from_node(&root, text, &mut symbols);

    symbols.sort_by_key(|s| {
        (
            s.selection_range.start.line,
            s.selection_range.start.character,
        )
    });

    symbols
}

fn extract_symbols_from_node(
    node: &cellang::parser::CelNode,
    text: &str,
    symbols: &mut Vec<DocumentSymbol>,
) {
    use cellang::SyntaxKind;

    if node.kind() == SyntaxKind::Call
        && let Some(symbol) = extract_comprehension_symbol(node, text)
    {
        symbols.push(symbol);
    }

    for child in node.children() {
        extract_symbols_from_node(&child, text, symbols);
    }
}

fn extract_comprehension_symbol(
    call_node: &cellang::parser::CelNode,
    text: &str,
) -> Option<DocumentSymbol> {
    use cellang::SyntaxKind;

    let mut is_comprehension = false;
    let mut binder_name = None;
    let mut binder_range = None;

    for token in call_node
        .descendants_with_tokens()
        .filter_map(|e| e.into_token())
    {
        if token.kind() == SyntaxKind::Ident {
            let text_content = token.text();
            if matches!(
                text_content,
                "exists" | "all" | "map" | "filter" | "exists_one"
            ) {
                is_comprehension = true;
            } else if is_comprehension && binder_name.is_none() {
                let range = token.text_range();
                let start = u32::from(range.start()) as usize;
                let end = u32::from(range.end()) as usize;
                binder_name = Some(text_content.to_string());
                binder_range = Some((start, end));
            }
        }
    }

    if !is_comprehension || binder_name.is_none() {
        return None;
    }

    let name = binder_name?;
    let (start, end) = binder_range?;
    let range = crate::position::byte_range_to_lsp_range(text, start, end);

    #[allow(deprecated)]
    Some(DocumentSymbol {
        name: name.clone(),
        detail: Some("comprehension binder".to_string()),
        kind: SymbolKind::VARIABLE,
        tags: None,
        deprecated: None,
        range,
        selection_range: range,
        children: None,
    })
}

#[allow(dead_code)]
fn _ignore_workspace_edit(_: WorkspaceEdit) {}

fn is_identifier_byte(text: &str, offset: usize) -> bool {
    let Some(byte) = text.as_bytes().get(offset).copied() else {
        return false;
    };
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn build_hover_content(
    token_text: &str,
    symbol_record: &crate::symbols::SymbolRecord,
) -> MarkupContent {
    let mut content = String::new();

    content.push_str("**");
    content.push_str(token_text);
    content.push_str("**");

    if let Some(decl_range) = symbol_record.declaration {
        content.push_str("\n\n*Declared at: ");
        content.push_str(&format!(
            "line {}, character {}",
            decl_range.start.line, decl_range.start.character
        ));
        content.push('*');
    } else {
        content.push_str("\n\n*Environment variable*");
    }

    let reference_count = symbol_record.references.len();
    if reference_count > 0 {
        content.push_str(&format!("\n\n{} reference", reference_count));
        if reference_count != 1 {
            content.push('s');
        }
    }

    MarkupContent {
        kind: MarkupKind::Markdown,
        value: content,
    }
}
