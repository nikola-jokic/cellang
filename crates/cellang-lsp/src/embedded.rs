use cellang::Env;
use lsp_types::{
    CompletionItem, CompletionItemKind, Diagnostic, Documentation, Hover,
    HoverContents, Location, MarkupContent, MarkupKind, Position, Range,
};

use crate::diagnostics::{NormalizedDiagnostic, NormalizedSeverity};
use crate::formatter::{FormatterError, format_document};
use crate::position::{
    byte_offset_to_position, byte_range_to_lsp_range, position_to_byte_offset,
    translate_local_range_by_host_start_offset,
    translate_local_range_by_host_start_position,
};
use crate::symbols::SymbolIndex;

#[derive(Debug, Clone)]
pub struct EmbeddedService {
    env: Env,
}

impl EmbeddedService {
    #[must_use]
    pub fn new(env: Env) -> Self {
        Self { env }
    }

    #[must_use]
    pub fn env(&self) -> &Env {
        &self.env
    }

    #[must_use]
    pub fn diagnostics(&self, text: &str) -> Vec<NormalizedDiagnostic> {
        diagnostics_for_text_with_env(text, &self.env)
    }

    #[must_use]
    pub fn lsp_diagnostics(&self, text: &str) -> Vec<Diagnostic> {
        self.diagnostics(text)
            .into_iter()
            .map(|diagnostic| diagnostic.to_lsp(text))
            .collect()
    }

    #[must_use]
    pub fn hover_at_offset(&self, text: &str, offset: usize) -> Option<Hover> {
        hover_for_text_at_offset(text, offset, &self.env)
    }

    #[must_use]
    pub fn hover_at_position(
        &self,
        text: &str,
        position: Position,
    ) -> Option<Hover> {
        hover_for_text_at_position(text, position, &self.env)
    }

    #[must_use]
    pub fn definition_at_position(
        &self,
        text: &str,
        position: Position,
    ) -> Option<Range> {
        SymbolIndex::with_env(text, &self.env).definition_at(position)
    }

    #[must_use]
    pub fn references_at_position(
        &self,
        text: &str,
        position: Position,
    ) -> Vec<Range> {
        let mut ranges =
            SymbolIndex::with_env(text, &self.env).references_at(position);
        sort_ranges(&mut ranges);
        ranges
    }

    #[must_use]
    pub fn completions(&self, text: &str) -> Vec<CompletionItem> {
        completions_for_text_with_env(text, &self.env)
    }

    pub fn format(&self, text: &str) -> Result<String, FormatterError> {
        format_document(text)
    }

    #[must_use]
    pub fn document_symbols(
        &self,
        text: &str,
    ) -> Vec<lsp_types::DocumentSymbol> {
        document_symbols_for_text(text)
    }
}

impl Default for EmbeddedService {
    fn default() -> Self {
        Self::new(Env::default())
    }
}

#[derive(Debug, Clone)]
pub struct HostExpression<'a> {
    pub host_text: &'a str,
    pub expression_text: &'a str,
    pub expression_start_byte: usize,
}

impl<'a> HostExpression<'a> {
    #[must_use]
    pub fn new(
        host_text: &'a str,
        expression_text: &'a str,
        expression_start_byte: usize,
    ) -> Self {
        Self {
            host_text,
            expression_text,
            expression_start_byte,
        }
    }

    #[must_use]
    pub fn from_start_position(
        host_text: &'a str,
        expression_text: &'a str,
        start: Position,
    ) -> Self {
        Self::new(
            host_text,
            expression_text,
            position_to_byte_offset(host_text, start),
        )
    }

    #[must_use]
    pub fn start_position(&self) -> Position {
        byte_offset_to_position(self.host_text, self.expression_start_byte)
    }

    #[must_use]
    pub fn translate_range(&self, range: Range) -> Range {
        translate_local_range_by_host_start_offset(
            self.host_text,
            self.expression_start_byte,
            self.expression_text,
            range,
        )
    }

    #[must_use]
    pub fn translate_hover(&self, hover: Hover) -> Hover {
        Hover {
            contents: hover.contents,
            range: hover.range.map(|range| self.translate_range(range)),
        }
    }

    #[must_use]
    pub fn translate_diagnostic(&self, diagnostic: Diagnostic) -> Diagnostic {
        Diagnostic {
            range: self.translate_range(diagnostic.range),
            ..diagnostic
        }
    }

    #[must_use]
    pub fn translate_location(&self, location: Location) -> Location {
        Location {
            uri: location.uri,
            range: self.translate_range(location.range),
        }
    }
}

#[must_use]
pub fn diagnostics_for_text_with_env(
    text: &str,
    env: &Env,
) -> Vec<NormalizedDiagnostic> {
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

    if let Err(error) = cellang::parser::type_check(env, &lowered) {
        return vec![NormalizedDiagnostic::from(cellang::CompileError::from(
            error,
        ))];
    }

    Vec::new()
}

#[must_use]
pub fn hover_for_text_at_position(
    text: &str,
    position: Position,
    env: &Env,
) -> Option<Hover> {
    let offset = position_to_byte_offset(text, position);
    hover_for_text_at_offset(text, offset, env)
}

#[must_use]
pub fn hover_for_text_at_offset(
    text: &str,
    offset: usize,
    env: &Env,
) -> Option<Hover> {
    if !is_identifier_byte(text, offset) {
        return None;
    }

    let position = byte_offset_to_position(text, offset);
    let index = SymbolIndex::with_env(text, env);
    let symbol_record = index.symbol_at(position)?;

    let parsed = cellang::parser::parse(text).ok()?;
    let root = cellang::parser::CelNode::new_root(parsed);
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

#[must_use]
pub fn completions_for_text_with_env(
    text: &str,
    env: &Env,
) -> Vec<CompletionItem> {
    let mut items =
        Vec::with_capacity(env.idents().len() + env.functions().len());

    let md_doc = |doc: Option<String>| {
        doc.map(|d| {
            Documentation::MarkupContent(MarkupContent {
                kind: MarkupKind::Markdown,
                value: d,
            })
        })
    };

    for (name, decl) in env.idents() {
        items.push(CompletionItem {
            label: name.clone(),
            kind: Some(CompletionItemKind::VARIABLE),
            documentation: md_doc(decl.doc.clone()),
            ..Default::default()
        });
    }

    for (name, decl) in env.functions() {
        items.push(CompletionItem {
            label: name.clone(),
            kind: Some(CompletionItemKind::FUNCTION),
            documentation: md_doc(decl.doc.clone()),
            ..Default::default()
        });
    }

    for name in collect_local_symbols(text) {
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
    items
}

#[must_use]
pub fn document_symbols_for_text(text: &str) -> Vec<lsp_types::DocumentSymbol> {
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

#[must_use]
pub fn local_position_from_host_position(
    host_text: &str,
    expression_start_byte: usize,
    expression_text: &str,
    host_position: Position,
) -> Option<Position> {
    let host_offset = position_to_byte_offset(host_text, host_position);
    let expression_end =
        expression_start_byte.saturating_add(expression_text.len());

    if host_offset < expression_start_byte || host_offset > expression_end {
        return None;
    }

    Some(byte_offset_to_position(
        expression_text,
        host_offset.saturating_sub(expression_start_byte),
    ))
}

#[must_use]
pub fn translate_local_range_by_start_position(
    host_text: &str,
    host_start: Position,
    local_text: &str,
    local_range: Range,
) -> Range {
    translate_local_range_by_host_start_position(
        host_text,
        host_start,
        local_text,
        local_range,
    )
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

fn extract_symbols_from_node(
    node: &cellang::parser::CelNode,
    text: &str,
    symbols: &mut Vec<lsp_types::DocumentSymbol>,
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
) -> Option<lsp_types::DocumentSymbol> {
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
    let range = byte_range_to_lsp_range(text, start, end);

    #[allow(deprecated)]
    Some(lsp_types::DocumentSymbol {
        name: name.clone(),
        detail: Some("comprehension binder".to_string()),
        kind: lsp_types::SymbolKind::VARIABLE,
        tags: None,
        deprecated: None,
        range,
        selection_range: range,
        children: None,
    })
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

fn is_identifier_byte(text: &str, offset: usize) -> bool {
    let Some(byte) = text.as_bytes().get(offset).copied() else {
        return false;
    };
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn sort_ranges(ranges: &mut [Range]) {
    ranges.sort_by_key(|range| {
        (
            range.start.line,
            range.start.character,
            range.end.line,
            range.end.character,
        )
    });
}
