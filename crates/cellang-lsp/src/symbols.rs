use std::collections::HashMap;

use cellang::{Env, SyntaxKind, parser::ParseResult};
use lsp_types::{Position, Range};
use rowan::{Language, NodeOrToken, SyntaxToken};

use crate::position::{byte_range_to_lsp_range, position_to_byte_offset};

type ByteRange = (usize, usize);

#[derive(Debug, Clone, PartialEq, Eq)]
struct SymbolEntry {
    declaration: Option<ByteRange>,
    references: Vec<ByteRange>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolRecord {
    pub declaration: Option<Range>,
    pub references: Vec<Range>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolIndex {
    text: String,
    parsed: Option<ParseResult>,
    entries: Vec<SymbolEntry>,
    occurrence_to_symbol: HashMap<ByteRange, usize>,
}

impl SymbolIndex {
    #[must_use]
    pub fn new(text: &str) -> Self {
        Self::with_env(text, &Env::default())
    }

    #[must_use]
    pub fn with_env(text: &str, env: &Env) -> Self {
        let parsed = cellang::parser::parse(text).ok();
        let mut builder = SymbolIndexBuilder::new(env);

        if let Some(parsed_tree) = &parsed {
            let root = cellang::parser::CelNode::new_root(parsed_tree.clone());
            builder.index_root(&root);
        }

        builder.finish(text, parsed)
    }

    #[must_use]
    pub fn definition_at(&self, position: Position) -> Option<Range> {
        let symbol_id = self.symbol_id_at(position)?;
        let declaration = self.entries.get(symbol_id)?.declaration?;
        Some(byte_range_to_lsp_range(
            &self.text,
            declaration.0,
            declaration.1,
        ))
    }

    #[must_use]
    pub fn references_at(&self, position: Position) -> Vec<Range> {
        let Some(symbol_id) = self.symbol_id_at(position) else {
            return Vec::new();
        };
        let Some(entry) = self.entries.get(symbol_id) else {
            return Vec::new();
        };

        let mut ranges = Vec::new();
        if let Some(declaration) = entry.declaration {
            ranges.push(byte_range_to_lsp_range(
                &self.text,
                declaration.0,
                declaration.1,
            ));
        }
        ranges.extend(entry.references.iter().map(|(start, end)| {
            byte_range_to_lsp_range(&self.text, *start, *end)
        }));
        ranges
    }

    #[must_use]
    pub fn symbol_at(&self, position: Position) -> Option<SymbolRecord> {
        let symbol_id = self.symbol_id_at(position)?;
        let entry = self.entries.get(symbol_id)?;

        Some(SymbolRecord {
            declaration: entry.declaration.map(|(start, end)| {
                byte_range_to_lsp_range(&self.text, start, end)
            }),
            references: entry
                .references
                .iter()
                .map(|(start, end)| {
                    byte_range_to_lsp_range(&self.text, *start, *end)
                })
                .collect(),
        })
    }

    fn symbol_id_at(&self, position: Position) -> Option<usize> {
        let parsed = self.parsed.as_ref()?;
        let offset = position_to_byte_offset(&self.text, position);
        if !is_identifier_byte(&self.text, offset) {
            return None;
        }
        let offset_u32 = u32::try_from(offset).ok()?;

        let root = cellang::parser::CelNode::new_root(parsed.clone());
        let _node =
            cellang::inspection::node_at_offset(&root, offset_u32.into())?;

        let token = root
            .token_at_offset(offset_u32.into())
            .right_biased()
            .or_else(|| {
                root.token_at_offset(offset_u32.into()).left_biased()
            })?;
        if token.kind() != SyntaxKind::Ident {
            return None;
        }

        let range = token_to_byte_range(&token);
        if !(range.0..range.1).contains(&offset) {
            return None;
        }

        self.occurrence_to_symbol.get(&range).copied()
    }
}

#[must_use]
pub fn definition_at(text: &str, position: Position) -> Option<Range> {
    SymbolIndex::new(text).definition_at(position)
}

#[must_use]
pub fn references_at(text: &str, position: Position) -> Vec<Range> {
    SymbolIndex::new(text).references_at(position)
}

#[must_use]
pub fn definition_at_with_env(
    text: &str,
    position: Position,
    env: &Env,
) -> Option<Range> {
    SymbolIndex::with_env(text, env).definition_at(position)
}

#[must_use]
pub fn references_at_with_env(
    text: &str,
    position: Position,
    env: &Env,
) -> Vec<Range> {
    SymbolIndex::with_env(text, env).references_at(position)
}

#[derive(Debug)]
struct SymbolIndexBuilder<'a> {
    env: &'a Env,
    entries: Vec<SymbolEntry>,
    occurrence_to_symbol: HashMap<ByteRange, usize>,
    scopes: Vec<HashMap<String, usize>>,
    env_symbols: HashMap<String, usize>,
}

impl<'a> SymbolIndexBuilder<'a> {
    fn new(env: &'a Env) -> Self {
        Self {
            env,
            entries: Vec::new(),
            occurrence_to_symbol: HashMap::new(),
            scopes: vec![HashMap::new()],
            env_symbols: HashMap::new(),
        }
    }

    fn finish(self, text: &str, parsed: Option<ParseResult>) -> SymbolIndex {
        SymbolIndex {
            text: text.to_string(),
            parsed,
            entries: self.entries,
            occurrence_to_symbol: self.occurrence_to_symbol,
        }
    }

    fn index_root(&mut self, root: &cellang::parser::CelNode) {
        for child in root.children_with_tokens() {
            self.visit_element(child);
        }
    }

    fn visit_element<L>(
        &mut self,
        element: NodeOrToken<cellang::parser::CelNode, SyntaxToken<L>>,
    ) where
        L: Language<Kind = SyntaxKind>,
    {
        if let Some(node) = element.as_node() {
            if node.kind() == SyntaxKind::Call {
                self.visit_call(node.clone());
                return;
            }

            for child in node.children_with_tokens() {
                self.visit_element(child);
            }
            return;
        }

        let Some(token) = element.as_token() else {
            return;
        };
        if token.kind() != SyntaxKind::Ident {
            return;
        }
        if is_field_accessor_token(token) || is_call_callee_ident_token(token) {
            return;
        }

        self.record_reference(token.text(), token_to_byte_range(token));
    }

    fn visit_call(&mut self, call_node: cellang::parser::CelNode) {
        let CallParts { callee, args } =
            parse_call_parts(call_node.children_with_tokens());
        let Some(macro_name) = callee_macro_name(callee.as_ref()) else {
            for child in call_node.children_with_tokens() {
                self.visit_element(child);
            }
            return;
        };

        if !is_comprehension_macro(&macro_name) {
            for child in call_node.children_with_tokens() {
                self.visit_element(child);
            }
            return;
        }

        if args.len() < 2 {
            for child in call_node.children_with_tokens() {
                self.visit_element(child);
            }
            return;
        }

        let is_method_style = callee
            .as_ref()
            .and_then(NodeOrToken::as_node)
            .is_some_and(|node| node.kind() == SyntaxKind::FieldAccess);

        let (declaration_group, body_groups) = if is_method_style {
            if let Some(callee_ref) = callee.as_ref() {
                self.visit_method_macro_receiver(callee_ref);
            }
            (&args[0], &args[1..])
        } else {
            if args.len() < 3 {
                for child in call_node.children_with_tokens() {
                    self.visit_element(child);
                }
                return;
            }
            self.visit_group(&args[0]);
            (&args[1], &args[2..])
        };

        let Some((declaration_name, declaration)) =
            declaration_from_group(declaration_group)
        else {
            self.visit_group(declaration_group);
            for group in body_groups {
                self.visit_group(group);
            }
            return;
        };

        let symbol_id = self.record_declaration(declaration);
        self.push_scope_binding(&declaration_name, symbol_id);

        for group in body_groups {
            self.visit_group(group);
        }

        self.pop_scope_binding(&declaration_name);
    }

    fn visit_group(
        &mut self,
        group: &[NodeOrToken<
            cellang::parser::CelNode,
            SyntaxToken<impl Language<Kind = SyntaxKind>>,
        >],
    ) {
        for element in group {
            self.visit_element(element.clone());
        }
    }

    fn visit_method_macro_receiver(
        &mut self,
        callee: &NodeOrToken<
            cellang::parser::CelNode,
            SyntaxToken<impl Language<Kind = SyntaxKind>>,
        >,
    ) {
        let Some(node) = callee.as_node() else {
            return;
        };
        if node.kind() != SyntaxKind::FieldAccess {
            return;
        }

        for child in node.children_with_tokens() {
            if let Some(token) = child.as_token()
                && token.kind() == SyntaxKind::Dot
            {
                break;
            }
            self.visit_element(child);
        }
    }

    fn record_declaration(&mut self, declaration: ByteRange) -> usize {
        let symbol_id = self.entries.len();
        self.entries.push(SymbolEntry {
            declaration: Some(declaration),
            references: Vec::new(),
        });
        self.occurrence_to_symbol.insert(declaration, symbol_id);
        symbol_id
    }

    fn record_reference(&mut self, name: &str, range: ByteRange) {
        let Some(symbol_id) = self.resolve_symbol_id(name) else {
            return;
        };
        if self.occurrence_to_symbol.contains_key(&range) {
            return;
        }

        if let Some(entry) = self.entries.get_mut(symbol_id) {
            entry.references.push(range);
        }
        self.occurrence_to_symbol.insert(range, symbol_id);
    }

    fn resolve_symbol_id(&mut self, name: &str) -> Option<usize> {
        if let Some(local) = self
            .scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
        {
            return Some(local);
        }

        if let Some(existing) = self.env_symbols.get(name).copied() {
            return Some(existing);
        }

        self.env.lookup_ident(name)?;

        let symbol_id = self.entries.len();
        self.entries.push(SymbolEntry {
            declaration: None,
            references: Vec::new(),
        });
        self.env_symbols.insert(name.to_string(), symbol_id);
        Some(symbol_id)
    }

    fn push_scope_binding(&mut self, name: &str, symbol_id: usize) {
        self.scopes
            .push(HashMap::from([(name.to_string(), symbol_id)]));
    }

    fn pop_scope_binding(&mut self, _name: &str) {
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }
}

struct CallParts<L>
where
    L: Language<Kind = SyntaxKind>,
{
    callee: Option<NodeOrToken<cellang::parser::CelNode, SyntaxToken<L>>>,
    args: Vec<Vec<NodeOrToken<cellang::parser::CelNode, SyntaxToken<L>>>>,
}

fn parse_call_parts<L>(
    children: impl IntoIterator<
        Item = NodeOrToken<cellang::parser::CelNode, SyntaxToken<L>>,
    >,
) -> CallParts<L>
where
    L: Language<Kind = SyntaxKind>,
{
    let mut before_left_paren = true;
    let mut callee = None;
    let mut args = Vec::new();
    let mut current_group = Vec::new();

    for child in children {
        if let Some(token) = child.as_token() {
            match token.kind() {
                SyntaxKind::LeftParen => {
                    before_left_paren = false;
                    continue;
                }
                SyntaxKind::Comma if !before_left_paren => {
                    args.push(current_group);
                    current_group = Vec::new();
                    continue;
                }
                SyntaxKind::RightParen if !before_left_paren => {
                    args.push(current_group);
                    current_group = Vec::new();
                    continue;
                }
                SyntaxKind::RightParen | SyntaxKind::Comma => continue,
                _ => {}
            }
        }

        if before_left_paren {
            if callee.is_none() {
                callee = Some(child);
            }
            continue;
        }

        current_group.push(child);
    }

    if !current_group.is_empty() {
        args.push(current_group);
    }

    args.retain(|group| !group.is_empty());

    CallParts { callee, args }
}

fn declaration_from_group<L>(
    group: &[NodeOrToken<cellang::parser::CelNode, SyntaxToken<L>>],
) -> Option<(String, ByteRange)>
where
    L: Language<Kind = SyntaxKind>,
{
    for element in group {
        if let Some(token) = element.as_token()
            && token.kind() == SyntaxKind::Ident
        {
            return Some((
                token.text().to_string(),
                token_to_byte_range(token),
            ));
        }

        let Some(node) = element.as_node() else {
            continue;
        };
        if let Some(token) = node
            .descendants_with_tokens()
            .filter_map(|item| item.into_token())
            .find(|token| token.kind() == SyntaxKind::Ident)
        {
            return Some((
                token.text().to_string(),
                token_to_byte_range(&token),
            ));
        }
    }

    None
}

fn callee_macro_name<L>(
    callee: Option<&NodeOrToken<cellang::parser::CelNode, SyntaxToken<L>>>,
) -> Option<String>
where
    L: Language<Kind = SyntaxKind>,
{
    let callee = callee?;

    if let Some(token) = callee.as_token()
        && token.kind() == SyntaxKind::Ident
    {
        return Some(token.text().to_string());
    }

    let node = callee.as_node()?;
    if node.kind() != SyntaxKind::FieldAccess {
        return None;
    }

    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .scan(false, |seen_dot, token| {
            if token.kind() == SyntaxKind::Dot {
                *seen_dot = true;
                return Some(None);
            }

            if *seen_dot && token.kind() == SyntaxKind::Ident {
                return Some(Some(token.text().to_string()));
            }

            Some(None)
        })
        .flatten()
        .next()
}

fn is_comprehension_macro(name: &str) -> bool {
    matches!(name, "all" | "exists" | "exists_one" | "map" | "filter")
}

fn is_identifier_byte(text: &str, offset: usize) -> bool {
    let Some(byte) = text.as_bytes().get(offset).copied() else {
        return false;
    };
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn token_to_byte_range<L>(token: &SyntaxToken<L>) -> ByteRange
where
    L: Language<Kind = SyntaxKind>,
{
    let range = token.text_range();
    let raw_start = u32::from(range.start()) as usize;
    let raw_end = u32::from(range.end()) as usize;
    let text = token.text();

    let leading_ws = text.len().saturating_sub(text.trim_start().len());
    let trailing_ws = text.len().saturating_sub(text.trim_end().len());
    let start = raw_start.saturating_add(leading_ws);
    let end = raw_end.saturating_sub(trailing_ws);

    (start.min(end), end.max(start))
}

fn is_field_accessor_token<L>(token: &SyntaxToken<L>) -> bool
where
    L: Language<Kind = SyntaxKind>,
{
    let Some(parent) = token.parent() else {
        return false;
    };
    if parent.kind() != SyntaxKind::FieldAccess {
        return false;
    }

    let token_range = token.text_range();
    let mut seen_dot = false;
    for child in parent.children_with_tokens() {
        let Some(child_token) = child.as_token() else {
            continue;
        };

        if child_token.kind() == SyntaxKind::Dot {
            seen_dot = true;
            continue;
        }

        if child_token.text_range() == token_range {
            return seen_dot;
        }
    }

    false
}

fn is_call_callee_ident_token<L>(token: &SyntaxToken<L>) -> bool
where
    L: Language<Kind = SyntaxKind>,
{
    let Some(parent) = token.parent() else {
        return false;
    };
    if parent.kind() != SyntaxKind::Call {
        return false;
    }

    for child in parent.children_with_tokens() {
        if let Some(child_token) = child.as_token()
            && child_token.kind() == SyntaxKind::LeftParen
        {
            return false;
        }

        if let Some(child_token) = child.as_token()
            && child_token.text_range() == token.text_range()
        {
            return true;
        }

        if let Some(child_node) = child.as_node()
            && child_node.text_range().contains_range(token.text_range())
        {
            return false;
        }
    }

    false
}

#[cfg(test)]
mod symbol_index {
    use super::*;
    use cellang::types::{IdentDecl, Type};

    use crate::position::byte_offset_to_position;

    fn nth_offset(haystack: &str, needle: &str, nth: usize) -> usize {
        haystack
            .match_indices(needle)
            .nth(nth)
            .map(|(idx, _)| idx)
            .expect("needle occurrence should exist")
    }

    fn position_for_nth(text: &str, needle: &str, nth: usize) -> Position {
        byte_offset_to_position(text, nth_offset(text, needle, nth))
    }

    #[test]
    fn local_resolution() {
        let text = "roles.exists(role, role == target && role != fallback)";
        let index = SymbolIndex::new(text);

        let usage_position = position_for_nth(text, "role", 1);
        let definition =
            index.definition_at(usage_position).expect("definition");
        let references = index.references_at(usage_position);

        println!("local definition: {:?}", definition);
        println!("local references: {:?}", references);

        let expected_decl = byte_range_to_lsp_range(
            text,
            nth_offset(text, "role", 1),
            nth_offset(text, "role", 1) + "role".len(),
        );
        assert_eq!(definition, expected_decl);
        assert_eq!(
            references.len(),
            3,
            "declaration + two references expected"
        );
        assert!(references.contains(&expected_decl));
    }

    #[test]
    fn unknown_symbol() {
        let text = "missing + 1";
        let position = position_for_nth(text, "missing", 0);

        let definition = definition_at(text, position);
        let references = references_at(text, position);

        println!("unknown definition: {:?}", definition);
        println!("unknown references: {:?}", references);

        assert!(definition.is_none());
        assert!(references.is_empty());
    }

    #[test]
    fn function_parameters_as_declarations() {
        let text = "exists(items, element, element > 0)";
        let index = SymbolIndex::new(text);
        let usage_position = position_for_nth(text, "element", 1);

        let definition =
            index.definition_at(usage_position).expect("definition");
        let references = index.references_at(usage_position);

        assert_eq!(references.len(), 2, "parameter declaration + one use");
        assert!(references.contains(&definition));
    }

    #[test]
    fn environment_variables_without_source_declaration() {
        let text = "user == 'alice'";
        let mut builder = Env::builder();
        builder
            .add_ident(IdentDecl::new("user", Type::String))
            .expect("add env ident");
        let env = builder.build();

        let index = SymbolIndex::with_env(text, &env);
        let position = position_for_nth(text, "user", 0);

        assert!(index.definition_at(position).is_none());
        let references = index.references_at(position);
        assert_eq!(references.len(), 1);
    }

    #[test]
    fn whitespace_position_returns_empty() {
        let text = "exists(items, item, item > 0)";
        let whitespace = text.find(' ').expect("whitespace should exist");
        let position = byte_offset_to_position(text, whitespace);

        let index = SymbolIndex::new(text);
        assert!(index.definition_at(position).is_none());
        assert!(index.references_at(position).is_empty());
    }
}
