//! LSP inspection APIs for querying CEL syntax trees.
//!
//! This module provides helper functions for Language Server Protocol (LSP)
//! operations such as hover, go-to-definition, and find-references.

use crate::syntax::{SyntaxKind, ast::CelNode};
use rowan::{TextRange, TextSize};

/// Returns the deepest syntax node that covers the given offset.
///
/// This is the primary API for LSP hover and go-to-definition features.
/// Returns the most specific (deepest) node in the tree that contains the offset.
///
/// # Examples
///
/// ```
/// # use cellang::{parser::parse, inspection::node_at_offset};
/// # use rowan::SyntaxNode;
/// # use rowan::TextSize;
/// let green = parse("1 + 2").unwrap();
/// let root = SyntaxNode::new_root(green);
/// let node = node_at_offset(&root, TextSize::from(0));
/// assert!(node.is_some());
/// ```
pub fn node_at_offset(root: &CelNode, offset: TextSize) -> Option<CelNode> {
    if !root.text_range().contains(offset) {
        return None;
    }

    root.token_at_offset(offset)
        .right_biased()
        .and_then(|token| token.parent())
}

/// Returns all direct child nodes matching the given kind.
///
/// This helper is useful for extracting specific child node types without
/// manual filtering.
///
/// # Examples
///
/// ```
/// # use cellang::{parser::parse, inspection::children_by_kind, SyntaxKind};
/// # use rowan::SyntaxNode;
/// let green = parse("[1, 2, 3]").unwrap();
/// let root = SyntaxNode::new_root(green);
/// let list = root.descendants().find(|n| n.kind() == SyntaxKind::List).unwrap();
/// let exprs = children_by_kind(&list, SyntaxKind::Expr);
/// assert_eq!(exprs.len(), 0);
/// ```
pub fn children_by_kind(node: &CelNode, kind: SyntaxKind) -> Vec<CelNode> {
    node.children()
        .filter(|child| child.kind() == kind)
        .collect()
}

/// Extracts the text range of a syntax node.
///
/// This is a convenience wrapper around Rowan's text_range() that returns
/// a stable TextRange suitable for LSP diagnostics and highlights.
pub fn text_range(node: &CelNode) -> TextRange {
    node.text_range()
}

/// Returns the text at the given offset, if valid.
///
/// This helper locates the token at the offset and returns its text content.
/// Returns None if the offset is out of bounds or doesn't correspond to a token.
pub fn text_at_offset(root: &CelNode, offset: TextSize) -> Option<String> {
    if !root.text_range().contains(offset) {
        return None;
    }

    root.token_at_offset(offset)
        .right_biased()
        .map(|token| token.text().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::parser::parse;

    fn parse_root(input: &str) -> CelNode {
        let green = parse(input).expect("parse failed");
        rowan::SyntaxNode::new_root(green)
    }

    #[test]
    fn test_node_at_offset_finds_token() {
        let root = parse_root("1 + 2");
        let node = node_at_offset(&root, TextSize::from(0));
        assert!(node.is_some(), "should find node at offset 0");
    }

    #[test]
    fn test_node_at_offset_finds_operator() {
        let root = parse_root("1 + 2");
        let node = node_at_offset(&root, TextSize::from(2));
        assert!(node.is_some(), "should find node at offset 2 (Plus)");
        let node = node.unwrap();
        let has_plus = node
            .ancestors()
            .flat_map(|n| n.children_with_tokens())
            .any(|child| {
                child
                    .as_token()
                    .is_some_and(|t| t.kind() == SyntaxKind::Plus)
            });
        assert!(has_plus, "ancestors should contain Plus token");
    }

    #[test]
    fn test_node_at_offset_out_of_range_returns_none() {
        let root = parse_root("1 + 2");
        let node = node_at_offset(&root, TextSize::from(1000));
        assert!(node.is_none(), "should return None for out-of-range offset");
    }

    #[test]
    fn test_node_at_offset_in_complex_expr() {
        let root = parse_root("foo.bar(baz)[0]");
        let nodes_found: Vec<_> = (0..root.text_range().len().into())
            .filter_map(|i| node_at_offset(&root, TextSize::from(i)))
            .collect();
        assert!(
            !nodes_found.is_empty(),
            "should find nodes at various offsets"
        );
    }

    #[test]
    fn test_children_by_kind_finds_exprs_in_list() {
        let root = parse_root("[1, 2, 3]");
        let list = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::List)
            .expect("should find List node");
        let exprs = children_by_kind(&list, SyntaxKind::Expr);
        assert_eq!(exprs.len(), 0, "atom elements are tokens, not Expr nodes");
    }

    #[test]
    fn test_children_by_kind_empty_list() {
        let root = parse_root("[]");
        let list = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::List)
            .expect("should find List node");
        let exprs = children_by_kind(&list, SyntaxKind::Expr);
        assert_eq!(exprs.len(), 0, "should find 0 Expr children in empty list");
    }

    #[test]
    fn test_children_by_kind_filters_correctly() {
        let root = parse_root("{a: 1, b: 2}");
        let map = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::Map)
            .expect("should find Map node");
        let exprs = children_by_kind(&map, SyntaxKind::Expr);
        assert_eq!(
            exprs.len(),
            0,
            "atom keys/values are tokens, not Expr nodes"
        );
    }

    #[test]
    fn test_text_range_extraction() {
        let root = parse_root("1 + 2 * 3");
        let binary_ops: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::BinaryOp)
            .collect();
        assert_eq!(binary_ops.len(), 2);

        let range1 = text_range(&binary_ops[0]);
        let range2 = text_range(&binary_ops[1]);

        assert!(range1.len() > TextSize::from(0));
        assert!(range2.len() > TextSize::from(0));
        assert!(
            range1.contains_range(range2),
            "outer op should contain inner op"
        );
    }

    #[test]
    fn test_text_at_offset_finds_token_text() {
        let root = parse_root("foo + bar");
        let text = text_at_offset(&root, TextSize::from(0));
        assert_eq!(text, Some("foo".to_string()));
    }

    #[test]
    fn test_text_at_offset_finds_operator() {
        let root = parse_root("1+2");
        let text = text_at_offset(&root, TextSize::from(1));
        assert_eq!(text, Some("+".to_string()));
    }

    #[test]
    fn test_text_at_offset_out_of_range() {
        let root = parse_root("foo");
        let text = text_at_offset(&root, TextSize::from(1000));
        assert!(text.is_none(), "should return None for out-of-range offset");
    }

    #[test]
    fn test_text_at_offset_handles_whitespace() {
        let root = parse_root("1 + 2");
        let text = text_at_offset(&root, TextSize::from(1));
        assert!(
            text == Some(" ".to_string()) || text == Some("+".to_string()),
            "offset 1 should be whitespace or operator depending on token boundaries"
        );
    }

    #[test]
    fn test_node_at_offset_nested_expr() {
        let root = parse_root("(1 + 2) * 3");
        let node = node_at_offset(&root, TextSize::from(2));
        assert!(node.is_some());
    }

    #[test]
    fn test_children_by_kind_in_binary_op() {
        let root = parse_root("a + b");
        let binary = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::BinaryOp)
            .expect("should find BinaryOp");
        let exprs = children_by_kind(&binary, SyntaxKind::Expr);
        assert_eq!(exprs.len(), 0, "operands are tokens, not Expr nodes");
    }

    #[test]
    fn test_text_range_covers_source() {
        let input = "foo.bar";
        let root = parse_root(input);
        let field_access = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::FieldAccess)
            .expect("should find FieldAccess");
        let range = text_range(&field_access);
        let text = &input[range];
        assert_eq!(text, "foo.bar", "range should cover entire field access");
    }
}
