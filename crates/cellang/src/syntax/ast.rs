//! Typed syntax node wrappers for CEL AST.
//!
//! This module provides type-safe wrappers around Rowan `SyntaxNode` for structured
//! access to the CEL syntax tree. Each wrapper validates node kind and provides
//! accessors for child nodes/tokens.
//!
//! These wrappers are purely syntactic - they provide no semantic information about
//! types or values. Semantic analysis happens in the HIR layer.

use crate::syntax::{CelLanguage, SyntaxKind};
use rowan::SyntaxNode;

/// Type alias for CEL syntax nodes.
pub type CelNode = SyntaxNode<CelLanguage>;

/// Trait for typed AST nodes wrapping Rowan syntax nodes.
///
/// This follows the Rowan pattern for typed AST wrappers:
/// - Each wrapper type implements AstNode
/// - `cast()` validates the node kind and wraps if valid
/// - `syntax()` returns the underlying SyntaxNode for traversal
pub trait AstNode: Sized {
    /// Try to cast a syntax node to this typed wrapper.
    /// Returns None if the node kind doesn't match.
    fn cast(node: CelNode) -> Option<Self>;

    /// Get the underlying syntax node.
    fn syntax(&self) -> &CelNode;
}

/// Typed wrapper for binary operation nodes (e.g., `a + b`, `x && y`).
///
/// Binary operations have the structure:
/// ```text
/// BinaryOp
///   ├─ Expr (left operand)
///   ├─ Token (operator: Plus, Minus, Star, etc.)
///   └─ Expr (right operand)
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BinaryOpNode(CelNode);

impl AstNode for BinaryOpNode {
    fn cast(node: CelNode) -> Option<Self> {
        if node.kind() == SyntaxKind::BinaryOp {
            Some(Self(node))
        } else {
            None
        }
    }

    fn syntax(&self) -> &CelNode {
        &self.0
    }
}

impl BinaryOpNode {
    /// Returns the left operand node, if it's a complex expression.
    /// Returns None for atom operands (which are tokens, not nodes).
    #[cfg(test)]
    pub fn lhs(&self) -> Option<CelNode> {
        // LHS is before the operator token
        let op = self.operator()?;
        self.0
            .children_with_tokens()
            .take_while(|child| child.as_token().map(|t| t.kind()) != Some(op))
            .filter_map(|child| child.into_node())
            .next()
    }

    /// Returns the right operand node, if it's a complex expression.
    /// Returns None for atom operands (which are tokens, not nodes).
    #[cfg(test)]
    pub fn rhs(&self) -> Option<CelNode> {
        // RHS is after the operator token
        let op = self.operator()?;
        self.0
            .children_with_tokens()
            .skip_while(|child| child.as_token().map(|t| t.kind()) != Some(op))
            .skip(1) // Skip the operator itself
            .filter_map(|child| child.into_node())
            .next()
    }

    /// Returns the operator token kind (Plus, Minus, Star, etc.).
    pub fn operator(&self) -> Option<SyntaxKind> {
        self.0.children_with_tokens().find_map(|child| {
            child.into_token().and_then(|token| {
                let kind = token.kind();
                // Check if it's a binary operator token
                match kind {
                    SyntaxKind::Plus
                    | SyntaxKind::Minus
                    | SyntaxKind::Star
                    | SyntaxKind::Slash
                    | SyntaxKind::Percent
                    | SyntaxKind::And
                    | SyntaxKind::Or
                    | SyntaxKind::EqualEqual
                    | SyntaxKind::NotEqual
                    | SyntaxKind::Less
                    | SyntaxKind::LessEqual
                    | SyntaxKind::Greater
                    | SyntaxKind::GreaterEqual
                    | SyntaxKind::In => Some(kind),
                    _ => None,
                }
            })
        })
    }
}

/// Typed wrapper for unary operation nodes (e.g., `-x`, `!flag`).
///
/// Unary operations have the structure:
/// ```text
/// UnaryOp
///   ├─ Token (operator: Minus, Not)
///   └─ Expr (operand)
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnaryOpNode(CelNode);

impl AstNode for UnaryOpNode {
    fn cast(node: CelNode) -> Option<Self> {
        if node.kind() == SyntaxKind::UnaryOp {
            Some(Self(node))
        } else {
            None
        }
    }

    fn syntax(&self) -> &CelNode {
        &self.0
    }
}

impl UnaryOpNode {
    /// Returns the operand node, if it's a complex expression.
    /// Returns None for atom operands (which are tokens, not nodes).
    pub fn operand(&self) -> Option<CelNode> {
        self.0.children().next()
    }

    /// Returns the operator token kind (Minus, Not).
    pub fn operator(&self) -> Option<SyntaxKind> {
        self.0.children_with_tokens().find_map(|child| {
            child.into_token().and_then(|token| {
                let kind = token.kind();
                match kind {
                    SyntaxKind::Minus | SyntaxKind::Not => Some(kind),
                    _ => None,
                }
            })
        })
    }
}

/// Typed wrapper for function call nodes (e.g., `f(x, y)`).
///
/// Call nodes have the structure:
/// ```text
/// Call
///   ├─ Expr (callee - can be Ident or complex expression)
///   ├─ LeftParen
///   ├─ Expr (arg 1)
///   ├─ Comma
///   ├─ Expr (arg 2)
///   ├─ ...
///   └─ RightParen
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallNode(CelNode);

impl AstNode for CallNode {
    fn cast(node: CelNode) -> Option<Self> {
        if node.kind() == SyntaxKind::Call {
            Some(Self(node))
        } else {
            None
        }
    }

    fn syntax(&self) -> &CelNode {
        &self.0
    }
}

impl CallNode {
    /// Returns the callee node, if it's a complex expression.
    /// Returns None if callee is an atom (identifier token).
    pub fn callee(&self) -> Option<CelNode> {
        self.0.children().next()
    }

    /// Returns all argument nodes (skipping the callee).
    /// Only returns nodes for complex argument expressions; atom arguments are tokens.
    pub fn args(&self) -> Vec<CelNode> {
        self.0.children().skip(1).collect()
    }
}

/// Typed wrapper for field access nodes (e.g., `obj.field`).
///
/// Field access nodes have the structure:
/// ```text
/// FieldAccess
///   ├─ Expr (target object)
///   ├─ Dot
///   └─ Ident (field name)
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldAccessNode(CelNode);

impl AstNode for FieldAccessNode {
    fn cast(node: CelNode) -> Option<Self> {
        if node.kind() == SyntaxKind::FieldAccess {
            Some(Self(node))
        } else {
            None
        }
    }

    fn syntax(&self) -> &CelNode {
        &self.0
    }
}

impl FieldAccessNode {
    /// Returns the target node, if it's a complex expression.
    /// Returns None if target is an atom token.
    pub fn target(&self) -> Option<CelNode> {
        self.0.children().next()
    }

    /// Returns the field name token.
    pub fn field(&self) -> Option<String> {
        self.0
            .children_with_tokens()
            .filter_map(|child| child.into_token())
            .filter(|token| token.kind() == SyntaxKind::Ident)
            .nth(1) // Skip target identifier, get field name
            .or_else(|| {
                // Fallback: if there's only one Ident, it's the field
                self.0
                    .children_with_tokens()
                    .filter_map(|child| child.into_token())
                    .find(|token| token.kind() == SyntaxKind::Ident)
            })
            .map(|token| token.text().to_string())
    }
}

/// Typed wrapper for index access nodes (e.g., `list[0]`, `map["key"]`).
///
/// Index nodes have the structure:
/// ```text
/// Index
///   ├─ Expr (target - list or map)
///   ├─ LeftBracket
///   ├─ Expr (index expression)
///   └─ RightBracket
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IndexNode(CelNode);

impl AstNode for IndexNode {
    fn cast(node: CelNode) -> Option<Self> {
        if node.kind() == SyntaxKind::Index {
            Some(Self(node))
        } else {
            None
        }
    }

    fn syntax(&self) -> &CelNode {
        &self.0
    }
}

impl IndexNode {
    /// Returns the target node, if it's a complex expression.
    /// Returns None if target is an atom token.
    pub fn target(&self) -> Option<CelNode> {
        self.0.children().next()
    }

    /// Returns the index node, if it's a complex expression.
    /// Returns None if index is an atom token.
    pub fn index(&self) -> Option<CelNode> {
        self.0.children().nth(1)
    }
}

/// Typed wrapper for list literal nodes (e.g., `[1, 2, 3]`).
///
/// List nodes have the structure:
/// ```text
/// List
///   ├─ LeftBracket
///   ├─ Expr (element 1)
///   ├─ Comma
///   ├─ Expr (element 2)
///   ├─ ...
///   └─ RightBracket
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ListNode(CelNode);

impl AstNode for ListNode {
    fn cast(node: CelNode) -> Option<Self> {
        if node.kind() == SyntaxKind::List {
            Some(Self(node))
        } else {
            None
        }
    }

    fn syntax(&self) -> &CelNode {
        &self.0
    }
}

impl ListNode {
    /// Returns all element nodes (excludes atom tokens).
    /// Atom elements are tokens, not nodes, so they won't appear in this list.
    pub fn elements(&self) -> Vec<CelNode> {
        self.0.children().collect()
    }
}

/// Typed wrapper for map literal nodes (e.g., `{a: 1, b: 2}`).
///
/// Map nodes have the structure:
/// ```text
/// Map
///   ├─ LeftBrace
///   ├─ Expr (key 1)
///   ├─ Colon
///   ├─ Expr (value 1)
///   ├─ Comma
///   ├─ Expr (key 2)
///   ├─ Colon
///   ├─ Expr (value 2)
///   ├─ ...
///   └─ RightBrace
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MapNode(CelNode);

impl AstNode for MapNode {
    fn cast(node: CelNode) -> Option<Self> {
        if node.kind() == SyntaxKind::Map {
            Some(Self(node))
        } else {
            None
        }
    }

    fn syntax(&self) -> &CelNode {
        &self.0
    }
}

impl MapNode {
    /// Returns all key-value pairs as (key, value) node tuples.
    /// Only returns pairs where keys/values are complex expressions (nodes).
    /// Atom keys/values (tokens) are not included.
    pub fn entries(&self) -> Vec<(CelNode, CelNode)> {
        let nodes: Vec<_> = self.0.children().collect();
        nodes
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| (pair[0].clone(), pair[1].clone()))
            .collect()
    }
}

/// Typed wrapper for ternary conditional nodes (e.g., `cond ? then_val : else_val`).
///
/// Ternary nodes have the structure:
/// ```text
/// Ternary
///   ├─ Expr (condition)
///   ├─ QuestionMark
///   ├─ Expr (then branch)
///   ├─ Colon
///   └─ Expr (else branch)
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TernaryNode(CelNode);

impl AstNode for TernaryNode {
    fn cast(node: CelNode) -> Option<Self> {
        if node.kind() == SyntaxKind::Ternary {
            Some(Self(node))
        } else {
            None
        }
    }

    fn syntax(&self) -> &CelNode {
        &self.0
    }
}

impl TernaryNode {
    /// Returns the condition node, if it's a complex expression.
    /// Returns None if condition is an atom token.
    pub fn condition(&self) -> Option<CelNode> {
        // Condition is before the QuestionMark token
        self.0
            .children_with_tokens()
            .take_while(|child| {
                !matches!(
                    child.as_token().map(|t| t.kind()),
                    Some(SyntaxKind::QuestionMark)
                )
            })
            .filter_map(|child| child.into_node())
            .next()
    }

    /// Returns the then-branch node, if it's a complex expression.
    /// Returns None if then-branch is an atom token.
    pub fn then_expr(&self) -> Option<CelNode> {
        // Then-branch is between QuestionMark and Colon
        let mut after_question = false;
        self.0
            .children_with_tokens()
            .skip_while(|child| {
                if matches!(
                    child.as_token().map(|t| t.kind()),
                    Some(SyntaxKind::QuestionMark)
                ) {
                    after_question = true;
                    true
                } else {
                    !after_question
                }
            })
            .take_while(|child| {
                !matches!(
                    child.as_token().map(|t| t.kind()),
                    Some(SyntaxKind::Colon)
                )
            })
            .filter_map(|child| child.into_node())
            .next()
    }

    /// Returns the else-branch node, if it's a complex expression.
    /// Returns None if else-branch is an atom token.
    pub fn else_expr(&self) -> Option<CelNode> {
        // Else-branch is after Colon
        self.0
            .children_with_tokens()
            .skip_while(|child| {
                !matches!(
                    child.as_token().map(|t| t.kind()),
                    Some(SyntaxKind::Colon)
                )
            })
            .skip(1) // Skip the Colon itself
            .filter_map(|child| child.into_node())
            .next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::parser::parse;

    fn parse_expr(input: &str) -> CelNode {
        let green = parse(input).expect("parse failed");
        let root = SyntaxNode::new_root(green);
        // Get the first Expr child under Root
        root.children()
            .find(|child| child.kind() == SyntaxKind::Expr)
            .expect("no Expr node found")
    }

    #[test]
    fn test_binary_op_wrapper() {
        let root = parse_expr("1 + 2");
        let expr_children: Vec<_> = root
            .children()
            .filter(|n| n.kind() == SyntaxKind::BinaryOp)
            .collect();
        assert_eq!(expr_children.len(), 1, "expected one BinaryOp node");

        let bin_op =
            BinaryOpNode::cast(expr_children[0].clone()).expect("cast failed");
        assert_eq!(bin_op.operator(), Some(SyntaxKind::Plus));
        assert!(bin_op.lhs().is_none(), "atom operands have no child nodes");
        assert!(bin_op.rhs().is_none(), "atom operands have no child nodes");
    }

    #[test]
    fn test_binary_op_precedence() {
        let root = parse_expr("1 + 2 * 3");
        let binary_ops: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::BinaryOp)
            .collect();
        assert_eq!(binary_ops.len(), 2);

        let plus_node =
            BinaryOpNode::cast(binary_ops[0].clone()).expect("cast failed");
        assert_eq!(plus_node.operator(), Some(SyntaxKind::Plus));
        assert!(plus_node.lhs().is_none(), "lhs is atom");
        assert!(plus_node.rhs().is_some(), "rhs is BinaryOp node");

        let mult_node =
            BinaryOpNode::cast(binary_ops[1].clone()).expect("cast failed");
        assert_eq!(mult_node.operator(), Some(SyntaxKind::Star));
    }

    #[test]
    fn test_unary_op_wrapper() {
        let root = parse_expr("-5");
        let unary_ops: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::UnaryOp)
            .collect();
        assert_eq!(unary_ops.len(), 1);

        let unary =
            UnaryOpNode::cast(unary_ops[0].clone()).expect("cast failed");
        assert_eq!(unary.operator(), Some(SyntaxKind::Minus));
        assert!(unary.operand().is_none(), "atom operand has no child node");
    }

    #[test]
    fn test_unary_not_wrapper() {
        let root = parse_expr("!true");
        let unary_ops: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::UnaryOp)
            .collect();
        assert_eq!(unary_ops.len(), 1);

        let unary =
            UnaryOpNode::cast(unary_ops[0].clone()).expect("cast failed");
        assert_eq!(unary.operator(), Some(SyntaxKind::Not));
        assert!(unary.operand().is_none(), "atom operand has no child node");
    }

    #[test]
    fn test_call_wrapper() {
        let root = parse_expr("foo(a, b, c)");
        let calls: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::Call)
            .collect();
        assert_eq!(calls.len(), 1);

        let call = CallNode::cast(calls[0].clone()).expect("cast failed");
        assert!(call.callee().is_none(), "callee is identifier token");
        let args = call.args();
        assert_eq!(args.len(), 0, "all args are atom tokens");
    }

    #[test]
    fn test_call_no_args() {
        let root = parse_expr("bar()");
        let calls: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::Call)
            .collect();
        assert_eq!(calls.len(), 1);

        let call = CallNode::cast(calls[0].clone()).expect("cast failed");
        assert!(call.callee().is_none(), "callee is identifier token");
        let args = call.args();
        assert_eq!(args.len(), 0, "no arguments");
    }

    #[test]
    fn test_field_access_wrapper() {
        let root = parse_expr("obj.field");
        let field_accesses: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::FieldAccess)
            .collect();
        assert_eq!(field_accesses.len(), 1);

        let field = FieldAccessNode::cast(field_accesses[0].clone())
            .expect("cast failed");
        assert!(field.target().is_none(), "target is identifier token");
        assert_eq!(field.field(), Some("field".to_string()));
    }

    #[test]
    fn test_field_access_chain() {
        let root = parse_expr("a.b.c");
        let field_accesses: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::FieldAccess)
            .collect();
        assert_eq!(field_accesses.len(), 2, "expected 2 field accesses");

        // Outer field access (a.b).c
        let outer = FieldAccessNode::cast(field_accesses[0].clone())
            .expect("cast failed");
        assert_eq!(outer.field(), Some("c".to_string()));
        assert!(outer.target().is_some(), "target is inner FieldAccess node");

        // Inner field access a.b
        let inner = FieldAccessNode::cast(field_accesses[1].clone())
            .expect("cast failed");
        assert_eq!(inner.field(), Some("b".to_string()));
        assert!(inner.target().is_none(), "target is identifier token");
    }

    #[test]
    fn test_index_wrapper() {
        let root = parse_expr("list[0]");
        let indexes: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::Index)
            .collect();
        assert_eq!(indexes.len(), 1);

        let index = IndexNode::cast(indexes[0].clone()).expect("cast failed");
        assert!(index.target().is_none(), "target is identifier token");
        assert!(index.index().is_none(), "index is int token");
    }

    #[test]
    fn test_list_wrapper() {
        let root = parse_expr("[1, 2, 3]");
        let lists: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::List)
            .collect();
        assert_eq!(lists.len(), 1);

        let list = ListNode::cast(lists[0].clone()).expect("cast failed");
        let elements = list.elements();
        assert_eq!(elements.len(), 0, "all elements are atom tokens");
    }

    #[test]
    fn test_list_empty() {
        let root = parse_expr("[]");
        let lists: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::List)
            .collect();
        assert_eq!(lists.len(), 1);

        let list = ListNode::cast(lists[0].clone()).expect("cast failed");
        let elements = list.elements();
        assert_eq!(elements.len(), 0, "expected empty list");
    }

    #[test]
    fn test_map_wrapper() {
        let root = parse_expr(r#"{"a": 1, "b": 2}"#);
        let maps: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::Map)
            .collect();
        assert_eq!(maps.len(), 1);

        let map = MapNode::cast(maps[0].clone()).expect("cast failed");
        let entries = map.entries();
        assert_eq!(entries.len(), 0, "all keys/values are atom tokens");
    }

    #[test]
    fn test_map_empty() {
        let root = parse_expr("{}");
        let maps: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::Map)
            .collect();
        assert_eq!(maps.len(), 1);

        let map = MapNode::cast(maps[0].clone()).expect("cast failed");
        let entries = map.entries();
        assert_eq!(entries.len(), 0, "expected empty map");
    }

    #[test]
    fn test_ternary_wrapper() {
        let root = parse_expr("x ? y : z");
        let ternaries: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::Ternary)
            .collect();
        assert_eq!(ternaries.len(), 1);

        let ternary =
            TernaryNode::cast(ternaries[0].clone()).expect("cast failed");
        assert!(
            ternary.condition().is_none(),
            "condition is identifier token"
        );
        assert!(
            ternary.then_expr().is_none(),
            "then branch is identifier token"
        );
        assert!(
            ternary.else_expr().is_none(),
            "else branch is identifier token"
        );
    }

    #[test]
    fn test_ternary_nested() {
        let root = parse_expr("a ? b : c ? d : e");
        let ternaries: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::Ternary)
            .collect();
        assert_eq!(ternaries.len(), 2, "expected nested ternaries");

        let outer =
            TernaryNode::cast(ternaries[0].clone()).expect("cast failed");
        assert!(outer.condition().is_none(), "condition is identifier token");
        assert!(
            outer.then_expr().is_none(),
            "then branch is identifier token"
        );
        assert!(
            outer.else_expr().is_some(),
            "else branch is inner Ternary node"
        );
    }

    #[test]
    fn test_cast_wrong_kind_returns_none() {
        let root = parse_expr("1 + 2");
        let binary_ops: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::BinaryOp)
            .collect();
        assert_eq!(binary_ops.len(), 1);

        // Try to cast BinaryOp as UnaryOp - should fail
        assert!(UnaryOpNode::cast(binary_ops[0].clone()).is_none());
        assert!(CallNode::cast(binary_ops[0].clone()).is_none());
        assert!(ListNode::cast(binary_ops[0].clone()).is_none());
    }

    #[test]
    fn test_complex_chaining() {
        let root = parse_expr("foo.bar(baz)[0]");
        // Should have Call, FieldAccess, and Index
        assert!(
            root.descendants()
                .any(|n| n.kind() == SyntaxKind::FieldAccess)
        );
        assert!(root.descendants().any(|n| n.kind() == SyntaxKind::Call));
        assert!(root.descendants().any(|n| n.kind() == SyntaxKind::Index));
    }
}
