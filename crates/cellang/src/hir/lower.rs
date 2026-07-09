use crate::hir::expr::{Atom, BinaryOp, Expr, UnaryOp};
use crate::lexer::Token;
use crate::syntax::ast::{
    AstNode, BinaryOpNode, CallNode, CelNode, FieldAccessNode, IndexNode,
    ListNode, MapNode, TernaryNode, UnaryOpNode,
};
use crate::syntax::{ParseResult, SyntaxKind, parser};
use rowan::{NodeOrToken, SyntaxNode, SyntaxToken};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerErrorKind {
    ParseFailure,
    UnsupportedNode,
    UnsupportedToken,
    MalformedSyntax,
    MissingOperand,
    InvalidLiteral,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LowerError {
    pub kind: LowerErrorKind,
    pub message: String,
    pub span: Option<(usize, usize)>,
}

impl LowerError {
    fn new(kind: LowerErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
            span: None,
        }
    }

    fn at_node(
        kind: LowerErrorKind,
        message: impl Into<String>,
        node: &CelNode,
    ) -> Self {
        let range = node.text_range();
        Self {
            kind,
            message: message.into(),
            span: Some((
                u32::from(range.start()) as usize,
                u32::from(range.end()) as usize,
            )),
        }
    }

    fn at_token(
        kind: LowerErrorKind,
        message: impl Into<String>,
        token: &SyntaxToken<crate::syntax::CelLanguage>,
    ) -> Self {
        let range = token.text_range();
        Self {
            kind,
            message: message.into(),
            span: Some((
                u32::from(range.start()) as usize,
                u32::from(range.end()) as usize,
            )),
        }
    }
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for LowerError {}

pub fn lower_source(input: &str) -> Result<Expr, LowerError> {
    let parsed = parser::parse(input).map_err(|err| {
        LowerError::new(LowerErrorKind::ParseFailure, err.message)
    })?;
    lower(parsed)
}

pub fn lower(parse_result: ParseResult) -> Result<Expr, LowerError> {
    let root = SyntaxNode::new_root(parse_result);
    let root_expr = root
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)
        .ok_or_else(|| {
            LowerError::new(
                LowerErrorKind::MalformedSyntax,
                "missing root expression node",
            )
        })?;
    lower_node(&root_expr)
}

fn lower_node(node: &CelNode) -> Result<Expr, LowerError> {
    match node.kind() {
        SyntaxKind::Expr => lower_expr_wrapper(node),
        SyntaxKind::UnaryOp => lower_unary(node),
        SyntaxKind::BinaryOp => lower_binary(node),
        SyntaxKind::Call => lower_call(node),
        SyntaxKind::FieldAccess => lower_field(node),
        SyntaxKind::Index => lower_index(node),
        SyntaxKind::List => lower_list(node),
        SyntaxKind::Map => lower_map(node),
        SyntaxKind::Ternary => lower_ternary(node),
        SyntaxKind::Error => Err(LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "malformed syntax node",
            node,
        )),
        other => Err(LowerError::at_node(
            LowerErrorKind::UnsupportedNode,
            format!("unsupported syntax node kind: {other:?}"),
            node,
        )),
    }
}

fn lower_expr_wrapper(node: &CelNode) -> Result<Expr, LowerError> {
    let mut first_token_kind = None;
    for child in node.children_with_tokens() {
        if let NodeOrToken::Token(token) = child {
            first_token_kind = Some(token.kind());
            break;
        }
    }

    match first_token_kind {
        Some(SyntaxKind::Dyn) => {
            let inner = extract_expr_between(
                node,
                Some(SyntaxKind::LeftParen),
                Some(SyntaxKind::RightParen),
                "dyn",
            )?;
            Ok(Expr::Dyn(Box::new(inner)))
        }
        Some(SyntaxKind::LeftParen) => {
            let inner = extract_expr_between(
                node,
                Some(SyntaxKind::LeftParen),
                Some(SyntaxKind::RightParen),
                "group",
            )?;
            Ok(Expr::Group(Box::new(inner)))
        }
        _ => first_expr_from_node(node, "expression"),
    }
}

fn lower_unary(node: &CelNode) -> Result<Expr, LowerError> {
    let unary = UnaryOpNode::cast(node.clone()).ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "failed to cast unary operation node",
            node,
        )
    })?;

    let op_kind = unary.operator().ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "missing unary operator",
            node,
        )
    })?;

    let op = match op_kind {
        SyntaxKind::Minus => UnaryOp::Neg,
        SyntaxKind::Not => UnaryOp::Not,
        _ => {
            return Err(LowerError::at_node(
                LowerErrorKind::UnsupportedToken,
                format!("unsupported unary operator: {op_kind:?}"),
                unary.syntax(),
            ));
        }
    };

    let expr = if let Some(operand) = unary.operand() {
        lower_node(&operand)?
    } else {
        let mut seen_op = false;
        let mut operand = None;
        for child in unary.syntax().children_with_tokens() {
            if let NodeOrToken::Token(token) = &child
                && token.kind() == op_kind
                && !seen_op
            {
                seen_op = true;
                continue;
            }
            if !seen_op {
                continue;
            }

            if let Some(expr) = maybe_lower_element(child)? {
                operand = Some(expr);
                break;
            }
        }

        operand.ok_or_else(|| {
            LowerError::at_node(
                LowerErrorKind::MissingOperand,
                "missing unary operand",
                unary.syntax(),
            )
        })?
    };

    Ok(Expr::Unary {
        op,
        expr: Box::new(expr),
    })
}

fn lower_binary(node: &CelNode) -> Result<Expr, LowerError> {
    let binary = BinaryOpNode::cast(node.clone()).ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "failed to cast binary operation node",
            node,
        )
    })?;

    let op_kind = binary.operator().ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "missing binary operator",
            binary.syntax(),
        )
    })?;

    let op = match op_kind {
        SyntaxKind::Plus => BinaryOp::Add,
        SyntaxKind::Minus => BinaryOp::Sub,
        SyntaxKind::Star => BinaryOp::Mul,
        SyntaxKind::Slash => BinaryOp::Div,
        SyntaxKind::Percent => BinaryOp::Mod,
        SyntaxKind::EqualEqual => BinaryOp::Eq,
        SyntaxKind::NotEqual => BinaryOp::Ne,
        SyntaxKind::Less => BinaryOp::Lt,
        SyntaxKind::LessEqual => BinaryOp::Le,
        SyntaxKind::Greater => BinaryOp::Gt,
        SyntaxKind::GreaterEqual => BinaryOp::Ge,
        SyntaxKind::And => BinaryOp::And,
        SyntaxKind::Or => BinaryOp::Or,
        SyntaxKind::In => BinaryOp::In,
        _ => {
            return Err(LowerError::at_node(
                LowerErrorKind::UnsupportedToken,
                format!("unsupported binary operator: {op_kind:?}"),
                binary.syntax(),
            ));
        }
    };

    let mut seen_op = false;
    let mut lhs = None;
    let mut rhs = None;

    for child in binary.syntax().children_with_tokens() {
        if let NodeOrToken::Token(token) = &child
            && token.kind() == op_kind
            && !seen_op
        {
            seen_op = true;
            continue;
        }

        if !seen_op {
            if lhs.is_none() {
                lhs = maybe_lower_element(child)?;
            }
        } else if rhs.is_none() {
            rhs = maybe_lower_element(child)?;
        }
    }

    let lhs = lhs.ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MissingOperand,
            "missing binary left operand",
            binary.syntax(),
        )
    })?;
    let rhs = rhs.ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MissingOperand,
            "missing binary right operand",
            binary.syntax(),
        )
    })?;

    Ok(Expr::Binary {
        op,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    })
}

fn lower_call(node: &CelNode) -> Result<Expr, LowerError> {
    let call = CallNode::cast(node.clone()).ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "failed to cast call node",
            node,
        )
    })?;

    let _ = call.args();

    let mut callee = None;
    let mut args = Vec::new();
    let mut in_args = false;

    for child in call.syntax().children_with_tokens() {
        if let NodeOrToken::Token(token) = &child {
            match token.kind() {
                SyntaxKind::LeftParen => {
                    in_args = true;
                    continue;
                }
                SyntaxKind::RightParen | SyntaxKind::Comma => continue,
                _ => {}
            }
        }

        if !in_args {
            if callee.is_none() {
                callee = maybe_lower_element(child)?;
            }
        } else if let Some(arg) = maybe_lower_element(child)? {
            args.push(arg);
        }
    }

    let callee = if let Some(c) = callee {
        c
    } else if let Some(callee_node) = call.callee() {
        lower_node(&callee_node)?
    } else {
        return Err(LowerError::at_node(
            LowerErrorKind::MissingOperand,
            "missing call target",
            call.syntax(),
        ));
    };

    if let Expr::Field { target, field } = callee {
        Ok(Expr::Call {
            func: Box::new(Expr::Atom(Atom::Ident(field))),
            args: std::iter::once(*target).chain(args).collect(),
            is_method: true,
        })
    } else {
        Ok(Expr::Call {
            func: Box::new(callee),
            args,
            is_method: false,
        })
    }
}

fn lower_field(node: &CelNode) -> Result<Expr, LowerError> {
    let field = FieldAccessNode::cast(node.clone()).ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "failed to cast field access node",
            node,
        )
    })?;

    let field_name = field.field().ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MissingOperand,
            "missing field identifier",
            field.syntax(),
        )
    })?;

    let target = if let Some(target) = field.target() {
        lower_node(&target)?
    } else {
        let mut seen_dot = false;
        let mut target = None;
        for child in field.syntax().children_with_tokens() {
            if let NodeOrToken::Token(token) = &child
                && token.kind() == SyntaxKind::Dot
                && !seen_dot
            {
                seen_dot = true;
                continue;
            }

            if seen_dot {
                break;
            }

            if target.is_none() {
                target = maybe_lower_element(child)?;
            }
        }
        target.ok_or_else(|| {
            LowerError::at_node(
                LowerErrorKind::MissingOperand,
                "missing field access target",
                field.syntax(),
            )
        })?
    };

    Ok(Expr::Field {
        target: Box::new(target),
        field: field_name,
    })
}

fn lower_index(node: &CelNode) -> Result<Expr, LowerError> {
    let index = IndexNode::cast(node.clone()).ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "failed to cast index node",
            node,
        )
    })?;

    let mut target = None;
    let mut bracket_open = false;
    let mut idx = None;

    for child in index.syntax().children_with_tokens() {
        if let NodeOrToken::Token(token) = &child {
            match token.kind() {
                SyntaxKind::LeftBracket => {
                    bracket_open = true;
                    continue;
                }
                SyntaxKind::RightBracket => continue,
                _ => {}
            }
        }

        if !bracket_open {
            if target.is_none() {
                target = maybe_lower_element(child)?;
            }
        } else if idx.is_none() {
            idx = maybe_lower_element(child)?;
        }
    }

    let target = if let Some(target_node) = index.target() {
        lower_node(&target_node)?
    } else {
        target.ok_or_else(|| {
            LowerError::at_node(
                LowerErrorKind::MissingOperand,
                "missing index target",
                index.syntax(),
            )
        })?
    };

    let idx = if let Some(index_node) = index.index() {
        lower_node(&index_node)?
    } else {
        idx.ok_or_else(|| {
            LowerError::at_node(
                LowerErrorKind::MissingOperand,
                "missing index expression",
                index.syntax(),
            )
        })?
    };

    Ok(Expr::Index {
        target: Box::new(target),
        index: Box::new(idx),
    })
}

fn lower_list(node: &CelNode) -> Result<Expr, LowerError> {
    let list = ListNode::cast(node.clone()).ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "failed to cast list node",
            node,
        )
    })?;

    let _ = list.elements();

    let mut items = Vec::new();
    for child in list.syntax().children_with_tokens() {
        if let NodeOrToken::Token(token) = &child
            && matches!(
                token.kind(),
                SyntaxKind::LeftBracket
                    | SyntaxKind::RightBracket
                    | SyntaxKind::Comma
            )
        {
            continue;
        }

        if let Some(item) = maybe_lower_element(child)? {
            items.push(item);
        }
    }

    Ok(Expr::List(items))
}

fn lower_map(node: &CelNode) -> Result<Expr, LowerError> {
    let map = MapNode::cast(node.clone()).ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "failed to cast map node",
            node,
        )
    })?;

    let _ = map.entries();

    let mut flat = Vec::new();
    for child in map.syntax().children_with_tokens() {
        if let NodeOrToken::Token(token) = &child
            && matches!(
                token.kind(),
                SyntaxKind::LeftBrace
                    | SyntaxKind::RightBrace
                    | SyntaxKind::Colon
                    | SyntaxKind::Comma
            )
        {
            continue;
        }

        if let Some(item) = maybe_lower_element(child)? {
            flat.push(item);
        }
    }

    if flat.len() % 2 != 0 {
        return Err(LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "map literal must have key/value pairs",
            map.syntax(),
        ));
    }

    let entries = flat
        .chunks_exact(2)
        .map(|pair| (pair[0].clone(), pair[1].clone()))
        .collect();

    Ok(Expr::Map(entries))
}

fn lower_ternary(node: &CelNode) -> Result<Expr, LowerError> {
    let ternary = TernaryNode::cast(node.clone()).ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MalformedSyntax,
            "failed to cast ternary node",
            node,
        )
    })?;

    let mut cond = None;
    let mut then_expr = None;
    let mut else_expr = None;
    let mut phase = 0;

    for child in ternary.syntax().children_with_tokens() {
        if let NodeOrToken::Token(token) = &child {
            match token.kind() {
                SyntaxKind::QuestionMark => {
                    phase = 1;
                    continue;
                }
                SyntaxKind::Colon => {
                    phase = 2;
                    continue;
                }
                _ => {}
            }
        }

        match phase {
            0 if cond.is_none() => cond = maybe_lower_element(child)?,
            1 if then_expr.is_none() => then_expr = maybe_lower_element(child)?,
            2 if else_expr.is_none() => else_expr = maybe_lower_element(child)?,
            _ => {}
        }
    }

    let cond = if let Some(node) = ternary.condition() {
        lower_node(&node)?
    } else {
        cond.ok_or_else(|| {
            LowerError::at_node(
                LowerErrorKind::MissingOperand,
                "missing ternary condition",
                ternary.syntax(),
            )
        })?
    };

    let then_expr = if let Some(node) = ternary.then_expr() {
        lower_node(&node)?
    } else {
        then_expr.ok_or_else(|| {
            LowerError::at_node(
                LowerErrorKind::MissingOperand,
                "missing ternary then branch",
                ternary.syntax(),
            )
        })?
    };

    let else_expr = if let Some(node) = ternary.else_expr() {
        lower_node(&node)?
    } else {
        else_expr.ok_or_else(|| {
            LowerError::at_node(
                LowerErrorKind::MissingOperand,
                "missing ternary else branch",
                ternary.syntax(),
            )
        })?
    };

    Ok(Expr::Ternary {
        cond: Box::new(cond),
        then_expr: Box::new(then_expr),
        else_expr: Box::new(else_expr),
    })
}

fn extract_expr_between(
    node: &CelNode,
    start_delim: Option<SyntaxKind>,
    end_delim: Option<SyntaxKind>,
    context: &str,
) -> Result<Expr, LowerError> {
    let mut in_range = start_delim.is_none();
    let mut expr = None;

    for child in node.children_with_tokens() {
        if let NodeOrToken::Token(token) = &child {
            if start_delim.is_some_and(|start| token.kind() == start) {
                in_range = true;
                continue;
            }
            if end_delim.is_some_and(|end| token.kind() == end) {
                break;
            }
        }

        if !in_range {
            continue;
        }

        if expr.is_none() {
            expr = maybe_lower_element(child)?;
        }
    }

    expr.ok_or_else(|| {
        LowerError::at_node(
            LowerErrorKind::MissingOperand,
            format!("missing inner expression for {context}"),
            node,
        )
    })
}

fn first_expr_from_node(
    node: &CelNode,
    context: &str,
) -> Result<Expr, LowerError> {
    for child in node.children_with_tokens() {
        if let Some(expr) = maybe_lower_element(child)? {
            return Ok(expr);
        }
    }
    Err(LowerError::at_node(
        LowerErrorKind::MissingOperand,
        format!("missing operand in {context}"),
        node,
    ))
}

fn maybe_lower_element(
    element: NodeOrToken<CelNode, SyntaxToken<crate::syntax::CelLanguage>>,
) -> Result<Option<Expr>, LowerError> {
    match element {
        NodeOrToken::Node(node) => Ok(Some(lower_node(&node)?)),
        NodeOrToken::Token(token) => {
            if is_atom_token(token.kind()) {
                Ok(Some(Expr::Atom(lower_atom_token(&token)?)))
            } else if token.kind() == SyntaxKind::Error {
                Err(LowerError::at_token(
                    LowerErrorKind::MalformedSyntax,
                    "malformed token",
                    &token,
                ))
            } else {
                Ok(None)
            }
        }
    }
}

fn is_atom_token(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Ident
            | SyntaxKind::Int
            | SyntaxKind::Uint
            | SyntaxKind::Double
            | SyntaxKind::String
            | SyntaxKind::RawString
            | SyntaxKind::Bytes
            | SyntaxKind::RawBytes
            | SyntaxKind::True
            | SyntaxKind::False
            | SyntaxKind::Null
    )
}

fn lower_atom_token(
    token: &SyntaxToken<crate::syntax::CelLanguage>,
) -> Result<Atom, LowerError> {
    let text = token.text();
    match token.kind() {
        SyntaxKind::Ident => Ok(Atom::Ident(text.to_string())),
        SyntaxKind::Int => text.parse::<i64>().map(Atom::Int).map_err(|err| {
            LowerError::at_token(
                LowerErrorKind::InvalidLiteral,
                format!("invalid int literal '{text}': {err}"),
                token,
            )
        }),
        SyntaxKind::Uint => {
            let normalized = text.trim_end_matches(['u', 'U']);
            normalized.parse::<u64>().map(Atom::Uint).map_err(|err| {
                LowerError::at_token(
                    LowerErrorKind::InvalidLiteral,
                    format!("invalid uint literal '{text}': {err}"),
                    token,
                )
            })
        }
        SyntaxKind::Double => {
            text.parse::<f64>().map(Atom::Double).map_err(|err| {
                LowerError::at_token(
                    LowerErrorKind::InvalidLiteral,
                    format!("invalid double literal '{text}': {err}"),
                    token,
                )
            })
        }
        SyntaxKind::String | SyntaxKind::RawString => {
            Ok(Atom::String(Token::unescape(text).into_owned()))
        }
        SyntaxKind::Bytes | SyntaxKind::RawBytes => {
            Ok(Atom::Bytes(Token::unescape_bytes(text).into_owned()))
        }
        SyntaxKind::True => Ok(Atom::Bool(true)),
        SyntaxKind::False => Ok(Atom::Bool(false)),
        SyntaxKind::Null => Ok(Atom::Null),
        _ => Err(LowerError::at_token(
            LowerErrorKind::UnsupportedToken,
            format!("unsupported atom token: {:?}", token.kind()),
            token,
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rowan::GreenNodeBuilder;

    const SUCCESS_FIXTURES: &[(&str, &str)] = &[
        ("1 + 2 * 3", "precedence_mul_add"),
        ("a - b - c", "associativity_left_sub"),
        ("a / b / c", "associativity_left_div"),
        ("-5", "unary_minus"),
        ("!x", "unary_not"),
        ("-a * b", "unary_minus_mul"),
        ("foo(a, b)", "call_basic"),
        ("foo()", "call_empty"),
        ("foo([])", "call_empty_list"),
        ("foo({})", "call_empty_map"),
        ("a.b(c)", "method_call"),
        ("a.b(c).d", "method_field_chain"),
        ("foo.bar().baz()", "method_chain"),
        ("foo.bar().baz().qux()", "long_method_chain"),
        ("foo.all(test, test.size() > 4)", "nested_method_call"),
        ("a.b.c", "field_chain"),
        ("foo.bar.baz", "field_chain_3"),
        ("list[0]", "index_basic"),
        ("map[\"key\"]", "index_string_key"),
        ("a[b][c]", "index_chain"),
        ("foo[1][2]", "index_chain_numeric"),
        ("foo.check[0].baz", "field_index_field"),
        (
            "foo.bar.filter(x, x > 10)[0].id",
            "nested_method_index_field",
        ),
        ("foo.bar(x, t[x] > 10)", "method_with_index_arg"),
        ("a ? b : c", "ternary_basic"),
        ("x ? y ? z : w : v", "ternary_nested"),
        ("true ? 1 : false ? 2 : 3", "ternary_nested_else"),
        ("[1, 2, 3]", "list_basic"),
        ("[]", "list_empty"),
        ("[{foo: 1}, {bar: 2}]", "list_nested_maps"),
        ("{\"key\": value}", "map_string_key"),
        ("{foo: 1, bar: 2}", "map_ident_keys"),
        ("{}", "map_empty"),
        ("a && b || c", "logical_precedence"),
        ("1 < 2 && 3 >= 4 || 5 == 6 && 5 in 6", "relations_complex"),
        ("(1 + 2) * 3 % 4", "grouping_precedence"),
        ("has(x.y)", "macro_has_field"),
        ("all(items, i, i > 0)", "macro_all"),
        ("exists(items, i, i == target)", "macro_exists"),
        ("exists_one(items, i, i > 0)", "macro_exists_one"),
        ("map(items, i, i * 2)", "macro_map_transform"),
        ("map(items, i, i > 0, i * 2)", "macro_map_filter_transform"),
        ("filter(items, i, i > 0)", "macro_filter"),
        ("identifier", "atom_ident"),
        ("123", "atom_int"),
        ("123u", "atom_uint"),
        ("123.456", "atom_double"),
        ("true", "atom_true"),
        ("false", "atom_false"),
        ("\"string\"", "atom_string"),
        ("null", "atom_null"),
        ("1 + size(2u)", "inline_function_call"),
        ("1 + dyn(2u)", "inline_dyn_call"),
        ("foo.bar() < 4", "method_relation"),
    ];

    #[test]
    fn lowers_all_success_fixtures() {
        for (input, name) in SUCCESS_FIXTURES {
            let lowered = lower_source(input);
            assert!(
                lowered.is_ok(),
                "fixture '{name}' failed for input '{input}': {:?}",
                lowered.err()
            );
        }
    }

    #[test]
    fn lowers_operator_precedence() {
        let got = lower_source("1 + 2 * 3").expect("lowering should succeed");
        let expected = Expr::Binary {
            op: BinaryOp::Add,
            lhs: Box::new(Expr::Atom(Atom::Int(1))),
            rhs: Box::new(Expr::Binary {
                op: BinaryOp::Mul,
                lhs: Box::new(Expr::Atom(Atom::Int(2))),
                rhs: Box::new(Expr::Atom(Atom::Int(3))),
            }),
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn lowers_method_call_shape() {
        let got =
            lower_source("obj.method(arg)").expect("lowering should succeed");
        let expected = Expr::Call {
            func: Box::new(Expr::Atom(Atom::Ident("method".to_string()))),
            args: vec![
                Expr::Atom(Atom::Ident("obj".to_string())),
                Expr::Atom(Atom::Ident("arg".to_string())),
            ],
            is_method: true,
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn lowers_field_chain_shape() {
        let got = lower_source("a.b.c").expect("lowering should succeed");
        let expected = Expr::Field {
            target: Box::new(Expr::Field {
                target: Box::new(Expr::Atom(Atom::Ident("a".to_string()))),
                field: "b".to_string(),
            }),
            field: "c".to_string(),
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn lowers_ternary_shape() {
        let got = lower_source("a ? b : c").expect("lowering should succeed");
        let expected = Expr::Ternary {
            cond: Box::new(Expr::Atom(Atom::Ident("a".to_string()))),
            then_expr: Box::new(Expr::Atom(Atom::Ident("b".to_string()))),
            else_expr: Box::new(Expr::Atom(Atom::Ident("c".to_string()))),
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn lowers_nested_ternary_shape() {
        let got = lower_source("true ? 1 : false ? 2 : 3")
            .expect("lowering should succeed");
        let expected = Expr::Ternary {
            cond: Box::new(Expr::Atom(Atom::Bool(true))),
            then_expr: Box::new(Expr::Atom(Atom::Int(1))),
            else_expr: Box::new(Expr::Ternary {
                cond: Box::new(Expr::Atom(Atom::Bool(false))),
                then_expr: Box::new(Expr::Atom(Atom::Int(2))),
                else_expr: Box::new(Expr::Atom(Atom::Int(3))),
            }),
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn lowers_list_and_map_shapes() {
        let list =
            lower_source("[1, 2]").expect("list lowering should succeed");
        assert_eq!(
            list,
            Expr::List(vec![
                Expr::Atom(Atom::Int(1)),
                Expr::Atom(Atom::Int(2))
            ])
        );

        let map = lower_source("{foo: 1, bar: 2}")
            .expect("map lowering should succeed");
        assert_eq!(
            map,
            Expr::Map(vec![
                (
                    Expr::Atom(Atom::Ident("foo".to_string())),
                    Expr::Atom(Atom::Int(1)),
                ),
                (
                    Expr::Atom(Atom::Ident("bar".to_string())),
                    Expr::Atom(Atom::Int(2)),
                ),
            ])
        );
    }

    #[test]
    fn lowers_list_and_map_empty_shapes() {
        let list =
            lower_source("[]").expect("empty list lowering should succeed");
        assert_eq!(list, Expr::List(vec![]));

        let map =
            lower_source("{}").expect("empty map lowering should succeed");
        assert_eq!(map, Expr::Map(vec![]));
    }

    #[test]
    fn lowers_index_shapes() {
        let got = lower_source("foo[1]").expect("lowering should succeed");
        let expected = Expr::Index {
            target: Box::new(Expr::Atom(Atom::Ident("foo".to_string()))),
            index: Box::new(Expr::Atom(Atom::Int(1))),
        };
        assert_eq!(got, expected);

        let got = lower_source("foo[1][2]").expect("lowering should succeed");
        let expected = Expr::Index {
            target: Box::new(Expr::Index {
                target: Box::new(Expr::Atom(Atom::Ident("foo".to_string()))),
                index: Box::new(Expr::Atom(Atom::Int(1))),
            }),
            index: Box::new(Expr::Atom(Atom::Int(2))),
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn lowers_field_chain_with_index_shape() {
        let got =
            lower_source("foo.check[0].baz").expect("lowering should succeed");
        let expected = Expr::Field {
            target: Box::new(Expr::Index {
                target: Box::new(Expr::Field {
                    target: Box::new(Expr::Atom(Atom::Ident(
                        "foo".to_string(),
                    ))),
                    field: "check".to_string(),
                }),
                index: Box::new(Expr::Atom(Atom::Int(0))),
            }),
            field: "baz".to_string(),
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn malformed_input_reports_parse_failure_deterministically() {
        let err = lower_source("foo(").expect_err("lowering should fail");
        assert_eq!(err.kind, LowerErrorKind::ParseFailure);
        assert!(err.message.contains("continuing argument list"));
    }

    #[test]
    fn unsupported_node_reports_deterministic_error() {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(SyntaxKind::Root.into());
        builder.start_node(SyntaxKind::Expr.into());
        builder.start_node(SyntaxKind::Root.into());
        builder.finish_node();
        builder.finish_node();
        builder.finish_node();
        let tree = builder.finish();

        let err = lower(tree).expect_err("lowering should fail");
        assert_eq!(err.kind, LowerErrorKind::UnsupportedNode);
        assert!(err.message.contains("unsupported syntax node kind"));
    }

    #[test]
    fn missing_operand_reports_deterministic_error() {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(SyntaxKind::Root.into());
        builder.start_node(SyntaxKind::Expr.into());
        builder.start_node(SyntaxKind::BinaryOp.into());
        builder.token(SyntaxKind::Int.into(), "1");
        builder.token(SyntaxKind::Plus.into(), "+");
        builder.finish_node();
        builder.finish_node();
        builder.finish_node();
        let tree = builder.finish();

        let err = lower(tree).expect_err("lowering should fail");
        assert_eq!(err.kind, LowerErrorKind::MissingOperand);
        assert!(err.message.contains("missing binary right operand"));
    }
}
