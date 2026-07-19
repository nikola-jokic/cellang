use cellang::SyntaxKind;
use rowan::{NodeOrToken, SyntaxToken};
use serde_json::{Value, json};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FormatterErrorKind {
    ParseFailure,
    UnsupportedConstruct,
    InvalidSyntaxTree,
}

impl FormatterErrorKind {
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::ParseFailure => "parse_failure",
            Self::UnsupportedConstruct => "unsupported_construct",
            Self::InvalidSyntaxTree => "invalid_syntax_tree",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormatterError {
    kind: FormatterErrorKind,
    message: String,
}

impl FormatterError {
    #[must_use]
    pub fn kind(&self) -> &FormatterErrorKind {
        &self.kind
    }

    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }

    #[must_use]
    pub fn to_response_data(&self) -> Value {
        json!({
            "kind": self.kind.as_str(),
            "message": self.message,
        })
    }

    fn parse_failure(message: String) -> Self {
        Self {
            kind: FormatterErrorKind::ParseFailure,
            message,
        }
    }

    fn unsupported_construct(message: impl Into<String>) -> Self {
        Self {
            kind: FormatterErrorKind::UnsupportedConstruct,
            message: format!(
                "Formatting unsupported construct: {}",
                message.into()
            ),
        }
    }

    fn invalid_syntax_tree(message: impl Into<String>) -> Self {
        Self {
            kind: FormatterErrorKind::InvalidSyntaxTree,
            message: format!(
                "Formatting invalid syntax tree: {}",
                message.into()
            ),
        }
    }
}

impl std::fmt::Display for FormatterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for FormatterError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Associativity {
    Left,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BinaryOperator {
    symbol: &'static str,
    precedence: u8,
    associativity: Associativity,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Expr {
    Atom(String),
    Unary {
        op: &'static str,
        operand: Box<Expr>,
    },
    Binary {
        op: BinaryOperator,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    Field {
        target: Box<Expr>,
        field: String,
    },
    Index {
        target: Box<Expr>,
        index: Box<Expr>,
    },
    List(Vec<Expr>),
    Map(Vec<(Expr, Expr)>),
    Group(Box<Expr>),
}

impl Expr {
    fn precedence(&self) -> u8 {
        match self {
            Self::Binary { op, .. } => op.precedence,
            Self::Unary { .. } => 6,
            Self::Call { .. } | Self::Field { .. } | Self::Index { .. } => 7,
            Self::Atom(_) | Self::List(_) | Self::Map(_) | Self::Group(_) => {
                100
            }
        }
    }

    fn render(&self) -> String {
        self.render_with_context(None, false)
    }

    fn render_with_context(
        &self,
        parent: Option<BinaryOperator>,
        is_rhs_of_parent: bool,
    ) -> String {
        let raw = match self {
            Self::Atom(value) => value.clone(),
            Self::Unary { op, operand } => {
                let inner = if operand.precedence() < self.precedence() {
                    format!("({})", operand.render_with_context(None, false))
                } else {
                    operand.render_with_context(None, false)
                };
                format!("{op}{inner}")
            }
            Self::Binary { op, lhs, rhs } => {
                let left = lhs.render_with_context(Some(*op), false);
                let right = rhs.render_with_context(Some(*op), true);
                format!("{left} {} {right}", op.symbol)
            }
            Self::Call { callee, args } => {
                let rendered_callee = if callee.precedence() < self.precedence()
                {
                    format!("({})", callee.render_with_context(None, false))
                } else {
                    callee.render_with_context(None, false)
                };
                let rendered_args = args
                    .iter()
                    .map(Self::render)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{rendered_callee}({rendered_args})")
            }
            Self::Field { target, field } => {
                let rendered_target = if target.precedence() < self.precedence()
                {
                    format!("({})", target.render_with_context(None, false))
                } else {
                    target.render_with_context(None, false)
                };
                format!("{rendered_target}.{field}")
            }
            Self::Index { target, index } => {
                let rendered_target = if target.precedence() < self.precedence()
                {
                    format!("({})", target.render_with_context(None, false))
                } else {
                    target.render_with_context(None, false)
                };
                format!(
                    "{rendered_target}[{}]",
                    index.render_with_context(None, false)
                )
            }
            Self::List(items) => {
                let rendered = items
                    .iter()
                    .map(Self::render)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("[{rendered}]")
            }
            Self::Map(entries) => {
                let rendered = entries
                    .iter()
                    .map(|(key, value)| {
                        format!("{}: {}", key.render(), value.render())
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{rendered}}}")
            }
            Self::Group(inner) => format!("({})", inner.render()),
        };

        let Some(parent_op) = parent else {
            return raw;
        };

        let Self::Binary { op: current_op, .. } = self else {
            return raw;
        };

        let needs_parentheses = current_op.precedence < parent_op.precedence
            || (is_rhs_of_parent
                && current_op.precedence == parent_op.precedence
                && matches!(parent_op.associativity, Associativity::Left));

        if needs_parentheses {
            format!("({raw})")
        } else {
            raw
        }
    }
}

pub fn format_document(text: &str) -> Result<String, FormatterError> {
    let parsed = cellang::parser::parse(text)
        .map_err(|err| FormatterError::parse_failure(err.message))?;
    let root = cellang::parser::CelNode::new_root(parsed);
    let expr = parse_root(&root)?;
    Ok(expr.render())
}

fn parse_root(root: &cellang::parser::CelNode) -> Result<Expr, FormatterError> {
    let mut expressions = root
        .children()
        .filter(|node| node.kind() == SyntaxKind::Expr);
    let Some(expr_node) = expressions.next() else {
        return Err(FormatterError::invalid_syntax_tree(
            "missing top-level expression",
        ));
    };
    if expressions.next().is_some() {
        return Err(FormatterError::invalid_syntax_tree(
            "multiple top-level expressions",
        ));
    }
    parse_node(&expr_node)
}

fn parse_node(node: &cellang::parser::CelNode) -> Result<Expr, FormatterError> {
    match node.kind() {
        SyntaxKind::Expr => parse_expr_node(node),
        SyntaxKind::BinaryOp => parse_binary(node),
        SyntaxKind::UnaryOp => parse_unary(node),
        SyntaxKind::Call => parse_call(node),
        SyntaxKind::FieldAccess => parse_field_access(node),
        SyntaxKind::Index => parse_index(node),
        SyntaxKind::List => parse_list(node),
        SyntaxKind::Map => parse_map(node),
        SyntaxKind::Ternary => {
            Err(FormatterError::unsupported_construct("ternary expressions"))
        }
        SyntaxKind::Error => {
            Err(FormatterError::unsupported_construct("error nodes"))
        }
        other => Err(FormatterError::unsupported_construct(format!(
            "node kind {other:?}"
        ))),
    }
}

fn parse_expr_node(
    node: &cellang::parser::CelNode,
) -> Result<Expr, FormatterError> {
    let elements: Vec<_> = node.children_with_tokens().collect();
    if elements.is_empty() {
        return Err(FormatterError::invalid_syntax_tree(
            "empty expression node",
        ));
    }

    if let Some(token) = elements.first().and_then(NodeOrToken::as_token)
        && token.kind() == SyntaxKind::Dyn
    {
        return Err(FormatterError::unsupported_construct("dyn expressions"));
    }

    if let (Some(first), Some(last)) = (
        elements.first().and_then(NodeOrToken::as_token),
        elements.last().and_then(NodeOrToken::as_token),
    ) && first.kind() == SyntaxKind::LeftParen
        && last.kind() == SyntaxKind::RightParen
        && elements.len() >= 2
    {
        let inner = parse_sequence(&elements[1..elements.len() - 1])?;
        return Ok(Expr::Group(Box::new(inner)));
    }

    parse_sequence(&elements)
}

fn parse_binary(
    node: &cellang::parser::CelNode,
) -> Result<Expr, FormatterError> {
    let elements: Vec<_> = node.children_with_tokens().collect();

    let mut op_index = None;
    let mut op = None;
    for (idx, element) in elements.iter().enumerate() {
        let Some(token) = element.as_token() else {
            continue;
        };
        if let Some(binary_op) = binary_operator(token.kind()) {
            op_index = Some(idx);
            op = Some(binary_op);
            break;
        }
    }

    let Some(operator_index) = op_index else {
        return Err(FormatterError::invalid_syntax_tree(
            "binary operation without operator token",
        ));
    };
    let operator = op.expect("operator is always present when index exists");

    let lhs = parse_sequence(&elements[..operator_index])?;
    let rhs = parse_sequence(&elements[operator_index + 1..])?;
    Ok(Expr::Binary {
        op: operator,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    })
}

fn parse_unary(
    node: &cellang::parser::CelNode,
) -> Result<Expr, FormatterError> {
    let elements: Vec<_> = node.children_with_tokens().collect();
    let Some(operator_token) = elements.first().and_then(NodeOrToken::as_token)
    else {
        return Err(FormatterError::invalid_syntax_tree(
            "unary operation missing operator",
        ));
    };

    let op = match operator_token.kind() {
        SyntaxKind::Minus => "-",
        SyntaxKind::Not => "!",
        kind => {
            return Err(FormatterError::unsupported_construct(format!(
                "unary operator {kind:?}"
            )));
        }
    };

    let operand = parse_sequence(&elements[1..])?;
    Ok(Expr::Unary {
        op,
        operand: Box::new(operand),
    })
}

fn parse_call(node: &cellang::parser::CelNode) -> Result<Expr, FormatterError> {
    let elements: Vec<_> = node.children_with_tokens().collect();
    let left_paren = elements
        .iter()
        .position(|element| {
            element
                .as_token()
                .is_some_and(|t| t.kind() == SyntaxKind::LeftParen)
        })
        .ok_or_else(|| {
            FormatterError::invalid_syntax_tree("call missing left parenthesis")
        })?;

    let right_paren = elements
        .iter()
        .rposition(|element| {
            element
                .as_token()
                .is_some_and(|t| t.kind() == SyntaxKind::RightParen)
        })
        .ok_or_else(|| {
            FormatterError::invalid_syntax_tree(
                "call missing right parenthesis",
            )
        })?;

    if right_paren < left_paren {
        return Err(FormatterError::invalid_syntax_tree(
            "call parenthesis ordering is invalid",
        ));
    }

    let callee = parse_sequence(&elements[..left_paren])?;
    let args = split_on_token(
        &elements[left_paren + 1..right_paren],
        SyntaxKind::Comma,
    )
    .into_iter()
    .map(parse_sequence)
    .collect::<Result<Vec<_>, _>>()?;

    Ok(Expr::Call {
        callee: Box::new(callee),
        args,
    })
}

fn parse_field_access(
    node: &cellang::parser::CelNode,
) -> Result<Expr, FormatterError> {
    let elements: Vec<_> = node.children_with_tokens().collect();
    let dot_index = elements
        .iter()
        .position(|element| {
            element
                .as_token()
                .is_some_and(|t| t.kind() == SyntaxKind::Dot)
        })
        .ok_or_else(|| {
            FormatterError::invalid_syntax_tree("field access missing dot")
        })?;

    let target = parse_sequence(&elements[..dot_index])?;
    let field = elements[dot_index + 1..]
        .iter()
        .find_map(NodeOrToken::as_token)
        .ok_or_else(|| {
            FormatterError::invalid_syntax_tree(
                "field access missing field token",
            )
        })?;

    if field.kind() != SyntaxKind::Ident {
        return Err(FormatterError::unsupported_construct(format!(
            "field token {:?}",
            field.kind()
        )));
    }

    Ok(Expr::Field {
        target: Box::new(target),
        field: field.text().to_string(),
    })
}

fn parse_index(
    node: &cellang::parser::CelNode,
) -> Result<Expr, FormatterError> {
    let elements: Vec<_> = node.children_with_tokens().collect();
    let left_bracket = elements
        .iter()
        .position(|element| {
            element
                .as_token()
                .is_some_and(|t| t.kind() == SyntaxKind::LeftBracket)
        })
        .ok_or_else(|| {
            FormatterError::invalid_syntax_tree("index missing left bracket")
        })?;
    let right_bracket = elements
        .iter()
        .rposition(|element| {
            element
                .as_token()
                .is_some_and(|t| t.kind() == SyntaxKind::RightBracket)
        })
        .ok_or_else(|| {
            FormatterError::invalid_syntax_tree("index missing right bracket")
        })?;

    if right_bracket < left_bracket {
        return Err(FormatterError::invalid_syntax_tree(
            "index bracket ordering is invalid",
        ));
    }

    let target = parse_sequence(&elements[..left_bracket])?;
    let index = parse_sequence(&elements[left_bracket + 1..right_bracket])?;
    Ok(Expr::Index {
        target: Box::new(target),
        index: Box::new(index),
    })
}

fn parse_list(node: &cellang::parser::CelNode) -> Result<Expr, FormatterError> {
    let elements: Vec<_> = node.children_with_tokens().collect();
    let left_bracket = elements
        .iter()
        .position(|element| {
            element
                .as_token()
                .is_some_and(|t| t.kind() == SyntaxKind::LeftBracket)
        })
        .ok_or_else(|| {
            FormatterError::invalid_syntax_tree("list missing left bracket")
        })?;
    let right_bracket = elements
        .iter()
        .rposition(|element| {
            element
                .as_token()
                .is_some_and(|t| t.kind() == SyntaxKind::RightBracket)
        })
        .ok_or_else(|| {
            FormatterError::invalid_syntax_tree("list missing right bracket")
        })?;

    if right_bracket < left_bracket {
        return Err(FormatterError::invalid_syntax_tree(
            "list bracket ordering is invalid",
        ));
    }

    let items = split_on_token(
        &elements[left_bracket + 1..right_bracket],
        SyntaxKind::Comma,
    )
    .into_iter()
    .map(parse_sequence)
    .collect::<Result<Vec<_>, _>>()?;
    Ok(Expr::List(items))
}

fn parse_map(node: &cellang::parser::CelNode) -> Result<Expr, FormatterError> {
    let elements: Vec<_> = node.children_with_tokens().collect();
    let left_brace = elements
        .iter()
        .position(|element| {
            element
                .as_token()
                .is_some_and(|t| t.kind() == SyntaxKind::LeftBrace)
        })
        .ok_or_else(|| {
            FormatterError::invalid_syntax_tree("map missing left brace")
        })?;
    let right_brace = elements
        .iter()
        .rposition(|element| {
            element
                .as_token()
                .is_some_and(|t| t.kind() == SyntaxKind::RightBrace)
        })
        .ok_or_else(|| {
            FormatterError::invalid_syntax_tree("map missing right brace")
        })?;

    if right_brace < left_brace {
        return Err(FormatterError::invalid_syntax_tree(
            "map brace ordering is invalid",
        ));
    }

    let mut entries = Vec::new();
    for entry in split_on_token(
        &elements[left_brace + 1..right_brace],
        SyntaxKind::Comma,
    ) {
        let colon = entry
            .iter()
            .position(|element| {
                element
                    .as_token()
                    .is_some_and(|t| t.kind() == SyntaxKind::Colon)
            })
            .ok_or_else(|| {
                FormatterError::invalid_syntax_tree("map entry missing colon")
            })?;
        let key = parse_sequence(&entry[..colon])?;
        let value = parse_sequence(&entry[colon + 1..])?;
        entries.push((key, value));
    }

    Ok(Expr::Map(entries))
}

fn parse_sequence<L>(
    elements: &[NodeOrToken<cellang::parser::CelNode, SyntaxToken<L>>],
) -> Result<Expr, FormatterError>
where
    L: rowan::Language<Kind = SyntaxKind>,
{
    if elements.is_empty() {
        return Err(FormatterError::invalid_syntax_tree(
            "missing expression sequence",
        ));
    }

    if elements.len() == 1 {
        return parse_element(&elements[0]);
    }

    if let Some(node) = elements.first().and_then(NodeOrToken::as_node)
        && elements.len() == 1
    {
        return parse_node(node);
    }

    Err(FormatterError::unsupported_construct(
        "mixed token sequences",
    ))
}

fn parse_element<L>(
    element: &NodeOrToken<cellang::parser::CelNode, SyntaxToken<L>>,
) -> Result<Expr, FormatterError>
where
    L: rowan::Language<Kind = SyntaxKind>,
{
    if let Some(node) = element.as_node() {
        return parse_node(node);
    }
    let token = element
        .as_token()
        .ok_or_else(|| FormatterError::invalid_syntax_tree("missing token"))?;
    parse_atom(token)
}

fn parse_atom<L>(token: &SyntaxToken<L>) -> Result<Expr, FormatterError>
where
    L: rowan::Language<Kind = SyntaxKind>,
{
    let rendered = match token.kind() {
        SyntaxKind::Ident
        | SyntaxKind::Int
        | SyntaxKind::Uint
        | SyntaxKind::Double
        | SyntaxKind::True
        | SyntaxKind::False
        | SyntaxKind::Null => token.text().to_string(),
        SyntaxKind::String | SyntaxKind::RawString => {
            format!("\"{}\"", escape_string(token.text()))
        }
        SyntaxKind::Bytes | SyntaxKind::RawBytes => {
            format!("b\"{}\"", escape_string(token.text()))
        }
        SyntaxKind::Dyn => {
            return Err(FormatterError::unsupported_construct("dyn keyword"));
        }
        kind => {
            return Err(FormatterError::unsupported_construct(format!(
                "token kind {kind:?}"
            )));
        }
    };
    Ok(Expr::Atom(rendered))
}

fn split_on_token<L>(
    elements: &[NodeOrToken<cellang::parser::CelNode, SyntaxToken<L>>],
    split_kind: SyntaxKind,
) -> Vec<&[NodeOrToken<cellang::parser::CelNode, SyntaxToken<L>>]>
where
    L: rowan::Language<Kind = SyntaxKind>,
{
    if elements.is_empty() {
        return Vec::new();
    }

    let mut start = 0;
    let mut groups = Vec::new();
    for (idx, element) in elements.iter().enumerate() {
        if element
            .as_token()
            .is_some_and(|token| token.kind() == split_kind)
        {
            if start < idx {
                groups.push(&elements[start..idx]);
            }
            start = idx + 1;
        }
    }

    if start < elements.len() {
        groups.push(&elements[start..]);
    }
    groups
}

fn binary_operator(kind: SyntaxKind) -> Option<BinaryOperator> {
    let operator = match kind {
        SyntaxKind::Or => BinaryOperator {
            symbol: "||",
            precedence: 1,
            associativity: Associativity::Left,
        },
        SyntaxKind::And => BinaryOperator {
            symbol: "&&",
            precedence: 2,
            associativity: Associativity::Left,
        },
        SyntaxKind::EqualEqual => BinaryOperator {
            symbol: "==",
            precedence: 3,
            associativity: Associativity::Left,
        },
        SyntaxKind::NotEqual => BinaryOperator {
            symbol: "!=",
            precedence: 3,
            associativity: Associativity::Left,
        },
        SyntaxKind::Less => BinaryOperator {
            symbol: "<",
            precedence: 3,
            associativity: Associativity::Left,
        },
        SyntaxKind::LessEqual => BinaryOperator {
            symbol: "<=",
            precedence: 3,
            associativity: Associativity::Left,
        },
        SyntaxKind::Greater => BinaryOperator {
            symbol: ">",
            precedence: 3,
            associativity: Associativity::Left,
        },
        SyntaxKind::GreaterEqual => BinaryOperator {
            symbol: ">=",
            precedence: 3,
            associativity: Associativity::Left,
        },
        SyntaxKind::In => BinaryOperator {
            symbol: "in",
            precedence: 3,
            associativity: Associativity::Left,
        },
        SyntaxKind::Plus => BinaryOperator {
            symbol: "+",
            precedence: 4,
            associativity: Associativity::Left,
        },
        SyntaxKind::Minus => BinaryOperator {
            symbol: "-",
            precedence: 4,
            associativity: Associativity::Left,
        },
        SyntaxKind::Star => BinaryOperator {
            symbol: "*",
            precedence: 5,
            associativity: Associativity::Left,
        },
        SyntaxKind::Slash => BinaryOperator {
            symbol: "/",
            precedence: 5,
            associativity: Associativity::Left,
        },
        SyntaxKind::Percent => BinaryOperator {
            symbol: "%",
            precedence: 5,
            associativity: Associativity::Left,
        },
        _ => return None,
    };
    Some(operator)
}

fn escape_string(source: &str) -> String {
    source
        .chars()
        .flat_map(|ch| match ch {
            '\\' => "\\\\".chars().collect::<Vec<_>>(),
            '"' => "\\\"".chars().collect::<Vec<_>>(),
            '\n' => "\\n".chars().collect::<Vec<_>>(),
            '\r' => "\\r".chars().collect::<Vec<_>>(),
            '\t' => "\\t".chars().collect::<Vec<_>>(),
            _ => vec![ch],
        })
        .collect()
}

#[cfg(test)]
mod formatting {
    use super::*;

    #[test]
    fn canonical_output_matches_fixtures() {
        let fixtures = [
            ("1+2*3", "1 + 2 * 3"),
            ("foo(1,2)", "foo(1, 2)"),
            ("a.b(c)", "a.b(c)"),
            ("[1,2,3]", "[1, 2, 3]"),
            ("{foo:1,bar:[1,2]}", "{foo: 1, bar: [1, 2]}"),
            (
                "foo.bar([1,2],{x:1,y:2})+4",
                "foo.bar([1, 2], {x: 1, y: 2}) + 4",
            ),
            ("'ok'", "\"ok\""),
        ];

        for (input, expected) in fixtures {
            let actual =
                format_document(input).expect("formatting should succeed");
            assert_eq!(actual, expected, "fixture should match for '{input}'");
        }
    }

    #[test]
    fn formatting_is_deterministic_for_same_input() {
        let input = "foo(1,2)+bar.baz([1,2],{a:1,b:2})";
        let first =
            format_document(input).expect("first formatting should succeed");
        let second =
            format_document(input).expect("second formatting should succeed");
        assert_eq!(first, second);
    }

    #[test]
    fn unsupported_construct_has_explicit_kind_and_message() {
        let err = format_document("a ? b : c")
            .expect_err("ternary should be unsupported");
        assert_eq!(err.kind(), &FormatterErrorKind::UnsupportedConstruct);
        assert_eq!(
            err.message(),
            "Formatting unsupported construct: ternary expressions"
        );
        assert_eq!(
            err.to_response_data(),
            json!({
                "kind": "unsupported_construct",
                "message": "Formatting unsupported construct: ternary expressions"
            })
        );
    }
}
