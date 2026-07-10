use crate::lexer::{Lexer, Token, TokenType};
use crate::syntax::bridge::token_type_to_syntax_kind;
use crate::syntax::{Error, ParseResult, SyntaxKind};
use rowan::{Checkpoint, GreenNodeBuilder};

const PREFIX_BP: u8 = 13;
const POSTFIX_BP: u8 = 15;
const TERNARY_L_BP: u8 = 2;
const TERNARY_R_BP: u8 = 1;

pub fn parse(input: &str) -> Result<ParseResult, Error> {
    let lexer = Lexer::new(input);
    let mut tokens = Vec::new();

    for next in lexer {
        match next {
            Ok(token) => tokens.push(token),
            Err(err) => return Err(Error::new(err.message().to_string())),
        }
    }

    let mut parser = RowanParser {
        tokens,
        pos: 0,
        errors: Vec::new(),
        builder: GreenNodeBuilder::new(),
    };

    parser.builder.start_node(SyntaxKind::Root.into());
    parser.builder.start_node(SyntaxKind::Expr.into());
    parser.parse_expr(0);
    parser.builder.finish_node();

    while !parser.is_eof() {
        parser.record_error("Unexpected token");
        parser.builder.start_node(SyntaxKind::Error.into());
        parser.bump();
        parser.builder.finish_node();
    }

    parser.builder.finish_node();
    let green = parser.builder.finish();

    if parser.errors.is_empty() {
        Ok(green)
    } else {
        Err(Error::new(parser.errors.join(" | ")))
    }
}

struct RowanParser<'src> {
    tokens: Vec<Token<'src>>,
    pos: usize,
    errors: Vec<String>,
    builder: GreenNodeBuilder<'static>,
}

impl<'src> RowanParser<'src> {
    fn parse_expr(&mut self, min_bp: u8) -> Checkpoint {
        let mut lhs = self.builder.checkpoint();

        if self.is_eof() {
            self.record_error("Unexpected end of file, expected expression");
            self.builder.start_node(SyntaxKind::Error.into());
            self.builder.finish_node();
            return lhs;
        }

        lhs = match self.current().map(|token| token.ty) {
            Some(TokenType::Ident)
            | Some(TokenType::Int(_))
            | Some(TokenType::Uint(_))
            | Some(TokenType::Double(_))
            | Some(TokenType::String)
            | Some(TokenType::RawString)
            | Some(TokenType::Bytes)
            | Some(TokenType::RawBytes)
            | Some(TokenType::True)
            | Some(TokenType::False)
            | Some(TokenType::Null) => {
                self.bump();
                lhs
            }
            Some(TokenType::Dyn) => self.parse_dyn(lhs),
            Some(TokenType::LeftParen) => self.parse_group(lhs),
            Some(TokenType::Minus) | Some(TokenType::Not) => {
                self.parse_unary(lhs)
            }
            Some(TokenType::LeftBracket) => self.parse_list(lhs),
            Some(TokenType::LeftBrace) => self.parse_map(lhs),
            Some(_) => {
                self.record_error("Unexpected token");
                self.builder.start_node_at(lhs, SyntaxKind::Error.into());
                self.bump();
                self.builder.finish_node();
                lhs
            }
            None => lhs,
        };

        loop {
            if self.is_eof() || self.is_terminator() {
                break;
            }

            let Some(ty) = self.current().map(|token| token.ty) else {
                break;
            };

            match ty {
                TokenType::LeftParen => {
                    if POSTFIX_BP < min_bp {
                        break;
                    }
                    lhs = self.parse_call(lhs);
                }
                TokenType::LeftBracket => {
                    if POSTFIX_BP < min_bp {
                        break;
                    }
                    lhs = self.parse_index(lhs);
                }
                TokenType::Dot => {
                    if POSTFIX_BP < min_bp {
                        break;
                    }
                    lhs = self.parse_field_access(lhs);
                }
                TokenType::QuestionMark => {
                    if TERNARY_L_BP < min_bp {
                        break;
                    }
                    lhs = self.parse_ternary(lhs);
                }
                _ => {
                    let Some((l_bp, r_bp)) = infix_binding_power(ty) else {
                        break;
                    };

                    if l_bp < min_bp {
                        break;
                    }

                    self.builder
                        .start_node_at(lhs, SyntaxKind::BinaryOp.into());
                    self.bump();
                    self.parse_expr(r_bp);
                    self.builder.finish_node();
                }
            }
        }

        lhs
    }

    fn parse_unary(&mut self, checkpoint: Checkpoint) -> Checkpoint {
        self.builder
            .start_node_at(checkpoint, SyntaxKind::UnaryOp.into());
        self.bump();
        self.parse_expr(PREFIX_BP);
        self.builder.finish_node();
        checkpoint
    }

    fn parse_group(&mut self, checkpoint: Checkpoint) -> Checkpoint {
        self.builder
            .start_node_at(checkpoint, SyntaxKind::Expr.into());
        self.bump();
        self.parse_expr(0);
        self.expect_token(
            |ty| matches!(ty, TokenType::RightParen),
            "Expected closing parenthesis",
        );
        self.builder.finish_node();
        checkpoint
    }

    fn parse_dyn(&mut self, checkpoint: Checkpoint) -> Checkpoint {
        self.builder
            .start_node_at(checkpoint, SyntaxKind::Expr.into());
        self.bump();
        self.expect_token(
            |ty| matches!(ty, TokenType::LeftParen),
            "Expected opening parenthesis after dyn",
        );
        self.parse_expr(0);
        self.expect_token(
            |ty| matches!(ty, TokenType::RightParen),
            "Expected closing parenthesis after dyn",
        );
        self.builder.finish_node();
        checkpoint
    }

    fn parse_list(&mut self, checkpoint: Checkpoint) -> Checkpoint {
        self.builder
            .start_node_at(checkpoint, SyntaxKind::List.into());
        self.bump();

        if self.at(|ty| matches!(ty, TokenType::RightBracket)) {
            self.bump();
            self.builder.finish_node();
            return checkpoint;
        }

        loop {
            self.parse_expr(0);

            if self.at(|ty| matches!(ty, TokenType::Comma)) {
                self.bump();
                continue;
            }

            if self.at(|ty| matches!(ty, TokenType::RightBracket)) {
                self.bump();
                break;
            }

            self.expect_token(
                |ty| matches!(ty, TokenType::RightBracket),
                "continuing list",
            );
            break;
        }

        self.builder.finish_node();
        checkpoint
    }

    fn parse_map(&mut self, checkpoint: Checkpoint) -> Checkpoint {
        self.builder
            .start_node_at(checkpoint, SyntaxKind::Map.into());
        self.bump();

        if self.at(|ty| matches!(ty, TokenType::RightBrace)) {
            self.bump();
            self.builder.finish_node();
            return checkpoint;
        }

        loop {
            self.parse_expr(0);
            self.expect_token(
                |ty| matches!(ty, TokenType::Colon),
                "Expected colon between map key and value",
            );
            self.parse_expr(0);

            if self.at(|ty| matches!(ty, TokenType::Comma)) {
                self.bump();
                continue;
            }

            if self.at(|ty| matches!(ty, TokenType::RightBrace)) {
                self.bump();
                break;
            }

            self.expect_token(
                |ty| matches!(ty, TokenType::RightBrace),
                "continuing map",
            );
            break;
        }

        self.builder.finish_node();
        checkpoint
    }

    fn parse_call(&mut self, checkpoint: Checkpoint) -> Checkpoint {
        self.builder
            .start_node_at(checkpoint, SyntaxKind::Call.into());
        self.bump();

        if self.at(|ty| matches!(ty, TokenType::RightParen)) {
            self.bump();
            self.builder.finish_node();
            return checkpoint;
        }

        loop {
            self.parse_expr(0);

            if self.at(|ty| matches!(ty, TokenType::Comma)) {
                self.bump();
                continue;
            }

            if self.at(|ty| matches!(ty, TokenType::RightParen)) {
                self.bump();
                break;
            }

            self.expect_token(
                |ty| matches!(ty, TokenType::RightParen),
                "continuing argument list",
            );
            break;
        }

        self.builder.finish_node();
        checkpoint
    }

    fn parse_index(&mut self, checkpoint: Checkpoint) -> Checkpoint {
        self.builder
            .start_node_at(checkpoint, SyntaxKind::Index.into());
        self.bump();
        self.parse_expr(0);
        self.expect_token(
            |ty| matches!(ty, TokenType::RightBracket),
            "Expected closing bracket",
        );
        self.builder.finish_node();
        checkpoint
    }

    fn parse_field_access(&mut self, checkpoint: Checkpoint) -> Checkpoint {
        self.builder
            .start_node_at(checkpoint, SyntaxKind::FieldAccess.into());
        self.bump();

        if self.at(|ty| matches!(ty, TokenType::Ident)) {
            self.bump();
        } else if self.is_eof() {
            self.record_error("Unexpected end of file, expected field name");
            self.builder.start_node(SyntaxKind::Error.into());
            self.builder.finish_node();
        } else {
            self.record_error("Unexpected token");
            self.builder.start_node(SyntaxKind::Error.into());
            self.bump();
            self.builder.finish_node();
        }

        self.builder.finish_node();
        checkpoint
    }

    fn parse_ternary(&mut self, checkpoint: Checkpoint) -> Checkpoint {
        self.builder
            .start_node_at(checkpoint, SyntaxKind::Ternary.into());
        self.bump();
        self.parse_expr(0);
        self.expect_token(
            |ty| matches!(ty, TokenType::Colon),
            "Expected colon after the condition",
        );
        self.parse_expr(TERNARY_R_BP);
        self.builder.finish_node();
        checkpoint
    }

    fn expect_token(
        &mut self,
        mut check: impl FnMut(TokenType) -> bool,
        message: &str,
    ) {
        match self.current().map(|token| token.ty) {
            Some(ty) if check(ty) => {
                self.bump();
            }
            Some(_) => {
                self.record_error(message);
                self.builder.start_node(SyntaxKind::Error.into());
                self.bump();
                self.builder.finish_node();
            }
            None => {
                self.record_error(format!(
                    "Unexpected end of file, expected {message}"
                ));
                self.builder.start_node(SyntaxKind::Error.into());
                self.builder.finish_node();
            }
        }
    }

    fn record_error(&mut self, message: impl Into<String>) {
        self.errors.push(message.into());
    }

    fn at(&self, mut check: impl FnMut(TokenType) -> bool) -> bool {
        self.current().is_some_and(|token| check(token.ty))
    }

    fn is_terminator(&self) -> bool {
        self.at(|ty| {
            matches!(
                ty,
                TokenType::RightParen
                    | TokenType::RightBracket
                    | TokenType::RightBrace
                    | TokenType::Comma
                    | TokenType::Colon
                    | TokenType::Semicolon
            )
        })
    }

    fn current(&self) -> Option<&Token<'src>> {
        self.tokens.get(self.pos)
    }

    fn bump(&mut self) {
        if let Some(token) = self.tokens.get(self.pos) {
            let kind = token_type_to_syntax_kind(token.ty);
            self.builder.token(kind.into(), token.origin);
            self.pos += 1;
        }
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.tokens.len()
    }
}

fn infix_binding_power(token: TokenType) -> Option<(u8, u8)> {
    let pair = match token {
        TokenType::Or => (3, 4),
        TokenType::And => (5, 6),
        TokenType::In
        | TokenType::NotEqual
        | TokenType::EqualEqual
        | TokenType::Less
        | TokenType::LessEqual
        | TokenType::Greater
        | TokenType::GreaterEqual => (7, 8),
        TokenType::Plus | TokenType::Minus => (9, 10),
        TokenType::Star | TokenType::Slash | TokenType::Percent => (11, 12),
        _ => return None,
    };
    Some(pair)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::CelLanguage;
    use rowan::{NodeOrToken, SyntaxNode};

    fn parse_ok(input: &str) -> ParseResult {
        parse(input)
            .unwrap_or_else(|err| panic!("expected parse success: {err}"))
    }

    fn parse_err(input: &str) -> String {
        parse(input).expect_err("expected parse failure").message
    }

    fn root(node: ParseResult) -> SyntaxNode<CelLanguage> {
        SyntaxNode::new_root(node)
    }

    fn first_operator(node: &SyntaxNode<CelLanguage>) -> Option<SyntaxKind> {
        node.children_with_tokens().find_map(|child| match child {
            NodeOrToken::Token(tok)
                if matches!(
                    tok.kind(),
                    SyntaxKind::Plus
                        | SyntaxKind::Minus
                        | SyntaxKind::Star
                        | SyntaxKind::Slash
                        | SyntaxKind::Percent
                        | SyntaxKind::Less
                        | SyntaxKind::LessEqual
                        | SyntaxKind::Greater
                        | SyntaxKind::GreaterEqual
                        | SyntaxKind::EqualEqual
                        | SyntaxKind::NotEqual
                        | SyntaxKind::In
                        | SyntaxKind::And
                        | SyntaxKind::Or
                ) =>
            {
                Some(tok.kind())
            }
            NodeOrToken::Node(_) | NodeOrToken::Token(_) => None,
        })
    }

    #[test]
    fn parses_basic_atoms() {
        let cases = [
            ("123", SyntaxKind::Int),
            ("\"x\"", SyntaxKind::String),
            ("ident", SyntaxKind::Ident),
            ("true", SyntaxKind::True),
            ("null", SyntaxKind::Null),
        ];

        for (input, expected_token) in cases {
            let root = root(parse_ok(input));
            let has_token = root.descendants_with_tokens().any(|item| {
                item.into_token()
                    .is_some_and(|token| token.kind() == expected_token)
            });
            assert!(
                has_token,
                "expected token kind {expected_token:?} for {input}"
            );
        }
    }

    #[test]
    fn respects_operator_precedence() {
        let root = root(parse_ok("1 + 2 * 3"));
        let binaries: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::BinaryOp)
            .collect();
        assert_eq!(binaries.len(), 2);
        assert_eq!(first_operator(&binaries[0]), Some(SyntaxKind::Plus));
        assert_eq!(first_operator(&binaries[1]), Some(SyntaxKind::Star));
    }

    #[test]
    fn keeps_left_associativity_for_arithmetic() {
        let root = root(parse_ok("a - b - c"));
        let binaries: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::BinaryOp)
            .collect();
        assert_eq!(binaries.len(), 2);
        assert_eq!(first_operator(&binaries[0]), Some(SyntaxKind::Minus));
        assert_eq!(first_operator(&binaries[1]), Some(SyntaxKind::Minus));

        let nested_count = binaries[0]
            .children()
            .filter(|child| child.kind() == SyntaxKind::BinaryOp)
            .count();
        assert_eq!(nested_count, 1, "outer binary should contain lhs binary");
    }

    #[test]
    fn keeps_right_associativity_for_ternary() {
        let root = root(parse_ok("a ? b : c ? d : e"));
        let ternaries: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Ternary)
            .collect();
        assert_eq!(ternaries.len(), 2);
        let nested = ternaries[0]
            .children()
            .filter(|child| child.kind() == SyntaxKind::Ternary)
            .count();
        assert_eq!(nested, 1, "outer ternary should nest in else arm");
    }

    #[test]
    fn parses_calls_fields_and_indexing() {
        let root = root(parse_ok("foo.bar(baz)[0]"));
        let node_kinds: Vec<_> =
            root.descendants().map(|node| node.kind()).collect();
        assert!(node_kinds.contains(&SyntaxKind::FieldAccess));
        assert!(node_kinds.contains(&SyntaxKind::Call));
        assert!(node_kinds.contains(&SyntaxKind::Index));
    }

    #[test]
    fn parses_lists_maps_grouping_and_dyn() {
        let list = root(parse_ok("[1, 2, 3]"));
        assert!(
            list.descendants()
                .any(|node| node.kind() == SyntaxKind::List)
        );

        let map = root(parse_ok("{k: 1, m: 2}"));
        assert!(map.descendants().any(|node| node.kind() == SyntaxKind::Map));

        let group = root(parse_ok("(1 + 2)"));
        assert!(
            group
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Expr)
        );

        let dyn_expr = root(parse_ok("dyn(2u)"));
        let dyn_tokens = dyn_expr
            .descendants_with_tokens()
            .filter_map(|item| item.into_token())
            .filter(|token| token.kind() == SyntaxKind::Dyn)
            .count();
        assert_eq!(dyn_tokens, 1);
    }

    #[test]
    fn reports_deterministic_errors_without_panicking() {
        let first = parse_err("foo(");
        let second = parse_err("foo(");
        assert_eq!(first, second);
        assert!(first.contains("continuing argument list"));

        let unexpected = parse_err("1 + * 2");
        assert!(unexpected.contains("Unexpected token"));

        let list_eof = parse_err("[1, 2");
        assert!(list_eof.contains("continuing list"));
    }
}
