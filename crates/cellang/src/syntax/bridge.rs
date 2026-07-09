use crate::lexer::TokenType;
#[cfg(test)]
use crate::lexer::Token;
use crate::syntax::SyntaxKind;

/// Converts a lexer token kind into the corresponding Rowan syntax kind.
///
/// Mapping policy:
/// - Every `TokenType` variant is explicitly mapped.
/// - No token variants are intentionally excluded at this stage.
/// - Lexer failures (e.g. unterminated strings) do not produce `Token`, so
///   they are handled in diagnostics paths, not by this bridge.
pub fn token_type_to_syntax_kind(token_type: TokenType) -> SyntaxKind {
    match token_type {
        TokenType::LeftParen => SyntaxKind::LeftParen,
        TokenType::RightParen => SyntaxKind::RightParen,
        TokenType::LeftBracket => SyntaxKind::LeftBracket,
        TokenType::RightBracket => SyntaxKind::RightBracket,
        TokenType::LeftBrace => SyntaxKind::LeftBrace,
        TokenType::RightBrace => SyntaxKind::RightBrace,
        TokenType::Dot => SyntaxKind::Dot,
        TokenType::Comma => SyntaxKind::Comma,
        TokenType::Plus => SyntaxKind::Plus,
        TokenType::Percent => SyntaxKind::Percent,
        TokenType::Minus => SyntaxKind::Minus,
        TokenType::Semicolon => SyntaxKind::Semicolon,
        TokenType::Not => SyntaxKind::Not,
        TokenType::NotEqual => SyntaxKind::NotEqual,
        TokenType::Equal => SyntaxKind::Equal,
        TokenType::EqualEqual => SyntaxKind::EqualEqual,
        TokenType::Greater => SyntaxKind::Greater,
        TokenType::GreaterEqual => SyntaxKind::GreaterEqual,
        TokenType::Less => SyntaxKind::Less,
        TokenType::QuestionMark => SyntaxKind::QuestionMark,
        TokenType::LessEqual => SyntaxKind::LessEqual,
        TokenType::Slash => SyntaxKind::Slash,
        TokenType::Colon => SyntaxKind::Colon,
        TokenType::RawString => SyntaxKind::RawString,
        TokenType::Star => SyntaxKind::Star,
        TokenType::String => SyntaxKind::String,
        TokenType::Bytes => SyntaxKind::Bytes,
        TokenType::RawBytes => SyntaxKind::RawBytes,
        TokenType::Ident => SyntaxKind::Ident,
        TokenType::Int(_) => SyntaxKind::Int,
        TokenType::Uint(_) => SyntaxKind::Uint,
        TokenType::Double(_) => SyntaxKind::Double,
        TokenType::And => SyntaxKind::And,
        TokenType::As => SyntaxKind::As,
        TokenType::Break => SyntaxKind::Break,
        TokenType::Const => SyntaxKind::Const,
        TokenType::Else => SyntaxKind::Else,
        TokenType::For => SyntaxKind::For,
        TokenType::Function => SyntaxKind::Function,
        TokenType::If => SyntaxKind::If,
        TokenType::Import => SyntaxKind::Import,
        TokenType::Let => SyntaxKind::Let,
        TokenType::Loop => SyntaxKind::Loop,
        TokenType::Null => SyntaxKind::Null,
        TokenType::In => SyntaxKind::In,
        TokenType::Or => SyntaxKind::Or,
        TokenType::True => SyntaxKind::True,
        TokenType::False => SyntaxKind::False,
        TokenType::Var => SyntaxKind::Var,
        TokenType::Package => SyntaxKind::Package,
        TokenType::Namespace => SyntaxKind::Namespace,
        TokenType::Void => SyntaxKind::Void,
        TokenType::While => SyntaxKind::While,
        TokenType::Dyn => SyntaxKind::Dyn,
    }
}

impl From<TokenType> for SyntaxKind {
    fn from(value: TokenType) -> Self {
        token_type_to_syntax_kind(value)
    }
}

/// Converts a token into a `(start, len)` byte-span pair.
///
/// This keeps the migration bridge byte-for-byte compatible with the lexer's
/// `offset` and `span_len` fields.
#[cfg(test)]
pub fn token_to_syntax_span(token: &Token<'_>) -> (usize, usize) {
    (token.offset, token.span_len)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Lexer;

    #[test]
    fn maps_every_token_type_variant_exhaustively() {
        let cases = [
            (TokenType::LeftParen, SyntaxKind::LeftParen),
            (TokenType::RightParen, SyntaxKind::RightParen),
            (TokenType::LeftBracket, SyntaxKind::LeftBracket),
            (TokenType::RightBracket, SyntaxKind::RightBracket),
            (TokenType::LeftBrace, SyntaxKind::LeftBrace),
            (TokenType::RightBrace, SyntaxKind::RightBrace),
            (TokenType::Dot, SyntaxKind::Dot),
            (TokenType::Comma, SyntaxKind::Comma),
            (TokenType::Plus, SyntaxKind::Plus),
            (TokenType::Percent, SyntaxKind::Percent),
            (TokenType::Minus, SyntaxKind::Minus),
            (TokenType::Semicolon, SyntaxKind::Semicolon),
            (TokenType::Not, SyntaxKind::Not),
            (TokenType::NotEqual, SyntaxKind::NotEqual),
            (TokenType::Equal, SyntaxKind::Equal),
            (TokenType::EqualEqual, SyntaxKind::EqualEqual),
            (TokenType::Greater, SyntaxKind::Greater),
            (TokenType::GreaterEqual, SyntaxKind::GreaterEqual),
            (TokenType::Less, SyntaxKind::Less),
            (TokenType::QuestionMark, SyntaxKind::QuestionMark),
            (TokenType::LessEqual, SyntaxKind::LessEqual),
            (TokenType::Slash, SyntaxKind::Slash),
            (TokenType::Colon, SyntaxKind::Colon),
            (TokenType::RawString, SyntaxKind::RawString),
            (TokenType::Star, SyntaxKind::Star),
            (TokenType::String, SyntaxKind::String),
            (TokenType::Bytes, SyntaxKind::Bytes),
            (TokenType::RawBytes, SyntaxKind::RawBytes),
            (TokenType::Ident, SyntaxKind::Ident),
            (TokenType::Int(42), SyntaxKind::Int),
            (TokenType::Uint(42), SyntaxKind::Uint),
            (TokenType::Double(4.2), SyntaxKind::Double),
            (TokenType::And, SyntaxKind::And),
            (TokenType::As, SyntaxKind::As),
            (TokenType::Break, SyntaxKind::Break),
            (TokenType::Const, SyntaxKind::Const),
            (TokenType::Else, SyntaxKind::Else),
            (TokenType::For, SyntaxKind::For),
            (TokenType::Function, SyntaxKind::Function),
            (TokenType::If, SyntaxKind::If),
            (TokenType::Import, SyntaxKind::Import),
            (TokenType::Let, SyntaxKind::Let),
            (TokenType::Loop, SyntaxKind::Loop),
            (TokenType::Null, SyntaxKind::Null),
            (TokenType::In, SyntaxKind::In),
            (TokenType::Or, SyntaxKind::Or),
            (TokenType::True, SyntaxKind::True),
            (TokenType::False, SyntaxKind::False),
            (TokenType::Var, SyntaxKind::Var),
            (TokenType::Package, SyntaxKind::Package),
            (TokenType::Namespace, SyntaxKind::Namespace),
            (TokenType::Void, SyntaxKind::Void),
            (TokenType::While, SyntaxKind::While),
            (TokenType::Dyn, SyntaxKind::Dyn),
        ];

        for (token_type, expected) in cases {
            assert_eq!(token_type_to_syntax_kind(token_type), expected);
            assert_eq!(SyntaxKind::from(token_type), expected);
        }
    }

    #[test]
    fn converts_range_with_offset_and_length_parity() {
        let source = "foo + 42u";
        let mut lexer = Lexer::new(source);
        let ident = lexer.next().unwrap().unwrap();
        let plus = lexer.next().unwrap().unwrap();
        let uint = lexer.next().unwrap().unwrap();

        assert_eq!(token_to_syntax_span(&ident), (0, 3));
        assert_eq!(token_to_syntax_span(&plus), (4, 1));
        assert_eq!(token_to_syntax_span(&uint), (6, 3));

        for token in [&ident, &plus, &uint] {
            let (offset, len) = token_to_syntax_span(token);
            let slice = &source[offset..offset + len];
            assert_eq!(
                slice,
                &source[token.offset..token.offset + token.span_len]
            );
            assert_eq!(len, token.origin.len());
        }
    }

    #[test]
    fn handles_edge_cases_for_empty_and_multibyte_ranges() {
        let empty = Token {
            origin: "",
            offset: 0,
            span_len: 0,
            ty: TokenType::Ident,
        };
        assert_eq!(token_to_syntax_span(&empty), (0, 0));

        // Unicode identifiers are invalid in the current lexer, so we validate
        // multi-byte span handling with a manually constructed token.
        let unicode = Token {
            origin: "δ",
            offset: 7,
            span_len: "δ".len(),
            ty: TokenType::String,
        };
        let (offset, len) = token_to_syntax_span(&unicode);
        assert_eq!((offset, len), (7, 2));
        assert_eq!(len, unicode.origin.len());
    }

    #[test]
    fn unclosed_delimiter_is_lexer_error_not_bridge_token() {
        let mut lexer = Lexer::new("\"unterminated");
        let err = lexer.next().expect("expected lex result").expect_err(
            "unterminated delimiter should fail before bridge mapping",
        );
        let span = err.span();
        assert_eq!(span.offset(), 0);
        assert!(!span.is_empty());
    }
}
