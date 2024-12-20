use core::fmt;
use miette::{Diagnostic, Error, LabeledSpan};
use std::{borrow::Cow, collections::HashMap, sync::OnceLock};

#[derive(Diagnostic, Debug)]
pub struct Eof;

impl fmt::Display for Eof {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Unexpected end of file")
    }
}

impl std::error::Error for Eof {}

#[derive(Debug, PartialEq, Clone)]
pub struct Token<'src> {
    pub origin: &'src str,
    pub offset: usize,
    pub line: usize,
    pub kind: TokenKind,
}

impl Token<'_> {
    pub fn unescape(s: &str) -> Cow<'_, str> {
        Cow::Borrowed(s.trim_matches('"'))
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum TokenKind {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Star,
    Dot,
    Comma,
    Plus,
    Minus,
    Semicolon,
    Not,
    NotEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    Slash,
    String,
    Ident,
    Number(f64),
    And,
    As,
    Break,
    Const,
    Class,
    Else,
    False,
    For,
    Function,
    If,
    Import,
    Let,
    Loop,
    Null,
    In,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    Package,
    Namespace,
    Void,
    While,
    Eof,
}

fn keywords() -> &'static HashMap<&'static str, TokenKind> {
    static KEYWORDS: OnceLock<HashMap<&'static str, TokenKind>> = OnceLock::new();
    KEYWORDS.get_or_init(|| {
        let mut map = HashMap::new();
        map.insert("true", TokenKind::True);
        map.insert("false", TokenKind::False);
        map.insert("null", TokenKind::Null);
        map.insert("in", TokenKind::In);
        map.insert("as", TokenKind::As);
        map.insert("break", TokenKind::Break);
        map.insert("const", TokenKind::As);
        map.insert("continue", TokenKind::Const);
        map.insert("else", TokenKind::Else);
        map.insert("for", TokenKind::For);
        map.insert("function", TokenKind::Function);
        map.insert("if", TokenKind::If);
        map.insert("import", TokenKind::Import);
        map.insert("let", TokenKind::Let);
        map.insert("loop", TokenKind::Loop);
        map.insert("package", TokenKind::Package);
        map.insert("namespace", TokenKind::Namespace);
        map.insert("return", TokenKind::Return);
        map.insert("var", TokenKind::Var);
        map.insert("void", TokenKind::Void);
        map.insert("while", TokenKind::While);

        map
    })
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let origin = self.origin;
        match self.kind {
            TokenKind::In => write!(f, "IN {origin} nil"),
            TokenKind::Break => write!(f, "BREAK {origin} nil"),
            TokenKind::Const => write!(f, "CONST {origin} nil"),
            TokenKind::Import => write!(f, "IMPORT {origin} nil"),
            TokenKind::Let => write!(f, "LET {origin} nil "),
            TokenKind::Loop => write!(f, "LOOP {origin} nil"),
            TokenKind::Package => write!(f, "PACKAGE {origin} nil"),
            TokenKind::Namespace => write!(f, "NAMESPACE {origin} nil"),
            TokenKind::Void => write!(f, "VOID {origin} nil"),
            TokenKind::As => write!(f, "AS {origin} nil"),
            TokenKind::LeftParen => write!(f, "LEFT_PAREN {origin} nil"),
            TokenKind::RightParen => write!(f, "RIGHT_PAREN {origin} nil"),
            TokenKind::LeftBrace => write!(f, "LEFT_BRACE {origin} nil"),
            TokenKind::RightBrace => write!(f, "RIGHT_BRACE {origin} nil"),
            TokenKind::Star => write!(f, "STAR {origin} nil"),
            TokenKind::Dot => write!(f, "DOT {origin} nil"),
            TokenKind::Comma => write!(f, "COMMA {origin} nil"),
            TokenKind::Plus => write!(f, "PLUS {origin} nil"),
            TokenKind::Minus => write!(f, "MINUS {origin} nil"),
            TokenKind::Semicolon => write!(f, "SEMICOLON {origin} nil"),
            TokenKind::String => write!(f, "STRING {origin} {}", Token::unescape(origin)),
            TokenKind::Ident => write!(f, "IDENTIFIER {origin} nil"),
            TokenKind::Number(n) => {
                if n.fract() == 0.0 {
                    write!(f, "NUMBER {origin} {n}.0")
                } else {
                    write!(f, "NUMBER {origin} {n}")
                }
            }
            TokenKind::And => write!(f, "AND {origin} nil"),
            TokenKind::Class => write!(f, "CLASS {origin} nil"),
            TokenKind::Else => write!(f, "ELSE {origin} nil"),
            TokenKind::False => write!(f, "FALSE {origin} nil"),
            TokenKind::For => write!(f, "FOR {origin} nil"),
            TokenKind::Function => write!(f, "FUN {origin} nil"),
            TokenKind::If => write!(f, "IF {origin} nil"),
            TokenKind::Null => write!(f, "NIL {origin} nil"),
            TokenKind::Or => write!(f, "OR {origin} nil"),
            TokenKind::Print => write!(f, "PRINT {origin} nil"),
            TokenKind::Return => write!(f, "RETURN {origin} nil"),
            TokenKind::Super => write!(f, "SUPER {origin} nil"),
            TokenKind::This => write!(f, "THIS {origin} nil"),
            TokenKind::True => write!(f, "TRUE {origin} nil"),
            TokenKind::Var => write!(f, "VAR {origin} nil"),
            TokenKind::While => write!(f, "WHILE {origin} nil"),
            TokenKind::Not => write!(f, "BANG {origin} nil"),
            TokenKind::NotEqual => write!(f, "BANG_EQUAL {origin} nil"),
            TokenKind::Equal => write!(f, "EQUAL {origin} nil"),
            TokenKind::EqualEqual => write!(f, "EQUAL_EQUAL {origin} nil"),
            TokenKind::Greater => write!(f, "GREATER {origin} nil"),
            TokenKind::GreaterEqual => write!(f, "GREATER_EQUAL {origin} nil"),
            TokenKind::Less => write!(f, "LESS {origin} nil"),
            TokenKind::LessEqual => write!(f, "LESS_EQUAL {origin} nil"),
            TokenKind::Slash => write!(f, "SLASH {origin} nil"),
            TokenKind::Eof => write!(f, "EOF  nil"),
        }
    }
}

pub struct Lexer<'src> {
    whole: &'src str,
    rest: &'src str,
    byte: usize,
    line: usize,
    peeked: Option<Result<Token<'src>, miette::Error>>,
}

impl<'src> Lexer<'src> {
    pub fn new(input: &'src str) -> Self {
        Self {
            whole: input,
            rest: input,
            byte: 0,
            line: 1,
            peeked: None,
        }
    }

    pub fn expect(
        &mut self,
        expected: TokenKind,
        unexpected: &str,
    ) -> Result<Token<'src>, miette::Error> {
        self.expect_where(|next| next.kind == expected, unexpected)
    }

    pub fn expect_where(
        &mut self,
        mut check: impl FnMut(&Token<'src>) -> bool,
        unexpected: &str,
    ) -> Result<Token<'src>, miette::Error> {
        match self.next() {
            Some(Ok(token)) if check(&token) => Ok(token),
            Some(Ok(token)) => Err(miette::miette! {
                labels = vec![LabeledSpan::at(
                    token.offset..token.offset + token.origin.len(),
                    unexpected
                )],
                help = format!("Unexpected {token:?}"),
                "{unexpected}",
            }),
            Some(Err(e)) => Err(e),
            None => Err(Eof.into()),
        }
    }

    pub fn peek(&mut self) -> Option<&Result<Token<'src>, miette::Error>> {
        if self.peeked.is_none() {
            self.peeked = self.next();
        }
        self.peeked.as_ref()
    }
}

impl<'src> Iterator for Lexer<'src> {
    type Item = Result<Token<'src>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(peeked) = self.peeked.take() {
            return Some(peeked);
        }
        loop {
            let mut chars = self.rest.chars();
            let c = chars.next()?;
            let c_at = self.byte;
            let c_str = &self.rest[..c.len_utf8()];
            let c_onwards = self.rest;
            self.byte += c.len_utf8();
            self.rest = chars.as_str();

            enum Started {
                Slash,
                String,
                Number,
                Ident,
                OrEqual(TokenKind, TokenKind),
            }

            let line = self.line;
            let just = move |kind: TokenKind| {
                Some(Ok(Token {
                    kind,
                    line,
                    offset: c_at,
                    origin: c_str,
                }))
            };

            let started = match c {
                '(' => return just(TokenKind::LeftParen),
                ')' => return just(TokenKind::RightParen),
                '{' => return just(TokenKind::LeftBrace),
                '}' => return just(TokenKind::RightBrace),
                ',' => return just(TokenKind::Comma),
                '.' => return just(TokenKind::Dot),
                '-' => return just(TokenKind::Minus),
                '+' => return just(TokenKind::Plus),
                ';' => return just(TokenKind::Semicolon),
                '*' => return just(TokenKind::Star),
                '/' => Started::Slash,
                '<' => Started::OrEqual(TokenKind::Less, TokenKind::LessEqual),
                '>' => Started::OrEqual(TokenKind::Greater, TokenKind::GreaterEqual),
                '!' => Started::OrEqual(TokenKind::Not, TokenKind::NotEqual),
                '=' => Started::OrEqual(TokenKind::Equal, TokenKind::EqualEqual),
                '"' => Started::String,
                '0'..='9' => Started::Number,
                'a'..='z' | 'A'..='Z' | '_' => Started::Ident,
                '\n' => {
                    self.line += 1;
                    continue;
                }
                c if c.is_whitespace() => continue,
                c => {
                    let line = self.line;
                    return Some(Err(miette::miette! {
                        labels = vec![LabeledSpan::at(
                            self.byte-c.len_utf8()..self.byte,
                            "Unexpected character"
                        )],
                        "[line {line}] Error: Unexpected character: {c}",
                    }
                    .with_source_code(self.whole.to_string())));
                }
            };

            break match started {
                Started::Slash => {
                    if self.rest.starts_with('/') {
                        let comment_end = self.rest.find('\n').unwrap_or(self.rest.len());
                        self.byte += comment_end;
                        self.rest = &self.rest[comment_end..];
                        continue;
                    } else {
                        Some(Ok(Token {
                            kind: TokenKind::Slash,
                            line: self.line,
                            offset: c_at,
                            origin: c_str,
                        }))
                    }
                }
                Started::String => {
                    if let Some(end) = self.rest.find('"') {
                        self.byte += end + 1;
                        self.rest = &self.rest[end + 1..];
                        let literal = &c_onwards[..end + 1 + 1]; // + starting one + ending
                                                                 // one
                        Some(Ok(Token {
                            kind: TokenKind::String,
                            line: self.line,
                            offset: c_at,
                            origin: literal,
                        }))
                    } else {
                        let line = self.line;
                        self.rest = "";
                        let offset = self.byte - c.len_utf8()..self.byte + self.rest.len();
                        self.byte += self.rest.len();
                        return Some(Err(miette::miette! {
                            labels = vec![LabeledSpan::at(
                                offset,
                                "Unterminated string"
                            )],
                            "[line {line}] Error: Unterminated string.",
                        }
                        .with_source_code(self.whole.to_string())));
                    }
                }
                Started::Ident => {
                    let first_non_ident = c_onwards
                        .find(|c| !matches!(c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_'))
                        .unwrap_or(c_onwards.len());

                    let literal = &c_onwards[..first_non_ident];
                    let extra_bytes = literal.len() - c.len_utf8();
                    self.byte += extra_bytes;
                    self.rest = &self.rest[extra_bytes..];

                    let kind = match keywords().get(literal) {
                        Some(kind) => *kind,
                        None => TokenKind::Ident,
                    };

                    Some(Ok(Token {
                        kind,
                        line: self.line,
                        offset: c_at,
                        origin: literal,
                    }))
                }
                Started::Number => {
                    let mut found_dot = false;
                    let first_non_digit = c_onwards
                        .find(|c| match c {
                            '.' => {
                                if !found_dot {
                                    found_dot = true;
                                    false
                                } else {
                                    true
                                }
                            }
                            '0'..='9' => false,
                            _ => true,
                        })
                        .unwrap_or(c_onwards.len());

                    // if first_non_digit != 0 && c_onwards[..first_non_digit].ends_with('.') {
                    //     first_non_digit -= 1;
                    // }

                    self.byte += first_non_digit;
                    self.rest = &self.rest[first_non_digit - 1..];

                    let literal = &c_onwards[..first_non_digit];
                    let number = literal.parse().expect("number");
                    Some(Ok(Token {
                        kind: TokenKind::Number(number),
                        line: self.line,
                        offset: c_at,
                        origin: literal,
                    }))
                }
                Started::OrEqual(token, or_else) => {
                    if self.rest.starts_with('=') {
                        let span = &c_onwards[..c.len_utf8() + 1];
                        self.rest = &self.rest[1..];
                        self.byte += 1;
                        Some(Ok(Token {
                            kind: or_else,
                            line: self.line,
                            offset: c_at,
                            origin: span,
                        }))
                    } else {
                        Some(Ok(Token {
                            kind: token,
                            line: self.line,
                            offset: c_at,
                            origin: c_str,
                        }))
                    }
                }
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_good_identifier() {
        let good = vec![
            "foo", "_foo", "FOO", "_FOO", "foo_bar", "foo_BAR_", "foo123", "foo_123",
        ];
        for t in good {
            let mut lexer = Lexer::new(t);
            let token = lexer.next().unwrap().unwrap();
            assert_eq!(token.kind, TokenKind::Ident);
            assert_eq!(token.origin, t);
        }
    }

    #[test]
    fn test_bad_identifier() {
        let bad = vec!["123", "123foo", "123_foo", "123_FOO"];
        for t in bad {
            let mut lexer = Lexer::new(t);
            let token = lexer.next().unwrap().unwrap();
            assert_ne!(token.kind, TokenKind::Ident);
        }
    }

    #[test]
    fn keywords_are_identified() {
        let kw = keywords().keys().copied().collect::<Vec<_>>();
        for t in kw {
            let mut lexer = Lexer::new(t);
            let token = lexer.next().unwrap().unwrap();
            assert_eq!(token.kind, *keywords().get(t).unwrap());
        }
    }
}
