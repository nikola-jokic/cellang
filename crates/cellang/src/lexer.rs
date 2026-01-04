use crate::SyntaxError;
use core::fmt;
use miette::SourceSpan;
use std::{borrow::Cow, collections::HashMap, sync::OnceLock};

/// Token represents a single token in the source code.
/// The token from the lexer is used by the parser to build the AST (or a TokenTree).
/// It is up to the parser to decide how to use the token.
#[derive(Debug, PartialEq, Clone)]
pub struct Token<'src> {
    pub origin: &'src str,
    pub offset: usize,
    pub span_len: usize,
    pub ty: TokenType,
}

impl Token<'_> {
    /// Unescape a string literal. Unescaping is done according to the CEL specification.
    /// Example:
    /// ```rust
    /// use cellang::lexer::Token;
    /// let escaped = r#"Hello\nWorld\u0021"#;
    ///
    /// let unescaped = Token::unescape(escaped);
    /// assert_eq!(unescaped, "Hello\nWorld!");
    /// ```
    pub fn unescape(s: &str) -> Cow<'_, str> {
        unescape(s)
    }

    /// Unescape a byte string literal. Unescaping is done according to the CEL specification.
    /// Example:
    /// ```rust
    /// use cellang::lexer::Token;
    /// let escaped = r#"Hello\nWorld\u0021"#;
    ///
    /// let unescaped = Token::unescape_bytes(escaped);
    /// assert_eq!(unescaped.as_ref(), b"Hello\nWorld!");
    /// ```
    pub fn unescape_bytes(s: &str) -> Cow<'_, [u8]> {
        let out = unescape(s);
        Cow::Owned(out.as_bytes().to_vec())
    }
}

/// TokenType represents the type of the token.
/// It is used by the parser to build the AST.
/// The parser is responsible for deciding how to interpret the token.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum TokenType {
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
    Dot,
    Comma,
    Plus,
    Percent,
    Minus,
    Semicolon,
    Not,
    NotEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    QuestionMark,
    LessEqual,
    Slash,
    Colon,
    RawString,
    Star,
    String,
    Bytes,
    RawBytes,
    Ident,
    Int(i64),
    Uint(u64),
    Double(f64),
    And,
    As,
    Break,
    Const,
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
    True,
    Var,
    Package,
    Namespace,
    Void,
    While,
    Dyn,
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenType::LeftParen => write!(f, "'('"),
            TokenType::RightParen => write!(f, "')'"),
            TokenType::LeftBracket => write!(f, "'['"),
            TokenType::RightBracket => write!(f, "']'"),
            TokenType::LeftBrace => write!(f, "'{{'"),
            TokenType::RightBrace => write!(f, "'}}'"),
            TokenType::Dot => write!(f, "'.'"),
            TokenType::Comma => write!(f, "','"),
            TokenType::Plus => write!(f, "'+'"),
            TokenType::Percent => write!(f, "'%'"),
            TokenType::Minus => write!(f, "'-'"),
            TokenType::Semicolon => write!(f, "';'"),
            TokenType::Not => write!(f, "'!'"),
            TokenType::NotEqual => write!(f, "'!='"),
            TokenType::Equal => write!(f, "'='"),
            TokenType::EqualEqual => write!(f, "'=='"),
            TokenType::Greater => write!(f, "'>'"),
            TokenType::GreaterEqual => write!(f, "'>='"),
            TokenType::Less => write!(f, "'<'"),
            TokenType::QuestionMark => write!(f, "'?'"),
            TokenType::LessEqual => write!(f, "'<='"),
            TokenType::Slash => write!(f, "'/'"),
            TokenType::Colon => write!(f, "':'"),
            TokenType::RawString => write!(f, "RAW_STRING"),
            TokenType::Star => write!(f, "'*'"),
            TokenType::String => write!(f, "STRING"),
            TokenType::Bytes => write!(f, "BYTES"),
            TokenType::RawBytes => write!(f, "RAW_BYTES"),
            TokenType::Ident => write!(f, "IDENTIFIER"),
            TokenType::Int(n) => write!(f, "INT {}", n),
            TokenType::Uint(n) => write!(f, "UINT {}", n),
            TokenType::Double(n) => write!(f, "DOUBLE {}", n),
            TokenType::And => write!(f, "'&&'"),
            TokenType::Or => write!(f, "'||'"),
            TokenType::True => write!(f, "'true'"),
            TokenType::False => write!(f, "'false'"),
            TokenType::Null => write!(f, "'null'"),
            TokenType::In => write!(f, "'in'"),
            TokenType::As => write!(f, "'as'"),
            TokenType::Break => write!(f, "'break'"),
            TokenType::Const => write!(f, "'const'"),
            TokenType::Else => write!(f, "'else'"),
            TokenType::For => write!(f, "'for'"),
            TokenType::Function => write!(f, "'function'"),
            TokenType::If => write!(f, "'if'"),
            TokenType::Import => write!(f, "'import'"),
            TokenType::Let => write!(f, "'let'"),
            TokenType::Loop => write!(f, "'loop'"),
            TokenType::Package => write!(f, "'package'"),
            TokenType::Namespace => write!(f, "'namespace'"),
            TokenType::Var => write!(f, "'var'"),
            TokenType::Void => write!(f, "'void'"),
            TokenType::While => write!(f, "'while'"),
            TokenType::Dyn => write!(f, "'dyn'"),
        }
    }
}

fn keywords() -> &'static HashMap<&'static str, TokenType> {
    static KEYWORDS: OnceLock<HashMap<&'static str, TokenType>> =
        OnceLock::new();
    KEYWORDS.get_or_init(|| {
        let mut map = HashMap::new();
        map.insert("true", TokenType::True);
        map.insert("false", TokenType::False);
        map.insert("null", TokenType::Null);
        map.insert("in", TokenType::In);
        map.insert("as", TokenType::As);
        map.insert("break", TokenType::Break);
        map.insert("const", TokenType::As);
        map.insert("continue", TokenType::Const);
        map.insert("else", TokenType::Else);
        map.insert("for", TokenType::For);
        map.insert("function", TokenType::Function);
        map.insert("if", TokenType::If);
        map.insert("import", TokenType::Import);
        map.insert("let", TokenType::Let);
        map.insert("loop", TokenType::Loop);
        map.insert("package", TokenType::Package);
        map.insert("namespace", TokenType::Namespace);
        map.insert("var", TokenType::Var);
        map.insert("void", TokenType::Void);
        map.insert("while", TokenType::While);

        map
    })
}

fn single_char_escape() -> &'static HashMap<char, char> {
    static SINGLE_CHAR_ESCAPE: OnceLock<HashMap<char, char>> = OnceLock::new();
    // https://github.com/google/cel-spec/blob/master/doc/langdef.md#string-and-bytes-values
    SINGLE_CHAR_ESCAPE.get_or_init(|| {
        let mut map = HashMap::new();
        // A punctuation mark representing itself
        map.insert('\\', '\\');
        map.insert('?', '?');
        map.insert('"', '"');
        map.insert('\'', '\'');
        map.insert('`', '`');

        // A code for whitespace:
        map.insert('a', '\x07');
        map.insert('b', '\x08');
        map.insert('f', '\x0c');
        map.insert('n', '\n');
        map.insert('r', '\r');
        map.insert('t', '\t');
        map.insert('v', '\x0b');
        map
    })
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let origin = self.origin;
        match self.ty {
            TokenType::QuestionMark => write!(f, "QUESTIONMARK {origin} nil"),
            TokenType::Star => write!(f, "STAR {origin} nil"),
            TokenType::Colon => write!(f, "COLON {origin} nil"),
            TokenType::In => write!(f, "IN {origin} nil"),
            TokenType::Break => write!(f, "BREAK {origin} nil"),
            TokenType::Const => write!(f, "CONST {origin} nil"),
            TokenType::Import => write!(f, "IMPORT {origin} nil"),
            TokenType::Let => write!(f, "LET {origin} nil "),
            TokenType::Loop => write!(f, "LOOP {origin} nil"),
            TokenType::Package => write!(f, "PACKAGE {origin} nil"),
            TokenType::Namespace => write!(f, "NAMESPACE {origin} nil"),
            TokenType::Void => write!(f, "VOID {origin} nil"),
            TokenType::As => write!(f, "AS {origin} nil"),
            TokenType::LeftParen => write!(f, "LEFT_PAREN {origin} nil"),
            TokenType::RightParen => write!(f, "RIGHT_PAREN {origin} nil"),
            TokenType::LeftBracket => write!(f, "LEFT_BRACKET {origin} nil"),
            TokenType::RightBracket => write!(f, "RIGHT_BRACKET {origin} nil"),
            TokenType::LeftBrace => write!(f, "LEFT_BRACE {origin} nil"),
            TokenType::RightBrace => write!(f, "RIGHT_BRACE {origin} nil"),
            TokenType::Dot => write!(f, "DOT {origin} nil"),
            TokenType::Comma => write!(f, "COMMA {origin} nil"),
            TokenType::Plus => write!(f, "PLUS {origin} nil"),
            TokenType::Minus => write!(f, "MINUS {origin} nil"),
            TokenType::Semicolon => write!(f, "SEMICOLON {origin} nil"),
            TokenType::Dyn => write!(f, "DYN {origin} nil"),
            TokenType::String => {
                write!(f, "STRING {origin} {}", Token::unescape(origin))
            }
            TokenType::RawString => {
                write!(f, "RAW_STRING {origin} {}", Token::unescape(origin))
            }
            TokenType::Ident => write!(f, "IDENTIFIER {origin} nil"),
            TokenType::Int(n) => write!(f, "INT {origin} {n}"),
            TokenType::Uint(n) => write!(f, "UINT {origin} {n}"),
            TokenType::Double(n) => write!(f, "DOUBLE {origin} {n}"),
            TokenType::Bytes => write!(f, "BYTES {origin} nil"),
            TokenType::RawBytes => write!(f, "RAW_BYTES {origin} nil"),
            TokenType::And => write!(f, "AND {origin} nil"),
            TokenType::Else => write!(f, "ELSE {origin} nil"),
            TokenType::False => write!(f, "FALSE {origin} nil"),
            TokenType::For => write!(f, "FOR {origin} nil"),
            TokenType::Function => write!(f, "FUN {origin} nil"),
            TokenType::If => write!(f, "IF {origin} nil"),
            TokenType::Null => write!(f, "NIL {origin} nil"),
            TokenType::Or => write!(f, "OR {origin} nil"),
            TokenType::True => write!(f, "TRUE {origin} nil"),
            TokenType::Var => write!(f, "VAR {origin} nil"),
            TokenType::While => write!(f, "WHILE {origin} nil"),
            TokenType::Not => write!(f, "BANG {origin} nil"),
            TokenType::NotEqual => write!(f, "BANG_EQUAL {origin} nil"),
            TokenType::Equal => write!(f, "EQUAL {origin} nil"),
            TokenType::EqualEqual => write!(f, "EQUAL_EQUAL {origin} nil"),
            TokenType::Greater => write!(f, "GREATER {origin} nil"),
            TokenType::GreaterEqual => write!(f, "GREATER_EQUAL {origin} nil"),
            TokenType::Less => write!(f, "LESS {origin} nil"),
            TokenType::LessEqual => write!(f, "LESS_EQUAL {origin} nil"),
            TokenType::Slash => write!(f, "SLASH {origin} nil"),
            TokenType::Percent => write!(f, "PERCENT {origin} nil"),
        }
    }
}

/// Lexer is a simple lexer that tokenizes the source code.
/// It is used by the parser to build the AST.
///
/// The lexer implements the Iterator trait and returns a token at a time.
pub struct Lexer<'src> {
    whole: &'src str,
    rest: &'src str,
    byte: usize,
    peeked: Option<Result<Token<'src>, SyntaxError>>,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer from the source code.
    pub fn new(input: &'src str) -> Self {
        Self {
            whole: input,
            rest: input,
            byte: 0,
            peeked: None,
        }
    }

    /// Expect a token of a specific type.
    /// If the next token is not of the expected type, an error is returned
    /// with a labeled span pointing to the unexpected token and an error message
    /// provided by the caller.
    pub fn expect(
        &mut self,
        expected: TokenType,
        unexpected: &str,
    ) -> Result<Token<'src>, SyntaxError> {
        self.expect_where(|next| next.ty == expected, unexpected)
    }

    /// Expect a token that satisfies a predicate.
    /// If the next token does not satisfy the predicate, an error is returned
    /// with a labeled span pointing to the unexpected token and an error message
    /// provided by the caller.
    pub fn expect_where(
        &mut self,
        mut check: impl FnMut(&Token<'src>) -> bool,
        unexpected: &str,
    ) -> Result<Token<'src>, SyntaxError> {
        match self.next() {
            Some(Ok(token)) if check(&token) => Ok(token),
            Some(Ok(token)) => Err(SyntaxError::new(
                self.whole.to_string(),
                SourceSpan::new(token.offset.into(), token.span_len),
                unexpected.to_string(),
            )),
            Some(Err(e)) => Err(e),
            None => Err(SyntaxError::new(
                self.whole.to_string(),
                SourceSpan::new(self.byte.into(), 0),
                format!("Unexpected end of file, expected {unexpected}"),
            )),
        }
    }

    /// Peek at the next token without consuming it.
    /// The peeked token is returned by the next call to next().
    pub fn peek(&mut self) -> Option<&Result<Token<'src>, SyntaxError>> {
        if self.peeked.is_none() {
            self.peeked = self.next();
        }
        self.peeked.as_ref()
    }

    #[inline]
    fn read_extra(&mut self, n: usize) {
        self.byte += n;
        if n == self.rest.len() {
            self.rest = "";
        } else {
            self.rest = &self.rest[n..];
        }
    }
}

impl<'src> Iterator for Lexer<'src> {
    type Item = Result<Token<'src>, SyntaxError>;

    /// Get the next token from the source code.
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
                RawString,
                Bytes,
                RawBytes,
                DecimalNumber,
                HexNumber,
                Ident,
                OrEqual(TokenType, TokenType),
            }

            let just = move |ty: TokenType| {
                Some(Ok(Token {
                    ty,
                    offset: c_at,
                    span_len: c_str.len(),
                    origin: c_str,
                }))
            };

            let started = match c {
                '(' => return just(TokenType::LeftParen),
                ')' => return just(TokenType::RightParen),
                '[' => return just(TokenType::LeftBracket),
                ']' => return just(TokenType::RightBracket),
                '{' => return just(TokenType::LeftBrace),
                '}' => return just(TokenType::RightBrace),
                ':' => return just(TokenType::Colon),
                ',' => return just(TokenType::Comma),
                '.' => {
                    if self.rest.starts_with(|c: char| c.is_ascii_digit()) {
                        Started::DecimalNumber
                    } else {
                        return just(TokenType::Dot);
                    }
                }
                '*' => return just(TokenType::Star),
                '%' => return just(TokenType::Percent),
                '/' => Started::Slash,
                '-' => return just(TokenType::Minus),
                '+' => return just(TokenType::Plus),
                ';' => return just(TokenType::Semicolon),
                '<' => Started::OrEqual(TokenType::Less, TokenType::LessEqual),
                '>' => Started::OrEqual(
                    TokenType::Greater,
                    TokenType::GreaterEqual,
                ),
                '!' => Started::OrEqual(TokenType::Not, TokenType::NotEqual),
                '=' => {
                    Started::OrEqual(TokenType::Equal, TokenType::EqualEqual)
                }
                '"' | '\'' => Started::String,
                '?' => return just(TokenType::QuestionMark),
                '&' => {
                    if self.rest.starts_with('&') {
                        self.byte += 1;
                        self.rest = &self.rest[1..];
                        return just(TokenType::And);
                    } else {
                        return Some(Err(SyntaxError::new(
                            self.whole.to_string(),
                            SourceSpan::new(c_at.into(), self.byte - c_at),
                            format!("Error: Unexpected character: {c}"),
                        )
                        .with_help("expected `&&`")));
                    }
                }
                '|' => {
                    if self.rest.starts_with('|') {
                        self.byte += 1;
                        self.rest = &self.rest[1..];
                        return just(TokenType::Or);
                    } else {
                        return Some(Err(SyntaxError::new(
                            self.whole.to_string(),
                            SourceSpan::new(c_at.into(), self.byte - c_at),
                            format!("Error: Unexpected character: {c}"),
                        )
                        .with_help("expected `||`")));
                    }
                }
                '0'..='9' => {
                    if c == '0' && self.rest.starts_with("x") {
                        Started::HexNumber
                    } else {
                        Started::DecimalNumber
                    }
                }
                c if matches!(c, 'a'..='z' | 'A'..='Z' | '_') => match c {
                    'r' | 'R' => {
                        if self.rest.starts_with(['"', '\'']) {
                            Started::RawString
                        } else if self.rest.starts_with(['b', 'B']) {
                            let rest = &self.rest[1..];
                            if rest.starts_with(['"', '\'']) {
                                Started::RawBytes
                            } else {
                                Started::Ident
                            }
                        } else {
                            Started::Ident
                        }
                    }
                    'b' | 'B' => {
                        if self.rest.starts_with(['"', '\'']) {
                            Started::Bytes
                        } else if self.rest.starts_with(['r', 'R']) {
                            let rest = &self.rest[1..];
                            if rest.starts_with(['"', '\'']) {
                                Started::RawBytes
                            } else {
                                Started::Ident
                            }
                        } else {
                            Started::Ident
                        }
                    }
                    _ => Started::Ident,
                },
                '\n' | '\r' => {
                    continue;
                }
                c if c.is_whitespace() => continue,
                c => {
                    return Some(Err(SyntaxError::new(
                        self.whole.to_string(),
                        SourceSpan::new(c_at.into(), self.byte - c_at),
                        format!("Error: Unexpected character: {c}"),
                    )));
                }
            };

            break match started {
                Started::Slash => {
                    if self.rest.starts_with('/') {
                        let comment_end = self
                            .rest
                            .find(['\n', '\r'])
                            .unwrap_or(self.rest.len());
                        self.byte += comment_end;
                        self.rest = &self.rest[comment_end..];
                        continue;
                    } else {
                        Some(Ok(Token {
                            ty: TokenType::Slash,
                            offset: c_at,
                            span_len: self.byte - c_at,
                            origin: c_str,
                        }))
                    }
                }
                Started::String => {
                    let (n, literal) = match scan_str(c_onwards) {
                        Ok(literal) => literal,
                        Err(e) => return Some(Err(e)),
                    };

                    let extra_bytes = n - c.len_utf8();
                    self.read_extra(extra_bytes);
                    Some(Ok(Token {
                        ty: TokenType::String,
                        offset: c_at,
                        span_len: self.byte - c_at,
                        origin: literal,
                    }))
                }
                Started::RawString => {
                    // starts with r
                    let rest = &c_onwards[1..]; // ignore r
                    let (n, literal) = match read_str_raw(rest) {
                        Ok(literal) => literal,
                        Err(e) => return Some(Err(e)),
                    };

                    self.read_extra(n);
                    Some(Ok(Token {
                        ty: TokenType::RawString,
                        offset: c_at,
                        span_len: self.byte - c_at,
                        origin: literal,
                    }))
                }
                Started::Bytes => {
                    // starts with b
                    let rest = &c_onwards[1..]; // ignore b
                    let (n, literal) = match scan_str(rest) {
                        Ok(literal) => literal,
                        Err(e) => return Some(Err(e)),
                    };
                    self.read_extra(n);
                    Some(Ok(Token {
                        ty: TokenType::Bytes,
                        offset: c_at,
                        span_len: self.byte - c_at,
                        origin: literal,
                    }))
                }
                Started::RawBytes => {
                    // starts with rb or br (case-insensitive)
                    let rest = &c_onwards[2..]; // ignore r
                    let (n, literal) = match read_str_raw(rest) {
                        Ok(literal) => literal,
                        Err(e) => return Some(Err(e)),
                    };

                    let extra_bytes = n + 1;
                    self.read_extra(extra_bytes);
                    Some(Ok(Token {
                        ty: TokenType::RawBytes,
                        offset: c_at,
                        span_len: self.byte - c_at,
                        origin: literal,
                    }))
                }
                Started::Ident => {
                    let first_non_ident = c_onwards
                        .find(|c| !matches!(c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_'))
                        .unwrap_or(c_onwards.len());

                    let literal = &c_onwards[..first_non_ident];
                    let extra_bytes = literal.len() - c.len_utf8();
                    self.byte += extra_bytes;
                    self.rest = &self.rest[extra_bytes..];

                    let ty = match keywords().get(literal) {
                        Some(ty) => *ty,
                        None => TokenType::Ident,
                    };

                    let span_len = self.byte - c_at;
                    if literal == "dyn" {
                        Some(Ok(Token {
                            ty: TokenType::Dyn,
                            offset: c_at,
                            span_len,
                            origin: literal,
                        }))
                    } else {
                        Some(Ok(Token {
                            ty,
                            offset: c_at,
                            span_len,
                            origin: literal,
                        }))
                    }
                }
                Started::DecimalNumber => {
                    enum State {
                        Nil,
                        Int,
                        Uint,
                        Dot,
                        Fraction,
                        Exp,
                        ExpSign,
                        ExpDigit,
                    }

                    let mut state = State::Nil;
                    let mut index = 0;
                    for c in c_onwards.chars() {
                        state = match (&state, c) {
                            (State::Nil | State::Int, '.') => State::Dot,
                            (State::Nil, c) if c.is_ascii_digit() => State::Int,
                            (State::Int, 'u') | (State::Int, 'U') => {
                                State::Uint
                            }
                            (State::Int, 'e') | (State::Int, 'E') => State::Exp,
                            (State::Int, c) if c.is_ascii_digit() => State::Int,
                            (State::Dot, c) if c.is_ascii_digit() => {
                                State::Fraction
                            }
                            (State::Fraction, 'e') | (State::Fraction, 'E') => {
                                State::Exp
                            }
                            (State::Fraction, c) if c.is_ascii_digit() => {
                                State::Fraction
                            }
                            (State::Exp, '+') | (State::Exp, '-') => {
                                State::ExpSign
                            }
                            (
                                State::Exp | State::ExpSign | State::ExpDigit,
                                c,
                            ) if c.is_ascii_digit() => State::ExpDigit,
                            (State::ExpSign, c) if c.is_ascii_digit() => {
                                State::ExpDigit
                            }
                            (State::ExpDigit, c) if c.is_ascii_digit() => {
                                State::ExpDigit
                            }
                            _ => break,
                        };
                        index += c.len_utf8();
                    }

                    match state {
                        State::Nil => {
                            return Some(Err(SyntaxError::new(
                                self.whole.to_string(),
                                SourceSpan::new(c_at.into(), self.byte - c_at),
                                format!("Error: Unexpected character: {c}"),
                            )
                            .with_help("Expected a number")));
                        }
                        State::Dot | State::Exp => {
                            // unread the dot or exp
                            let read = index - 1;
                            let extra_bytes = read - c.len_utf8();
                            self.read_extra(extra_bytes);
                            Some(Ok(Token {
                                ty: TokenType::Int(
                                    c_onwards[..read].parse().unwrap(),
                                ),
                                offset: c_at,
                                span_len: self.byte - c_at,
                                origin: &c_onwards[..read],
                            }))
                        }
                        State::ExpSign => {
                            // unread the exp sign
                            let read = index - 2;
                            let extra_bytes = index - 2 - c.len_utf8();
                            self.read_extra(extra_bytes);
                            Some(Ok(Token {
                                ty: TokenType::Int(
                                    c_onwards[..read].parse().unwrap(),
                                ),
                                offset: c_at,
                                span_len: self.byte - c_at,
                                origin: &c_onwards[..read],
                            }))
                        }
                        State::Int => {
                            let extra_bytes = index - c.len_utf8();
                            self.read_extra(extra_bytes);
                            Some(Ok(Token {
                                ty: TokenType::Int(
                                    c_onwards[..index].parse().unwrap(),
                                ),
                                offset: c_at,
                                span_len: self.byte - c_at,
                                origin: &c_onwards[..index],
                            }))
                        }
                        State::Uint => {
                            let extra_bytes = index - c.len_utf8();
                            self.read_extra(extra_bytes);
                            Some(Ok(Token {
                                ty: TokenType::Uint(
                                    c_onwards[..index - 1].parse().unwrap(),
                                ),
                                offset: c_at,
                                span_len: self.byte - c_at,
                                origin: &c_onwards[..index],
                            }))
                        }
                        State::Fraction | State::ExpDigit => {
                            let extra_bytes = index - c.len_utf8();
                            self.read_extra(extra_bytes);
                            Some(Ok(Token {
                                ty: TokenType::Double(
                                    c_onwards[..index].parse().unwrap(),
                                ),
                                offset: c_at,
                                span_len: self.byte - c_at,
                                origin: &c_onwards[..index],
                            }))
                        }
                    }
                }
                Started::HexNumber => {
                    let rest = &c_onwards[2..]; // ignore 0x
                    if rest.is_empty() {
                        return Some(Err(SyntaxError::new(
                            self.whole.to_string(),
                            SourceSpan::new(c_at.into(), self.byte - c_at),
                            format!("Error: Unexpected character: {c}"),
                        )
                        .with_help("Expected a number")));
                    }

                    let mut end = 0;
                    for c in rest.chars() {
                        match c {
                            'u' | 'U' => {
                                end += 1;
                                break;
                            }
                            c if c.is_ascii_hexdigit() => end += c.len_utf8(),
                            _ => break,
                        }
                    }

                    let extra_bytes = end + 2 - c.len_utf8();
                    self.read_extra(extra_bytes);

                    if c_onwards[..end + 2].ends_with(['u', 'U']) {
                        let literal = &c_onwards[..end + 2 - 1]; // ignore u
                        Some(Ok(Token {
                            ty: TokenType::Uint(
                                u64::from_str_radix(&literal[2..], 16).unwrap(),
                            ),
                            offset: c_at,
                            span_len: self.byte - c_at,
                            origin: literal,
                        }))
                    } else {
                        let literal = &c_onwards[..end + 2];
                        Some(Ok(Token {
                            ty: TokenType::Int(
                                i64::from_str_radix(&literal[2..], 16).unwrap(),
                            ),
                            offset: c_at,
                            span_len: self.byte - c_at,
                            origin: literal,
                        }))
                    }
                }
                Started::OrEqual(token, or_else) => {
                    if self.rest.starts_with('=') {
                        let span = &c_onwards[..c.len_utf8() + 1];
                        self.rest = &self.rest[1..];
                        self.byte += 1;
                        Some(Ok(Token {
                            ty: or_else,
                            offset: c_at,
                            span_len: self.byte - c_at,
                            origin: span,
                        }))
                    } else {
                        Some(Ok(Token {
                            ty: token,
                            offset: c_at,
                            span_len: self.byte - c_at,
                            origin: c_str,
                        }))
                    }
                }
            };
        }
    }
}

fn scan_str(s: &str) -> Result<(usize, &str), SyntaxError> {
    assert!(s.starts_with(['"', '\'']));

    if s.len() < 2 {
        return Err(SyntaxError::new(
            s.to_string(),
            SourceSpan::new(0.into(), s.len()),
            "Unexpected end of file",
        )
        .with_help("Expected a closing quote"));
    }

    let mut chars = s.chars();
    let delim_c = chars.next().unwrap();
    let delim_n = if s.starts_with(r#"""""#) || s.starts_with("'''") {
        // read rest of the delimiter
        chars.next().unwrap();
        chars.next().unwrap();
        3
    } else {
        1
    };

    let mut delim_hit = 0;
    let mut end = delim_n;
    loop {
        let c = match chars.next() {
            Some(c) => c,
            None => {
                return Err(SyntaxError::new(
                    s.to_string(),
                    SourceSpan::new(0.into(), end),
                    "Unexpected end of file",
                )
                .with_help("Expected a closing quote"));
            }
        };

        end += c.len_utf8();

        if delim_n == 1 && matches!(c, '\r' | '\n') {
            return Err(SyntaxError::new(
                s[..end].to_string(),
                SourceSpan::new((end - 1).into(), 1),
                "Unexpected newline in string",
            )
            .with_help("Unterminated string"));
        }

        // if it is a delimiter, check if it is the closing delimiter
        if c == delim_c {
            delim_hit += 1;
            if delim_hit == delim_n {
                return Ok((end, &s[delim_n..end - delim_n]));
            }
            continue;
        }
        delim_hit = 0;

        if c != '\\' {
            // Not a delimiter, not an escape
            continue;
        }

        // escape sequence
        let c = match chars.next() {
            Some(c) => c,
            None => {
                return Err(SyntaxError::new(
                    s.to_string(),
                    SourceSpan::new(0.into(), end),
                    "Unexpected end of file",
                )
                .with_help("Expected char after escape"));
            }
        };
        end += c.len_utf8();
        if single_char_escape().get(&c).is_some() {
            continue;
        }

        match c {
            'x' => {
                read_chars_tested(
                    &mut chars,
                    2,
                    is_hex,
                    "Expected 2 hex numbers on \\x",
                )?;
                end += 2;
            }
            'u' => {
                read_chars_tested(
                    &mut chars,
                    4,
                    is_hex,
                    "Expected 4 hex numbers after \\u",
                )?;
                end += 4;
            }
            'U' => {
                read_chars_tested(
                    &mut chars,
                    8,
                    is_hex,
                    "Expected 8 hex numbers after \\U",
                )?;
                end += 8;
            }
            '0'..='7' => {
                // one octal number is already read
                read_chars_tested(
                    &mut chars,
                    2,
                    is_octal,
                    "Expected 3 octal numbers after \\",
                )?;
                end += 2;
            }
            _ => {
                return Err(SyntaxError::new(
                    s.to_string(),
                    SourceSpan::new(0.into(), end),
                    format!("Unexpected character: {c}"),
                )
                .with_help("Expected a hex digit"));
            }
        }
    }
}

fn read_str_raw(s: &str) -> Result<(usize, &str), SyntaxError> {
    if s.len() < 2 {
        return Err(SyntaxError::new(
            s.to_string(),
            SourceSpan::new(0.into(), s.len()),
            "Unexpected end of file",
        )
        .with_help("Expected a closing quote"));
    }

    let take = if s.starts_with(r#"""""#) || s.starts_with("'''") {
        3
    } else {
        1
    };

    let delim = &s[..take];
    let rest = &s[take..];
    let end = match rest.find(delim) {
        Some(end) => end,
        None => {
            return Err(SyntaxError::new(
                s.to_string(),
                SourceSpan::new(0.into(), s.len()),
                "Unexpected end of file",
            )
            .with_help("Expected a closing quote"));
        }
    };

    Ok((end + 2 * take, &rest[..end]))
}

fn is_hex(c: char) -> bool {
    c.is_ascii_hexdigit()
}

fn is_octal(c: char) -> bool {
    matches!(c, '0'..='7')
}

fn read_chars_tested(
    chars: &mut impl Iterator<Item = char>,
    n: usize,
    test_fn: impl Fn(char) -> bool,
    err_msg: &str,
) -> Result<String, SyntaxError> {
    let mut buf = String::with_capacity(n);
    for _ in 0..n {
        let c = match chars.next() {
            Some(c) => c,
            None => {
                return Err(SyntaxError::new(
                    buf.clone(),
                    SourceSpan::new(0.into(), buf.len()),
                    "Unexpected end of file",
                )
                .with_help(err_msg.to_string()));
            }
        };

        if !test_fn(c) {
            return Err(SyntaxError::new(
                buf.clone(),
                SourceSpan::new(0.into(), buf.len()),
                format!("Unexpected character: {c}"),
            )
            .with_help(err_msg.to_string()));
        }

        buf.push(c);
    }
    Ok(buf)
}

pub(crate) fn unescape(s: &str) -> Cow<'_, str> {
    if !s.contains('\\') {
        return Cow::Borrowed(s);
    }

    let mut buf = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            buf.push(c);
            continue;
        }

        let c = match chars.next() {
            Some(c) => c,
            None => break,
        };

        if let Some(c) = single_char_escape().get(&c) {
            buf.push(*c);
            continue;
        }

        match c {
            'x' => {
                let c = u8::from_str_radix(
                    &read_chars_tested(
                        &mut chars,
                        2,
                        is_hex,
                        "Expected 2 hex numbers after \\x",
                    )
                    .expect("should be handled in lexing stage"),
                    16,
                )
                .unwrap();
                buf.push(c as char);
            }
            'u' => {
                let c = char::from_u32(
                    u32::from_str_radix(
                        &read_chars_tested(
                            &mut chars,
                            4,
                            is_hex,
                            "Expected 4 hex numbers after \\u",
                        )
                        .expect("should be handled in lexing stage"),
                        16,
                    )
                    .unwrap(),
                )
                .unwrap();
                buf.push(c);
            }
            'U' => {
                let c = char::from_u32(
                    u32::from_str_radix(
                        &read_chars_tested(
                            &mut chars,
                            8,
                            is_hex,
                            "Expected 8 hex numbers after \\U",
                        )
                        .expect("should be handled in lexing stage"),
                        16,
                    )
                    .unwrap(),
                )
                .unwrap();
                buf.push(c);
            }
            '0'..='7' => {
                let c = u8::from_str_radix(
                    &read_chars_tested(
                        &mut chars,
                        3,
                        is_octal,
                        "Expected 3 octal numbers after \\",
                    )
                    .expect("should be handled in lexing stage"),
                    8,
                )
                .unwrap();
                buf.push(c as char);
            }
            _ => unimplemented!(),
        }
    }

    Cow::Owned(buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[track_caller]
    fn assert_span_slice(source: &str, token: &Token<'_>, expected: &str) {
        let span = &source[token.offset..token.offset + token.span_len];
        assert_eq!(span, expected);
        assert_eq!(token.span_len, expected.len());
    }

    #[test]
    fn test_good_identifier() {
        let good = vec![
            "foo", "_foo", "FOO", "_FOO", "foo_bar", "foo_BAR_", "foo123",
            "foo_123",
        ];
        for t in good {
            let mut lexer = Lexer::new(t);
            let token = lexer.next().unwrap().unwrap();
            assert_eq!(token.ty, TokenType::Ident);
            assert_eq!(token.origin, t);
        }
    }

    #[test]
    fn test_bad_identifier() {
        let bad = vec!["123", "123foo", "123_foo", "123_FOO"];
        for t in bad {
            let mut lexer = Lexer::new(t);
            let token = lexer.next().unwrap();
            assert!(!matches!(
                token,
                Ok(Token {
                    ty: TokenType::Ident,
                    ..
                })
            ));
        }
    }

    #[test]
    fn keywords_are_identified() {
        let kw = keywords().keys().copied().collect::<Vec<_>>();
        for t in kw {
            let mut lexer = Lexer::new(t);
            let token = lexer.next().unwrap().unwrap();
            assert_eq!(token.ty, *keywords().get(t).unwrap());
        }
    }

    #[test]
    fn test_and() {
        let mut lexer = Lexer::new("&&");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::And);

        let mut lexer = Lexer::new("&|");
        let token = lexer.next().unwrap();
        assert!(token.is_err());
    }

    #[test]
    fn test_or() {
        let mut lexer = Lexer::new("||");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Or);

        let mut lexer = Lexer::new("|&");
        let token = lexer.next().unwrap();
        assert!(token.is_err());
    }

    #[test]
    fn test_decimal_parsing() {
        let mut lexer = Lexer::new("0");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Int(0));
        let token = lexer.next();
        assert!(token.is_none());

        let mut lexer = Lexer::new("123");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Int(123));
        let token = lexer.next();
        assert!(token.is_none());

        let mut lexer = Lexer::new("123u");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Uint(123));
        let token = lexer.next();
        assert!(token.is_none());

        let mut lexer = Lexer::new("123.");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Int(123));
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Dot);

        let mut lexer = Lexer::new("123u.");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Uint(123));
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Dot);

        let mut lexer = Lexer::new("123.123");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Double(123.123));
        let token = lexer.next();
        assert!(token.is_none(), "{:?}", token);

        let mut lexer = Lexer::new("123.123.");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Double(123.123));
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Dot);

        let mut lexer = Lexer::new("1.2e3");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Double(1.2e3));
        let token = lexer.next();
        assert!(token.is_none());

        let mut lexer = Lexer::new("1.2e+3");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Double(1.2e+3));
        let token = lexer.next();
        assert!(token.is_none());

        let mut lexer = Lexer::new("1.2e-3");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Double(1.2e-3));
        let token = lexer.next();
        assert!(token.is_none());

        let mut lexer = Lexer::new("1.2e3.");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Double(1.2e3));
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Dot);

        let mut lexer = Lexer::new(".2");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Double(0.2));
        let token = lexer.next();
        assert!(token.is_none());

        let mut lexer = Lexer::new(".2.");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Double(0.2));
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Dot);

        let mut lexer = Lexer::new(".2e3");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Double(0.2e3));
        let token = lexer.next();
        assert!(token.is_none());
    }

    #[test]
    fn test_hex_parsing() {
        let mut lexer = Lexer::new("0x123");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Int(0x123));
        let token = lexer.next();
        assert!(token.is_none());

        let mut lexer = Lexer::new("0x123.");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Int(0x123));
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Dot);

        let mut token = Lexer::new("0x");
        let token = token.next().unwrap();
        assert!(token.is_err(), "{:?}", token);
    }

    #[test]
    fn test_single_quote_string_parsing() {
        for delim in ['"', '\''] {
            let input = format!("{delim}foo{delim}");
            let mut lexer = Lexer::new(&input);
            let token = lexer.next().unwrap().unwrap();
            assert_eq!(token.ty, TokenType::String);
            assert_eq!(token.origin, "foo");
            let next = lexer.next();
            assert!(next.is_none());
        }
    }

    #[test]
    fn test_raw_string_parsing() {
        for delim in ['"', '\''] {
            for r in ["r", "R"] {
                let input = format!("{r}{delim}foo{delim}");
                let mut lexer = Lexer::new(&input);
                let token = lexer.next().unwrap().unwrap();
                assert_eq!(token.ty, TokenType::RawString);
                assert_eq!(token.origin, "foo");
                let next = lexer.next();
                assert!(next.is_none());
            }
        }
    }

    #[test]
    fn test_single_quote_bytes_parsing() {
        for delim in ['"', '\''] {
            for b in ["b", "B"] {
                let input = format!("{b}{delim}foo{delim}");
                let mut lexer = Lexer::new(&input);
                let token = lexer.next().unwrap().unwrap();
                assert_eq!(token.ty, TokenType::Bytes);
                assert_eq!(token.origin, "foo");
                let next = lexer.next();
                assert!(next.is_none());
            }
        }
    }

    #[test]
    fn test_tripple_quoted_string() {
        for delim in [r#"""""#, "'''"] {
            let input = format!("{delim}\nfoo\n{delim}");
            let mut lexer = Lexer::new(&input);
            let token = lexer.next().unwrap().unwrap();
            assert_eq!(token.ty, TokenType::String);
            assert_eq!(token.origin, "\nfoo\n");
            let next = lexer.next();
            assert!(next.is_none());
        }
    }

    #[test]
    fn test_raw_tripple_quoted_string() {
        for delim in [r#"""""#, "'''"] {
            for r in ["r", "R"] {
                let input = format!("{r}{delim}\nfoo\n{delim}");
                let mut lexer = Lexer::new(&input);
                let token = lexer.next().unwrap().unwrap();
                assert_eq!(token.ty, TokenType::RawString);
                assert_eq!(token.origin, "\nfoo\n");
                let next = lexer.next();
                assert!(next.is_none());
            }
        }
    }

    #[test]
    fn test_tripple_quoted_bytes() {
        for delim in [r#"""""#, "'''"] {
            for b in ["b", "B"] {
                let input = format!("{b}{delim}\nfoo\n{delim}", delim = delim);
                let mut lexer = Lexer::new(&input);
                let token = lexer.next().unwrap().unwrap();
                assert_eq!(token.ty, TokenType::Bytes);
                assert_eq!(token.origin, "\nfoo\n");
                let next = lexer.next();
                assert!(next.is_none());
            }
        }
    }

    #[test]
    fn test_raw_tripple_quoted_bytes() {
        for delim in [r#"""""#, "'''"] {
            for rb in ["rb", "rB", "Rb", "RB"] {
                let input = format!("{rb}{delim}\nfoo\n{delim}", delim = delim);
                let mut lexer = Lexer::new(&input);
                let token = lexer.next().unwrap().unwrap();
                assert_eq!(token.ty, TokenType::RawBytes);
                assert_eq!(token.origin, "\nfoo\n");
                let next = lexer.next();
                assert!(next.is_none());
            }
        }
    }

    #[test]
    fn test_types() {
        let tt = vec![
            ("true", TokenType::True),
            ("false", TokenType::False),
            ("42", TokenType::Int(42)),
            ("42u", TokenType::Uint(42)),
            ("42.0", TokenType::Double(42.0)),
            ("\"foo\"", TokenType::String),
            ("'foo'", TokenType::String),
            ("b\"foo\"", TokenType::Bytes),
            ("b'foo'", TokenType::Bytes),
            ("null", TokenType::Null),
        ];

        for (t, e) in tt {
            let mut lexer = Lexer::new(t);
            let token = lexer.next().unwrap().unwrap();
            assert_eq!(token.ty, e);
        }
    }

    #[test]
    fn test_dyn() {
        let mut lexer = Lexer::new("dyn(1u)");
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Dyn);
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::LeftParen);
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::Uint(1));
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token.ty, TokenType::RightParen);
    }

    #[test]
    fn test_scan_str() {
        let tripple_delim = [r#"""""#, "'''"];
        let single_delim = ['"', '\''];
        // good cases
        for value in [
            "",
            "foo",
            "foo\\\"bar",
            "foo\\'bar",
            "foo\\nbar",
            "foo\\x00bar",
            "foo\\u0000bar",
            "foo\\U00000000bar",
            "foo\\000bar",
        ] {
            // single delimiter
            for delim in single_delim {
                let input = format!("{}{}{}", delim, value, delim);
                let out = scan_str(&input);
                assert!(out.is_ok(), "input={input:?}, result={out:?}");
                let (end, out) = out.unwrap();
                assert_eq!(end, input.len());
                assert_eq!(out, value);
            }

            // single delimiter missing quote
            for delim in single_delim {
                let input = format!("{delim}{value}");
                let out = scan_str(&input);
                assert!(out.is_err(), "input={input:?}, result={out:?}");
            }

            // tripple delimiter
            for delim in tripple_delim {
                let input = format!("{}{}{}", delim, value, delim);
                let out = scan_str(&input);
                assert!(out.is_ok(), "input={input:?}, result={out:?}");
                let (end, out) = out.unwrap();
                assert_eq!(end, input.len());
                assert_eq!(out, value);
            }

            // tripple delimiter missing quote
            for delim in tripple_delim {
                let bad_delim = &delim[..2];
                let input = format!("{delim}{value}{bad_delim}");
                let out = scan_str(&input);
                assert!(out.is_err(), "input={input:?}, result={out:?}");
            }

            // tripple delimiter with added newlines
            for delim in tripple_delim {
                let input = format!("{}\n{}\n{}", delim, value, delim);
                let out = scan_str(&input);
                assert!(out.is_ok(), "input={input:?}, result={out:?}");
                let (end, out) = out.unwrap();
                assert_eq!(end, input.len());
                assert_eq!(out, format!("\n{value}\n"));
            }
        }

        // catch that the delimiter is not the same
        for (main, other) in [('"', '\''), ('\'', '"')] {
            let input = format!(
                r#"{main}{main}{main}
foo{main}{main}
{main} <- catches that space does not terminate the string
foo{main}{main}{other}{main} <- catches that the delimiter is not the same and proceeds with the next one
{other}{other}{other} <- other delimiter
{main}{main}{main}"#
            );
            let out = scan_str(&input);
            assert!(
                out.is_ok(),
                "main={main:?}, other={other:?}\ninput={input:?}, result={out:?}"
            );
            let (size, literal) = out.unwrap();
            assert_eq!(size, input.len());
            assert_eq!(literal, &input[3..input.len() - 3]);
        }

        // bad escapes
        for value in [
            r#"foo\sbar"#,       // invalid char escape
            r#"foo\xz0zzz"#,     // invalid unicode escape
            r#"foo\u000zzz"#,    // invalid unicode escape
            r#"foo\U000000zzz"#, // invalid unicode escape
            r#"foo\800zzz"#,     // invalid unicode escape
        ] {
            for delim in ['"', '\''] {
                let input = format!("{delim}{value}{delim}");
                let out = scan_str(&input);
                assert!(out.is_err(), "input={input:?}, result={out:?}");
            }

            for delim in [r#"""""#, "'''"] {
                let input = format!("{delim}{value}{delim}");
                let out = scan_str(&input);
                assert!(out.is_err(), "input={input:?}, result={out:?}");
            }

            for delim in [r#"""""#, "'''"] {
                let input = format!("{delim}\n{value}\n{delim}");
                let out = scan_str(&input);
                assert!(out.is_err(), "input={input:?}, result={out:?}");
            }
        }
    }

    #[test]
    fn test_unescape() {
        let input = r#"\n\t\r\"\'"#;
        let out = Token::unescape(input);
        assert_eq!(out, "\n\t\r\"\'");
    }

    #[test]
    fn test_string_span_and_offset() {
        let source = r#"  "line\n" 42"#;
        let mut lexer = Lexer::new(source);

        let string = lexer.next().unwrap().unwrap();
        assert_eq!(string.ty, TokenType::String);
        assert_eq!(string.offset, 2);
        assert_span_slice(source, &string, "\"line\\n\"");
        assert_eq!(string.origin, "line\\n");

        let number = lexer.next().unwrap().unwrap();
        assert!(matches!(number.ty, TokenType::Int(42)));
        let num_start = source.find("42").unwrap();
        assert_eq!(number.offset, num_start);
        assert_span_slice(source, &number, "42");
    }

    #[test]
    fn test_span_len_for_prefixed_literals() {
        let source = r#"foo rb"bar" b"baz" r"qux" 123u"#;
        let mut lexer = Lexer::new(source);

        let ident = lexer.next().unwrap().unwrap();
        assert_eq!(ident.ty, TokenType::Ident);
        assert_span_slice(source, &ident, "foo");

        let raw_bytes = lexer.next().unwrap().unwrap();
        assert_eq!(raw_bytes.ty, TokenType::RawBytes);
        assert_span_slice(source, &raw_bytes, "rb\"bar\"");
        assert_eq!(raw_bytes.origin, "bar");

        let bytes = lexer.next().unwrap().unwrap();
        assert_eq!(bytes.ty, TokenType::Bytes);
        assert_span_slice(source, &bytes, "b\"baz\"");
        assert_eq!(bytes.origin, "baz");

        let raw_string = lexer.next().unwrap().unwrap();
        assert_eq!(raw_string.ty, TokenType::RawString);
        assert_span_slice(source, &raw_string, "r\"qux\"");
        assert_eq!(raw_string.origin, "qux");

        let uint = lexer.next().unwrap().unwrap();
        assert!(matches!(uint.ty, TokenType::Uint(123)));
        assert_span_slice(source, &uint, "123u");
    }
}
