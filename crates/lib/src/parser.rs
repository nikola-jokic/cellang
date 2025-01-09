use miette::{Context, Error, LabeledSpan};
use std::borrow::Cow;
use std::fmt;

use crate::lexer::{Token, TokenType};
use crate::Lexer;

/// A parser for the language.
/// This parser is a Pratt parser, which is a top-down operator precedence parser.
/// Produces TokenTree (AST) from the input by using the lexer.
pub struct Parser<'src> {
    input: &'src str,
    lexer: Lexer<'src>,
}

impl<'src> Parser<'src> {
    pub fn new(input: &'src str) -> Self {
        Self {
            input,
            lexer: Lexer::new(input),
        }
    }

    /// Parses the whole input and returns the AST.
    pub fn parse(&mut self) -> Result<TokenTree<'src>, Error> {
        self.parse_expr(0)
    }

    fn parse_expr(&mut self, min_bp: u8) -> Result<TokenTree<'src>, Error> {
        let lhs = match self.lexer.next() {
            Some(Ok(token)) => token,
            None => return Ok(TokenTree::Atom(Atom::Null)), // todo: figure out this
            Some(Err(e)) => return Err(e),
        };

        let mut lhs = match lhs {
            // atoms
            Token {
                ty: TokenType::Ident,
                origin,
                ..
            } => TokenTree::Atom(Atom::Ident(origin)),
            Token {
                ty: TokenType::Int(n),
                ..
            } => TokenTree::Atom(Atom::Int(n)),
            Token {
                ty: TokenType::Uint(n),
                ..
            } => TokenTree::Atom(Atom::Uint(n)),
            Token {
                ty: TokenType::Double(n),
                ..
            } => TokenTree::Atom(Atom::Double(n)),
            Token {
                ty: TokenType::Null,
                ..
            } => TokenTree::Atom(Atom::Null),
            Token {
                ty: TokenType::String,
                origin,
                ..
            } => TokenTree::Atom(Atom::String(Token::unescape(origin))),
            Token {
                ty: TokenType::RawString,
                origin,
                ..
            } => TokenTree::Atom(Atom::String(Token::unescape(origin))),
            Token {
                ty: TokenType::Bytes,
                origin,
                ..
            } => TokenTree::Atom(Atom::Bytes(Token::unescape_bytes(origin))),
            Token {
                ty: TokenType::RawBytes,
                origin,
                ..
            } => TokenTree::Atom(Atom::Bytes(Token::unescape_bytes(origin))),
            Token {
                ty: TokenType::True,
                ..
            } => TokenTree::Atom(Atom::Bool(true)),
            Token {
                ty: TokenType::False,
                ..
            } => TokenTree::Atom(Atom::Bool(false)),

            // dyn
            Token {
                ty: TokenType::Dyn, ..
            } => {
                self.lexer.expect(
                    TokenType::LeftParen,
                    "Expected opening parenthesis after dyn",
                )?;
                let expr = self.parse_expr(0)?;
                self.lexer.expect(
                    TokenType::RightParen,
                    "Expected closing parenthesis after dyn",
                )?;
                TokenTree::Cons(Op::Dyn, vec![expr])
            }

            // groups
            Token {
                ty: TokenType::LeftParen,
                ..
            } => {
                let lhs = self.parse_expr(0)?;
                self.lexer.expect(
                    TokenType::RightParen,
                    "Expected closing parenthesis",
                )?;
                TokenTree::Cons(Op::Group, vec![lhs])
            }

            // unary operators
            Token {
                ty: TokenType::Not | TokenType::Minus,
                ..
            } => {
                let op = match lhs.ty {
                    TokenType::Not => Op::Not,
                    TokenType::Minus => Op::Minus,
                    _ => unreachable!(),
                };
                let ((), r_bp) = prefix_binding_power(op);
                let rhs = self.parse_expr(r_bp)?;
                TokenTree::Cons(op, vec![rhs])
            }

            // aggregate types
            Token {
                ty: TokenType::LeftBrace,
                ..
            } => self.parse_map()?,

            Token {
                ty: TokenType::LeftBracket,
                ..
            } => self.parse_list()?,

            token => {
                return Err(miette::miette! {
                    labels = vec![
                        LabeledSpan::at(
                            token.offset..token.offset + token.origin.len(),
                            "here",
                        ),
                    ],
                        help = format!("Unexpected token: {:?}", token.ty),
                        "Unexpected token"
                })
            }
        };

        loop {
            let op = self.lexer.peek();
            if op.map_or(false, |op| op.is_err()) {
                return Err(self
                    .lexer
                    .next()
                    .expect("checked Some above")
                    .expect_err("checked Err above"))
                .wrap_err("in place of expected operator");
            }

            let op = match op.map(|res| res.as_ref().expect("handled Err above")) {
                None => break,
                Some(Token {
                    ty:
                        TokenType::RightParen
                        | TokenType::RightBracket
                        | TokenType::RightBrace
                        | TokenType::Comma
                        | TokenType::Colon
                        | TokenType::Semicolon,
                    ..
                }) => break,
                Some(Token {
                    ty: TokenType::LeftParen,
                    ..
                }) => Op::Call,
                Some(Token {
                    ty: TokenType::LeftBracket,
                    ..
                }) => Op::Index,
                Some(Token {
                    ty: TokenType::Dot,
                    ..
                }) => Op::Field,
                Some(Token {
                    ty: TokenType::Minus,
                    ..
                }) => Op::Minus,
                Some(Token {
                    ty: TokenType::Plus,
                    ..
                }) => Op::Plus,
                Some(Token {
                    ty: TokenType::Star,
                    ..
                }) => Op::Multiply,
                Some(Token {
                    ty: TokenType::Percent,
                    ..
                }) => Op::Mod,
                Some(Token {
                    ty: TokenType::NotEqual,
                    ..
                }) => Op::NotEqual,
                Some(Token {
                    ty: TokenType::In,
                    ..
                }) => Op::In,
                Some(Token {
                    ty: TokenType::EqualEqual,
                    ..
                }) => Op::EqualEqual,
                Some(Token {
                    ty: TokenType::LessEqual,
                    ..
                }) => Op::LessEqual,
                Some(Token {
                    ty: TokenType::GreaterEqual,
                    ..
                }) => Op::GreaterEqual,
                Some(Token {
                    ty: TokenType::Less,
                    ..
                }) => Op::Less,
                Some(Token {
                    ty: TokenType::Greater,
                    ..
                }) => Op::Greater,
                Some(Token {
                    ty: TokenType::Slash,
                    ..
                }) => Op::Devide,
                Some(Token {
                    ty: TokenType::And,
                    ..
                }) => Op::And,
                Some(Token {
                    ty: TokenType::Or,
                    ..
                }) => Op::Or,
                Some(Token {
                    ty: TokenType::QuestionMark,
                    ..
                }) => Op::IfTernary,

                Some(token) => return Err(miette::miette! {
                    labels = vec![
                        LabeledSpan::at(token.offset..token.offset + token.origin.len(), "here"),
                    ],
                    help = format!("Unexpected {token:?}"),
                    "Expected an infix operator",
                }
                .with_source_code(self.input.to_string())),
            };

            if let Some((l_bp, ())) = postfix_binding_power(op) {
                if l_bp < min_bp {
                    break;
                }
                self.lexer.next();

                lhs = match op {
                    Op::Call => TokenTree::Call {
                        func: Box::new(lhs),
                        args: self
                            .parse_fn_call_args()
                            .wrap_err("in function call arguments")?,
                    },
                    Op::Index => {
                        let index = self
                            .parse_expr(0)
                            .wrap_err("in index expression")?;
                        self.lexer.expect(
                            TokenType::RightBracket,
                            "Expected closing bracket",
                        )?;
                        TokenTree::Cons(op, vec![lhs, index])
                    }
                    _ => TokenTree::Cons(op, vec![lhs]),
                };
                continue;
            }

            if let Some((l_bp, r_bp)) = infix_binding_power(op) {
                if l_bp < min_bp {
                    break;
                }
                self.lexer.next();

                lhs = match op {
                    Op::IfTernary => {
                        let mhs = self.parse_expr(0)?;
                        self.lexer.expect(
                            TokenType::Colon,
                            "Expected colon after the condition",
                        )?;
                        let rhs = self.parse_expr(r_bp)?;
                        TokenTree::Cons(op, vec![lhs, mhs, rhs])
                    }
                    Op::Field => {
                        match self.parse_expr(r_bp).wrap_err_with(|| {
                            format!("on the right-hand side of {lhs} {op}")
                        })? {
                            TokenTree::Call { func, args } => TokenTree::Call {
                                func,
                                args: vec![lhs]
                                    .into_iter()
                                    .chain(args)
                                    .collect(),
                            },
                            rhs => TokenTree::Cons(op, vec![lhs, rhs]),
                        }
                    }
                    _ => {
                        let rhs = self.parse_expr(r_bp)?;
                        TokenTree::Cons(op, vec![lhs, rhs])
                    }
                };

                continue;
            }

            break;
        }

        Ok(lhs)
    }

    fn parse_map(&mut self) -> Result<TokenTree<'src>, Error> {
        let mut items = Vec::new();
        if matches!(
            self.lexer.peek(),
            Some(Ok(Token {
                ty: TokenType::RightBrace,
                ..
            }))
        ) {
            self.lexer.next();
            return Ok(TokenTree::Cons(Op::Map, items));
        }
        loop {
            let key = self.parse_expr(0).wrap_err("in map key")?;
            self.lexer.expect(
                TokenType::Colon,
                "Expected colon between map key and value",
            )?;
            let value = self.parse_expr(0).wrap_err("in map value")?;
            items.push(key);
            items.push(value);

            let token = self
                .lexer
                .expect_where(
                    |token| {
                        matches!(
                            token.ty,
                            TokenType::Comma | TokenType::RightBrace
                        )
                    },
                    "continuing map",
                )
                .wrap_err("in map")?;

            if token.ty == TokenType::RightBrace {
                break;
            }
        }
        Ok(TokenTree::Cons(Op::Map, items))
    }

    fn parse_list(&mut self) -> Result<TokenTree<'src>, Error> {
        let mut items = Vec::new();
        if matches!(
            self.lexer.peek(),
            Some(Ok(Token {
                ty: TokenType::RightBracket,
                ..
            }))
        ) {
            self.lexer.next();
            return Ok(TokenTree::Cons(Op::List, items));
        }
        loop {
            let item = self.parse_expr(0).wrap_err("in list item")?;
            items.push(item);
            let token = self
                .lexer
                .expect_where(
                    |token| {
                        matches!(
                            token.ty,
                            TokenType::Comma | TokenType::RightBracket
                        )
                    },
                    "continuing list",
                )
                .wrap_err("in list")?;

            if token.ty == TokenType::RightBracket {
                break;
            }
        }
        Ok(TokenTree::Cons(Op::List, items))
    }

    fn parse_fn_call_args(&mut self) -> Result<Vec<TokenTree<'src>>, Error> {
        let mut args = Vec::new();

        if !matches!(
            self.lexer.peek(),
            Some(Ok(Token {
                ty: TokenType::RightParen,
                ..
            }))
        ) {
            loop {
                let arg = self.parse_expr(0).wrap_err_with(|| {
                    format!("in argument #{} of function call", args.len() + 1)
                })?;
                args.push(arg);
                let token = self
                    .lexer
                    .expect_where(
                        |token| {
                            matches!(
                                token.ty,
                                TokenType::Comma | TokenType::RightParen
                            )
                        },
                        "continuing argument list",
                    )
                    .wrap_err("in argument list of function call")?;

                if token.ty == TokenType::RightParen {
                    break;
                }
            }
        } else {
            self.lexer.next();
        }
        Ok(args)
    }
}

/// An atomic value in the AST.
/// This is the smallest unit of the AST.
#[derive(Debug, Clone, PartialEq)]
pub enum Atom<'src> {
    Bool(bool),
    Int(i64),
    Uint(u64),
    Double(f64),
    String(Cow<'src, str>),
    Bytes(Cow<'src, [u8]>),
    Ident(&'src str),
    Null,
}

impl fmt::Display for Atom<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Atom::Bool(b) => write!(f, "{b:?}"),
            Atom::Int(i) => write!(f, "{}", i),
            Atom::Uint(u) => write!(f, "{}", u),
            Atom::Double(d) => write!(f, "{}", d),
            Atom::String(s) => write!(f, "{:?}", s),
            Atom::Bytes(b) => write!(f, "{:?}", b),
            Atom::Ident(i) => write!(f, "{}", i),
            Atom::Null => write!(f, "null"),
        }
    }
}

/// An operator in the AST.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Op {
    Minus,
    Plus,
    Multiply,
    Devide,
    Mod,
    NotEqual,
    EqualEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Not,
    And,
    Or,
    IfTernary,
    In,
    Call,
    Index,
    For,
    Field,
    While,
    Var,
    Group,
    Map,
    List,
    Dyn,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Op::IfTernary => "?:",
            Op::Minus => "-",
            Op::Plus => "+",
            Op::Multiply => "*",
            Op::NotEqual => "!=",
            Op::EqualEqual => "==",
            Op::LessEqual => "<=",
            Op::GreaterEqual => ">=",
            Op::Less => "<",
            Op::Greater => ">",
            Op::Index => "[]",
            Op::Var => "var",
            Op::In => "in",
            Op::Devide => "/",
            Op::Not => "!",
            Op::And => "&&",
            Op::Or => "||",
            Op::Call => "(args)",
            Op::For => "for",
            Op::Field => ".",
            Op::While => "while",
            Op::Group => "(",
            Op::Map => "{map}",
            Op::List => "[list]",
            Op::Mod => "%",
            Op::Dyn => "dyn",
        };
        write!(f, "{}", s)
    }
}

/// A node in the AST.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenTree<'src> {
    Atom(Atom<'src>),
    Cons(Op, Vec<TokenTree<'src>>),
    Call {
        func: Box<TokenTree<'src>>,
        args: Vec<TokenTree<'src>>,
    },
}

impl fmt::Display for TokenTree<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenTree::Atom(atom) => write!(f, "{}", atom),
            TokenTree::Cons(op, args) => {
                write!(f, "{}", op)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                Ok(())
            }
            TokenTree::Call { func, args } => {
                write!(f, "{}(", func)?;
                for arg in args {
                    write!(f, ", {}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

fn prefix_binding_power(op: Op) -> ((), u8) {
    match op {
        Op::Minus | Op::Not => ((), 13),
        _ => panic!("Unexpected operator: {:?}", op),
    }
}

fn postfix_binding_power(op: Op) -> Option<(u8, ())> {
    match op {
        Op::Call | Op::Index => Some((15, ())),
        _ => None,
    }
}

// Precedence levels for infix operators.
// ?: - 1,2
// || - 3,4
// && - 5,6
// in - 7,8
// == != <><=>= - 7,8
// -(binary) +(binary) - 9,10
// * / % - 11,12
// ! -(unary) - 13,14
// () . [] {} - 15,16

/// Returns the binding powers for the given infix operator.
fn infix_binding_power(op: Op) -> Option<(u8, u8)> {
    let res = match op {
        // '=' => (2, 1),
        Op::IfTernary => (2, 1),
        Op::Or => (3, 4),
        Op::And => (5, 6),
        Op::In
        | Op::NotEqual
        | Op::EqualEqual
        | Op::Less
        | Op::LessEqual
        | Op::Greater
        | Op::GreaterEqual => (7, 8),
        Op::Plus | Op::Minus => (9, 10),
        Op::Multiply | Op::Devide | Op::Mod => (11, 12),
        Op::Field | Op::Call => (16, 15),
        _ => return None,
    };
    Some(res)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_and_multiply() {
        let input = "1 + 2 * 3";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Plus,
                vec![
                    TokenTree::Atom(Atom::Int(1)),
                    TokenTree::Cons(
                        Op::Multiply,
                        vec![
                            TokenTree::Atom(Atom::Int(2)),
                            TokenTree::Atom(Atom::Int(3)),
                        ]
                    )
                ]
            )
        );
    }

    #[test]
    fn test_field_access() {
        let input = "foo.bar.baz";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Field,
                vec![
                    TokenTree::Atom(Atom::Ident("foo")),
                    TokenTree::Cons(
                        Op::Field,
                        vec![
                            TokenTree::Atom(Atom::Ident("bar")),
                            TokenTree::Atom(Atom::Ident("baz")),
                        ]
                    )
                ]
            )
        );

        let input = "foo.check['bar'].baz";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Field,
                vec![
                    TokenTree::Atom(Atom::Ident("foo")),
                    TokenTree::Cons(
                        Op::Field,
                        vec![
                            TokenTree::Cons(
                                Op::Index,
                                vec![
                                    TokenTree::Atom(Atom::Ident("check")),
                                    TokenTree::Atom(Atom::String(
                                        Cow::Borrowed("bar")
                                    )),
                                ]
                            ),
                            TokenTree::Atom(Atom::Ident("baz")),
                        ]
                    )
                ]
            )
        );
    }

    #[test]
    fn test_function_call() {
        let input = "foo(bar, baz)";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Call {
                func: Box::new(TokenTree::Atom(Atom::Ident("foo"))),
                args: vec![
                    TokenTree::Atom(Atom::Ident("bar")),
                    TokenTree::Atom(Atom::Ident("baz")),
                ]
            }
        );

        let input = "foo([])";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Call {
                func: Box::new(TokenTree::Atom(Atom::Ident("foo"))),
                args: vec![TokenTree::Cons(Op::List, vec![])]
            }
        );

        let input = "foo({})";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Call {
                func: Box::new(TokenTree::Atom(Atom::Ident("foo"))),
                args: vec![TokenTree::Cons(Op::Map, vec![])]
            }
        );
    }

    #[test]
    fn test_method_call() {
        let input = "foo.bar(baz)";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Call {
                func: Box::new(TokenTree::Atom(Atom::Ident("bar"))),
                args: vec![
                    TokenTree::Atom(Atom::Ident("foo")),
                    TokenTree::Atom(Atom::Ident("baz")),
                ]
            }
        );
    }

    #[test]
    fn test_nested_method_call() {
        let input = "foo.all(test, test.size() > 4)";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        let want = TokenTree::Call {
            func: Box::new(TokenTree::Atom(Atom::Ident("all"))),
            args: vec![
                TokenTree::Atom(Atom::Ident("foo")),
                TokenTree::Atom(Atom::Ident("test")),
                TokenTree::Cons(
                    Op::Greater,
                    vec![
                        TokenTree::Call {
                            func: Box::new(TokenTree::Atom(Atom::Ident(
                                "size",
                            ))),
                            args: vec![TokenTree::Atom(Atom::Ident("test"))],
                        },
                        TokenTree::Atom(Atom::Int(4)),
                    ],
                ),
            ],
        };
        assert_eq!(tree, want, "expected {want:?}, got {tree:?}");
    }

    #[test]
    fn test_list_definition() {
        let input = "[1, 2, 3]";
        let mut parser = Parser::new(input);
        let tree = parser.parse();
        assert!(tree.is_ok(), "{:?}", tree);
        let tree = tree.unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::List,
                vec![
                    TokenTree::Atom(Atom::Int(1)),
                    TokenTree::Atom(Atom::Int(2)),
                    TokenTree::Atom(Atom::Int(3)),
                ]
            )
        );

        let input = "[]";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(tree, TokenTree::Cons(Op::List, vec![]));
    }

    #[test]
    fn test_map_definition() {
        let input = "{foo: 1, bar: 2}";
        let mut parser = Parser::new(input);
        let tree = parser.parse();
        assert!(tree.is_ok(), "{:?}", tree);
        let tree = tree.unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Map,
                vec![
                    TokenTree::Atom(Atom::Ident("foo")),
                    TokenTree::Atom(Atom::Int(1)),
                    TokenTree::Atom(Atom::Ident("bar")),
                    TokenTree::Atom(Atom::Int(2)),
                ]
            )
        );

        let input = "{}";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(tree, TokenTree::Cons(Op::Map, vec![]));
    }

    #[test]
    fn test_grouping() {
        let input = "(1 + 2) * 3 % 4";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Mod,
                vec![
                    TokenTree::Cons(
                        Op::Multiply,
                        vec![
                            TokenTree::Cons(
                                Op::Group,
                                vec![TokenTree::Cons(
                                    Op::Plus,
                                    vec![
                                        TokenTree::Atom(Atom::Int(1)),
                                        TokenTree::Atom(Atom::Int(2)),
                                    ]
                                ),]
                            ),
                            TokenTree::Atom(Atom::Int(3)),
                        ]
                    ),
                    TokenTree::Atom(Atom::Int(4)),
                ]
            )
        );
    }

    #[test]
    fn test_unary_minus() {
        let input = "-1";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(Op::Minus, vec![TokenTree::Atom(Atom::Int(1))])
        );
    }

    #[test]
    fn test_unary_not() {
        let input = "!true";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(Op::Not, vec![TokenTree::Atom(Atom::Bool(true))])
        );
    }

    #[test]
    fn test_relations() {
        let input = "1 < 2 && 3 >= 4 || 5 == 6 && 5 in 6";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Or,
                vec![
                    TokenTree::Cons(
                        Op::And,
                        vec![
                            TokenTree::Cons(
                                Op::Less,
                                vec![
                                    TokenTree::Atom(Atom::Int(1)),
                                    TokenTree::Atom(Atom::Int(2)),
                                ]
                            ),
                            TokenTree::Cons(
                                Op::GreaterEqual,
                                vec![
                                    TokenTree::Atom(Atom::Int(3)),
                                    TokenTree::Atom(Atom::Int(4)),
                                ]
                            ),
                        ]
                    ),
                    TokenTree::Cons(
                        Op::And,
                        vec![
                            TokenTree::Cons(
                                Op::EqualEqual,
                                vec![
                                    TokenTree::Atom(Atom::Int(5)),
                                    TokenTree::Atom(Atom::Int(6)),
                                ]
                            ),
                            TokenTree::Cons(
                                Op::In,
                                vec![
                                    TokenTree::Atom(Atom::Int(5)),
                                    TokenTree::Atom(Atom::Int(6)),
                                ]
                            ),
                        ]
                    ),
                ]
            )
        );
    }

    #[test]
    fn test_singuler_expression() {
        let tt = vec![
            ("identifier", TokenTree::Atom(Atom::Ident("identifier"))),
            ("123", TokenTree::Atom(Atom::Int(123))),
            ("123u", TokenTree::Atom(Atom::Uint(123))),
            ("123.456", TokenTree::Atom(Atom::Double(123.456))),
            ("true", TokenTree::Atom(Atom::Bool(true))),
            ("false", TokenTree::Atom(Atom::Bool(false))),
            (
                "\"string\"",
                TokenTree::Atom(Atom::String(Cow::Borrowed("string"))),
            ),
            ("null", TokenTree::Atom(Atom::Null)),
        ]
        .into_iter();

        for (input, expected) in tt {
            let mut parser = Parser::new(input);
            let tree = parser.parse();
            assert!(tree.is_ok(), "input={:?}, out={:?}", input, tree);
            let tree = tree.unwrap();
            assert_eq!(tree, expected);
        }
    }

    #[test]
    fn test_indexing() {
        let input = "foo[1]";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Index,
                vec![
                    TokenTree::Atom(Atom::Ident("foo")),
                    TokenTree::Atom(Atom::Int(1)),
                ]
            )
        );

        let input = "foo[1][2]";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Index,
                vec![
                    TokenTree::Cons(
                        Op::Index,
                        vec![
                            TokenTree::Atom(Atom::Ident("foo")),
                            TokenTree::Atom(Atom::Int(1)),
                        ]
                    ),
                    TokenTree::Atom(Atom::Int(2)),
                ]
            )
        );
    }

    #[test]
    fn test_ternary_if() {
        let input = "true ? 1 : 2";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::IfTernary,
                vec![
                    TokenTree::Atom(Atom::Bool(true)),
                    TokenTree::Atom(Atom::Int(1)),
                    TokenTree::Atom(Atom::Int(2)),
                ]
            )
        );

        let input = "true ? 1 : false ? 2 : 3";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::IfTernary,
                vec![
                    TokenTree::Atom(Atom::Bool(true)),
                    TokenTree::Atom(Atom::Int(1)),
                    TokenTree::Cons(
                        Op::IfTernary,
                        vec![
                            TokenTree::Atom(Atom::Bool(false)),
                            TokenTree::Atom(Atom::Int(2)),
                            TokenTree::Atom(Atom::Int(3)),
                        ]
                    ),
                ]
            )
        );
    }

    #[test]
    fn test_method_relation() {
        let input = "foo.bar() < 4";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Less,
                vec![
                    TokenTree::Call {
                        func: Box::new(TokenTree::Atom(Atom::Ident("bar"))),
                        args: vec![TokenTree::Atom(Atom::Ident("foo"))],
                    },
                    TokenTree::Atom(Atom::Int(4)),
                ]
            )
        );
    }

    #[test]
    fn test_inline_function_call() {
        let input = "1 + size(2u)";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Plus,
                vec![
                    TokenTree::Atom(Atom::Int(1)),
                    TokenTree::Call {
                        func: Box::new(TokenTree::Atom(Atom::Ident("size"))),
                        args: vec![TokenTree::Atom(Atom::Uint(2))],
                    },
                ]
            )
        );
    }

    #[test]
    fn test_inline_dyn_call() {
        let input = "1 + dyn(2u)";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::Plus,
                vec![
                    TokenTree::Atom(Atom::Int(1)),
                    TokenTree::Cons(
                        Op::Dyn,
                        vec![TokenTree::Atom(Atom::Uint(2))],
                    ),
                ]
            )
        );
    }

    #[test]
    fn test_nested_list_with_map() {
        let input = "[{foo: 1}, {bar: 2}]";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();
        assert_eq!(
            tree,
            TokenTree::Cons(
                Op::List,
                vec![
                    TokenTree::Cons(
                        Op::Map,
                        vec![
                            TokenTree::Atom(Atom::Ident("foo")),
                            TokenTree::Atom(Atom::Int(1)),
                        ]
                    ),
                    TokenTree::Cons(
                        Op::Map,
                        vec![
                            TokenTree::Atom(Atom::Ident("bar")),
                            TokenTree::Atom(Atom::Int(2)),
                        ]
                    ),
                ]
            )
        );
    }

    #[test]
    fn test_method_call_with_indexing() {
        let input = "foo.bar(x, t[x] > 10)";
        let mut parser = Parser::new(input);
        let tree = parser.parse().unwrap();

        let want = TokenTree::Call {
            func: Box::new(TokenTree::Atom(Atom::Ident("bar"))),
            args: vec![
                TokenTree::Atom(Atom::Ident("foo")),
                TokenTree::Atom(Atom::Ident("x")),
                TokenTree::Cons(
                    Op::Greater,
                    vec![
                        TokenTree::Cons(
                            Op::Index,
                            vec![
                                TokenTree::Atom(Atom::Ident("t")),
                                TokenTree::Atom(Atom::Ident("x")),
                            ],
                        ),
                        TokenTree::Atom(Atom::Int(10)),
                    ],
                ),
            ],
        };

        assert_eq!(tree, want);
    }
}
