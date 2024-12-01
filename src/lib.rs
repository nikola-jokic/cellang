use chumsky::prelude::*;
use std::collections::BTreeMap;
use std::fmt;

type Span = SimpleSpan;
pub type Spanned<T> = (T, Span);

#[derive(Debug, Clone, PartialEq)]
enum Token<'src> {
    Null,
    Int(i64),
    Uint(u64),
    Double(f64),
    Bool(bool),
    String(&'src str),
    Ident(&'src str),
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Null => write!(f, "null"),
            Token::Int(i) => write!(f, "{}", i),
            Token::Uint(u) => write!(f, "{}", u),
            Token::Double(d) => write!(f, "{}", d),
            Token::Bool(b) => write!(f, "{}", b),
            Token::String(s) => write!(f, "{:?}", s),
            Token::Ident(s) => write!(f, "{}", s),
        }
    }
}

#[derive(Debug)]
enum Value<'src> {
    Null,
    Int(i64),
    Uint(u64),
    Double(f64),
    Bool(bool),
    String(&'src str),
    Bytes(&'src [u8]),
    List(Vec<Self>),
    Map(BTreeMap<MapKey, Value<'src>>),
}

impl fmt::Display for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Null => write!(f, "null"),
            Value::Int(i) => write!(f, "{}", i),
            Value::Uint(u) => write!(f, "{}", u),
            Value::Double(d) => write!(f, "{}", d),
            Value::Bool(b) => write!(f, "{}", b),
            Value::String(s) => write!(f, "{:?}", s),
            Value::Bytes(b) => write!(f, "{:?}", b),
            Value::List(l) => {
                write!(f, "[")?;
                for (i, v) in l.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Value::Map(m) => {
                write!(f, "{{")?;
                for (i, (k, v)) in m.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}: {}", k, v)?;
                }
                write!(f, "}}")
            }
        }
    }
}

#[derive(Debug, PartialEq)]
enum MapKey {
    Int(i64),
    Uint(u64),
    Bool(bool),
    String(String),
}

#[derive(Clone, Debug)]
enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    NotEq,
}

#[derive(Debug)]
enum Expr<'src> {
    Error,
    Value(Value<'src>),
    List(Vec<Spanned<Self>>),
    Call(Box<Spanned<Self>>, Spanned<Vec<Spanned<Self>>>),
}

#[derive(Debug)]
struct Func<'src> {
    args: Vec<&'src str>,
    span: Span,
    body: Spanned<Expr<'src>>,
}

fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char, Span>>> {
    // A parser for strings
    let string = just('"')
        .ignore_then(none_of('"').repeated().to_slice())
        .then_ignore(just('"'))
        .map(Token::String);
}
