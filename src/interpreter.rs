use std::borrow::Cow;

use crate::{
    parser::{Atom, Op, TokenTree},
    Lexer, Parser,
};

pub struct Interpreter {}

impl Interpreter {
    pub fn eval(&self, program: &str) -> Value {
        let tree = Parser::new(program)
            .parse()
            .expect("Failed to parse program");
        self.eval_ast(&tree)
    }

    fn eval_ast(&self, root: &TokenTree) -> Value {
        match root {
            TokenTree::Atom(atom) => self.eval_atom(atom),
            TokenTree::Cons(op, tokens) => self.eval_cons(op, tokens),
            _ => unimplemented!(),
        }
    }

    fn eval_atom(&self, atom: &Atom) -> Value {
        match atom {
            Atom::Int(n) => Value::Int(*n),
            Atom::Uint(n) => Value::Uint(*n),
            Atom::Double(n) => Value::Double(*n),
            Atom::String(s) => Value::String(s.to_string()),
            Atom::Bool(b) => Value::Bool(*b),
            Atom::Null => Value::Null,
            _ => unimplemented!(),
        }
    }

    fn eval_cons(&self, op: &Op, tokens: &[TokenTree]) -> Value {
        match op {
            Op::Plus => {
                let lhs = self.eval_ast(&tokens[0]);
                let rhs = self.eval_ast(&tokens[1]);
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs + rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs + rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs + rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Minus => {
                let lhs = self.eval_ast(&tokens[0]);
                let rhs = self.eval_ast(&tokens[1]);
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs - rhs),
                    _ => unimplemented!(),
                }
            }
            _ => unimplemented!(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Int(i64),
    Uint(u64),
    Double(f64),
    String(String),
    Bool(bool),
    Null,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_primitives() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("42"), Value::Int(42));
        assert_eq!(interpreter.eval("true"), Value::Bool(true));
        assert_eq!(interpreter.eval("false"), Value::Bool(false));
        assert_eq!(interpreter.eval("null"), Value::Null);
        assert_eq!(
            interpreter.eval("\"hello\""),
            Value::String("hello".to_string())
        );
    }

    #[test]
    fn test_eval_plus() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("1 + 2"), Value::Int(3));
        assert_eq!(interpreter.eval("1u + 2u"), Value::Uint(3));
        assert_eq!(interpreter.eval("1.0 + 2.0"), Value::Double(3.0));
    }
}
