use miette::Error;
use std::collections::HashMap;

use crate::{
    parser::{Atom, Op, TokenTree},
    Parser,
};

pub struct Interpreter {}

impl Interpreter {
    pub fn eval(&self, program: &str) -> Result<Value, Error> {
        let tree = Parser::new(program).parse()?;
        self.eval_ast(&tree)
    }

    fn eval_ast(&self, root: &TokenTree) -> Result<Value, Error> {
        match root {
            TokenTree::Atom(atom) => self.eval_atom(atom),
            TokenTree::Cons(op, tokens) => self.eval_cons(op, tokens),
            _ => unimplemented!(),
        }
    }

    fn eval_atom(&self, atom: &Atom) -> Result<Value, Error> {
        let val = match atom {
            Atom::Int(n) => Value::Int(*n),
            Atom::Uint(n) => Value::Uint(*n),
            Atom::Double(n) => Value::Double(*n),
            Atom::String(s) => Value::String(s.to_string()),
            Atom::Bool(b) => Value::Bool(*b),
            Atom::Null => Value::Null,
            Atom::Bytes(b) => Value::Bytes(b.clone().to_vec()),
            _ => unimplemented!(),
        };
        Ok(val)
    }

    fn eval_cons(&self, op: &Op, tokens: &[TokenTree]) -> Result<Value, Error> {
        let val = match op {
            Op::Not => {
                let lhs = self.eval_ast(&tokens[0])?;
                match lhs {
                    Value::Bool(lhs) => Value::Bool(!lhs),
                    _ => miette::bail!("Expected bool, found {:?}", lhs),
                }
            }
            Op::Plus => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs + rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs + rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs + rhs),
                    (Value::String(s1), Value::String(s2)) => {
                        Value::String(format!("{}{}", s1, s2))
                    }
                    _ => unimplemented!(),
                }
            }
            Op::Minus => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs - rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs - rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs - rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Multiply => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs * rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs * rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs * rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Devide => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs / rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs / rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs / rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Mod => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs % rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs % rhs),
                    _ => unimplemented!(),
                }
            }
            Op::And => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs && rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Or => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    // short-circuit evaluation
                    (Value::Bool(true), _) => Value::Bool(true),
                    (_, Value::Bool(true)) => Value::Bool(true),
                    // normal evaluation
                    (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs || rhs),
                    _ => unimplemented!(),
                }
            }
            Op::EqualEqual => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs == rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs == rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs == rhs),
                    (Value::String(lhs), Value::String(rhs)) => Value::Bool(lhs == rhs),
                    (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs == rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Greater => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs > rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs > rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs > rhs),
                    _ => unimplemented!(),
                }
            }
            Op::GreaterEqual => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs >= rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs >= rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs >= rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Less => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs < rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs < rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs < rhs),
                    _ => unimplemented!(),
                }
            }
            Op::LessEqual => {
                let lhs = self.eval_ast(&tokens[0])?;
                let rhs = self.eval_ast(&tokens[1])?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs <= rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs <= rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs <= rhs),
                    _ => unimplemented!(),
                }
            }
            Op::List => {
                if tokens.is_empty() {
                    return Ok(Value::List(vec![]));
                }

                let mut list = Vec::with_capacity(tokens.len());
                let mut iter = tokens.iter();
                let first = self.eval_ast(iter.next().unwrap())?;
                let kind = first.kind();
                list.push(first);

                for token in iter {
                    let value = self.eval_ast(token)?;
                    if value.kind() != kind {
                        miette::bail!("List elements must have the same type");
                    }
                    list.push(value);
                }

                Value::List(list)
            }
            Op::Map => {
                if tokens.is_empty() {
                    return Ok(Value::Map(HashMap::new()));
                }

                let mut iter = tokens.iter();
                let first_key = self.eval_ast(iter.next().expect("Key must be present"))?;
                let first_value = self.eval_ast(iter.next().expect("Value must be present"))?;
                let key_kind = first_key.kind();
                let value_kind = first_value.kind();

                let mut map = HashMap::new();
                map.insert(MapKey::try_from(first_key)?, first_value);

                while let (Some(key), Some(value)) = (iter.next(), iter.next()) {
                    let key = self.eval_ast(key)?;
                    let value = self.eval_ast(value)?;
                    if key.kind() != key_kind || value.kind() != value_kind {
                        miette::bail!("Map elements must have the same type");
                    }
                    map.insert(MapKey::try_from(key)?, value);
                }

                Value::Map(map)
            }
            _ => unimplemented!(),
        };
        Ok(val)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Int(i64),
    Uint(u64),
    Double(f64),
    String(String),
    Bool(bool),
    Map(HashMap<MapKey, Value>),
    List(Vec<Value>),
    Bytes(Vec<u8>),
    Null,
}

impl Value {
    fn kind(&self) -> ValueKind {
        match self {
            Value::Int(_) => ValueKind::Int,
            Value::Uint(_) => ValueKind::Uint,
            Value::Double(_) => ValueKind::Double,
            Value::String(_) => ValueKind::String,
            Value::Bool(_) => ValueKind::Bool,
            Value::Map(_) => ValueKind::Map,
            Value::List(_) => ValueKind::List,
            Value::Bytes(_) => ValueKind::Bytes,
            Value::Null => ValueKind::Null,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum ValueKind {
    Int,
    Uint,
    Double,
    String,
    Bool,
    Map,
    List,
    Bytes,
    Null,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum MapKey {
    Int(i64),
    Uint(u64),
    String(String),
    Bool(bool),
}

impl TryFrom<Value> for MapKey {
    type Error = Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Int(n) => Ok(MapKey::Int(n)),
            Value::Uint(n) => Ok(MapKey::Uint(n)),
            Value::String(s) => Ok(MapKey::String(s)),
            Value::Bool(b) => Ok(MapKey::Bool(b)),
            _ => miette::bail!("Invalid map key: {:?}", value),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_primitives() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("42").expect("42"), Value::Int(42));
        assert_eq!(interpreter.eval("true").expect("true"), Value::Bool(true));
        assert_eq!(
            interpreter.eval("false").expect("false"),
            Value::Bool(false)
        );
        assert_eq!(interpreter.eval("null").expect("null"), Value::Null);
        assert_eq!(
            interpreter.eval("\"hello\"").expect("hello"),
            Value::String("hello".to_string())
        );
    }

    #[test]
    fn test_eval_plus() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("1 + 2").expect("1 + 2"), Value::Int(3));
        assert_eq!(
            interpreter.eval("1u + 2u").expect("1u + 2u"),
            Value::Uint(3)
        );
        assert_eq!(
            interpreter.eval("1.0 + 2.0").expect("1.0 + 2.0"),
            Value::Double(3.0)
        );
        assert_eq!(
            interpreter
                .eval("\"hello\" + \"world\"")
                .expect("\"hello\" + \"world\""),
            Value::String("helloworld".to_string())
        );
    }

    #[test]
    fn test_eval_minus() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("1 - 2").expect("1 - 2"), Value::Int(-1));
        assert_eq!(
            interpreter.eval("2u - 1u").expect("2u - 1u"),
            Value::Uint(1)
        );
        assert_eq!(
            interpreter.eval("1.0 - 2.0").expect("1.0 - 2.0"),
            Value::Double(-1.0)
        );
    }

    #[test]
    fn test_eval_multiply() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("2 * 3").expect("2 * 3"), Value::Int(6));
        assert_eq!(
            interpreter.eval("2u * 3u").expect("2u * 3u"),
            Value::Uint(6)
        );
        assert_eq!(
            interpreter.eval("2.0 * 3.0").expect("2.0 * 3.0"),
            Value::Double(6.0)
        );
    }

    #[test]
    fn test_eval_devide() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("6 / 3").expect("6 / 3"), Value::Int(2));
        assert_eq!(
            interpreter.eval("6u / 3u").expect("6u / 3u"),
            Value::Uint(2)
        );
        assert_eq!(
            interpreter.eval("6.0 / 3.0").expect("6.0 / 3.0"),
            Value::Double(2.0)
        );
    }

    #[test]
    fn test_eval_and() {
        let interpreter = Interpreter {};
        assert_eq!(
            interpreter.eval("true && false").expect("true && false"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("true && true").expect("true && true"),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_or() {
        let interpreter = Interpreter {};
        assert_eq!(
            interpreter.eval("false || true").expect("false || true"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("false || false").expect("false || false"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_eval_equal_equal() {
        let interpreter = Interpreter {};
        assert_eq!(
            interpreter.eval("1 == 1").expect("1 == 1"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1 == 2").expect("1 == 2"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1u == 1u").expect("1u == 1u"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1u == 2u").expect("1u == 2u"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1.0 == 1.0").expect("1.0 == 1.0"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1.0 == 2.0").expect("1.0 == 2.0"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("true == true").expect("true == true"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("true == false").expect("true == false"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter
                .eval("\"hello\" == \"hello\"")
                .expect("\"hello\" == \"hello\""),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter
                .eval("\"hello\" == \"world\"")
                .expect("\"hello\" == \"world\""),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_eval_greater() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("2 > 1").expect("2 > 1"), Value::Bool(true));
        assert_eq!(
            interpreter.eval("1 > 2").expect("1 > 2"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("2u > 1u").expect("2u > 1u"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1u > 2u").expect("1u > 2u"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("2.0 > 1.0").expect("2.0 > 1.0"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1.0 > 2.0").expect("1.0 > 2.0"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_eval_greater_equal() {
        let interpreter = Interpreter {};
        assert_eq!(
            interpreter.eval("2 >= 1").expect("2 >= 1"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1 >= 2").expect("1 >= 2"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1 >= 1").expect("1 >= 1"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("2u >= 1u").expect("2u >= 1u"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1u >= 2u").expect("1u >= 2u"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1u >= 1u").expect("1u >= 1u"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("2.0 >= 1.0").expect("2.0 >= 1.0"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1.0 >= 2.0").expect("1.0 >= 2.0"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1.0 >= 1.0").expect("1.0 >= 1.0"),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_less() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("1 < 2").expect("1 < 2"), Value::Bool(true));
        assert_eq!(
            interpreter.eval("2 < 1").expect("2 < 1"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1u < 2u").expect("1u < 2u"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("2u < 1u").expect("2u < 1u"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1.0 < 2.0").expect("1.0 < 2.0"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("2.0 < 1.0").expect("2.0 < 1.0"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_eval_less_equal() {
        let interpreter = Interpreter {};
        assert_eq!(
            interpreter.eval("1 <= 2").expect("1 <= 2"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("2 <= 1").expect("2 <= 1"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1 <= 1").expect("1 <= 1"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1u <= 2u").expect("1u <= 2u"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("2u <= 1u").expect("2u <= 1u"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1u <= 1u").expect("1u <= 1u"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1.0 <= 2.0").expect("1.0 <= 2.0"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("2.0 <= 1.0").expect("2.0 <= 1.0"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1.0 <= 1.0").expect("1.0 <= 1.0"),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_mod() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("5 % 2").expect("5 % 2"), Value::Int(1));
        assert_eq!(
            interpreter.eval("5u % 2u").expect("5u % 2u"),
            Value::Uint(1)
        );
    }

    #[test]
    fn test_eval_not() {
        let interpreter = Interpreter {};
        assert_eq!(
            interpreter.eval("!true").expect("!true"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("!false").expect("!false"),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_list() {
        let interpreter = Interpreter {};
        assert_eq!(interpreter.eval("[]").expect("[]"), Value::List(vec![]));
        assert_eq!(
            interpreter.eval("[1, 2, 3]").expect("[1, 2, 3]"),
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
        );
        assert_eq!(
            interpreter.eval("[1u, 2u, 3u]").expect("[1u, 2u, 3u]"),
            Value::List(vec![Value::Uint(1), Value::Uint(2), Value::Uint(3)])
        );
        assert_eq!(
            interpreter
                .eval("[1.0, 2.0, 3.0]")
                .expect("[1.0, 2.0, 3.0]"),
            Value::List(vec![
                Value::Double(1.0),
                Value::Double(2.0),
                Value::Double(3.0)
            ])
        );
        assert_eq!(
            interpreter
                .eval("[\"hello\", \"world\"]")
                .expect("[\"hello\", \"world\"]"),
            Value::List(vec![
                Value::String("hello".to_string()),
                Value::String("world".to_string())
            ])
        );
        assert_eq!(
            interpreter.eval("[true, false]").expect("[true, false]"),
            Value::List(vec![Value::Bool(true), Value::Bool(false)])
        );

        // list elements must have the same type
        let tt = [
            "[1, 2u, 3]",
            "[1, 2.0, 3]",
            "[1, \"hello\", 3]",
            "[1, true, 3]",
        ];
        for t in tt.iter() {
            let result = interpreter.eval(t);
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_map() {
        let tt = [
            ("{}", Value::Map(HashMap::new())),
            ("{1: 2, 3: 4}", {
                let mut map = HashMap::new();
                map.insert(MapKey::Int(1), Value::Int(2));
                map.insert(MapKey::Int(3), Value::Int(4));
                Value::Map(map)
            }),
            ("{1u: 2u, 3u: 4u}", {
                let mut map = HashMap::new();
                map.insert(MapKey::Uint(1), Value::Uint(2));
                map.insert(MapKey::Uint(3), Value::Uint(4));
                Value::Map(map)
            }),
            ("{\"hello\": \"world\"}", {
                let mut map = HashMap::new();
                map.insert(
                    MapKey::String("hello".to_string()),
                    Value::String("world".to_string()),
                );
                Value::Map(map)
            }),
            ("{true: false}", {
                let mut map = HashMap::new();
                map.insert(MapKey::Bool(true), Value::Bool(false));
                Value::Map(map)
            }),
        ];

        let interpreter = Interpreter {};
        for (input, expected) in tt.iter() {
            let result = interpreter.eval(input).expect(input);
            assert_eq!(result, *expected, "input: {}", input);
        }

        let tt = [
            ("{1: 2, 3u: 4}", "Map elements must have the same type"),
            ("{1: 2, 3: 4u}", "Map elements must have the same type"),
            (
                "{1: 2, 3: \"hello\"}",
                "Map elements must have the same type",
            ),
            ("{1: 2, 3: true}", "Map elements must have the same type"),
        ];

        for (input, expected) in tt.iter() {
            let result = interpreter.eval(input);
            assert!(result.is_err());
            assert_eq!(result.unwrap_err().to_string(), *expected);
        }
    }
}
