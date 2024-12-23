use miette::Error;
use std::collections::HashMap;

use crate::{
    parser::{Atom, Op, TokenTree},
    Parser,
};

type Function = Box<dyn Fn(&[Value]) -> Result<Value, Error>>;

pub struct Environment {
    variables: HashMap<String, Value>,
    functions: HashMap<String, Function>,
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

impl Environment {
    pub fn new() -> Self {
        Self {
            variables: HashMap::new(),
            functions: {
                let mut m = HashMap::new();
                m.insert("size".to_string(), Box::new(fn_size) as Function);
                m.insert("type".to_string(), Box::new(fn_type) as Function);
                m
            },
        }
    }

    pub fn get_variable(&self, name: &str) -> Option<&Value> {
        self.variables.get(name)
    }

    pub fn set_variable(&mut self, name: &str, value: Value) {
        self.variables.insert(name.to_string(), value);
    }

    pub fn get_function(&self, name: &str) -> Option<&Function> {
        self.functions.get(name)
    }

    pub fn set_function(&mut self, name: &str, function: Function) {
        self.functions.insert(name.to_string(), function);
    }
}

pub struct Interpreter<'a> {
    env: &'a Environment,
}

impl<'a> Interpreter<'a> {
    pub fn new(env: &'a Environment) -> Self {
        Self { env }
    }

    pub fn eval(&self, program: &str) -> Result<Value, Error> {
        let tree = Parser::new(program).parse()?;
        match self.eval_ast(&tree) {
            Ok(Object::Value(val)) => Ok(val),
            Ok(Object::Reference(ident)) => {
                if let Some(val) = self.env.get_variable(&ident) {
                    Ok(val.clone())
                } else {
                    miette::bail!("Variable not found: {}", ident);
                }
            }
            Err(e) => Err(e),
        }
    }

    fn eval_ast(&self, root: &TokenTree) -> Result<Object, Error> {
        match root {
            TokenTree::Atom(atom) => self.eval_atom(atom),
            TokenTree::Cons(op, tokens) => Ok(Object::Value(self.eval_cons(op, tokens)?)),
            TokenTree::Call { func, args } => {
                let f = match self.eval_ast(func)? {
                    Object::Reference(name) => match self.env.get_function(&name) {
                        Some(f) => f,
                        None => miette::bail!("Function not found: {}", name),
                    },
                    _ => miette::bail!("Expected function name, found {:?}", func),
                };
                let args = args
                    .iter()
                    .map(|arg| self.eval_ast(arg)?.value(self.env))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Object::Value(f(&args)?))
            }
        }
    }

    fn eval_atom(&self, atom: &Atom) -> Result<Object, Error> {
        let val = match atom {
            Atom::Int(n) => Object::Value(Value::Int(*n)),
            Atom::Uint(n) => Object::Value(Value::Uint(*n)),
            Atom::Double(n) => Object::Value(Value::Double(*n)),
            Atom::String(s) => Object::Value(Value::String(s.to_string())),
            Atom::Bool(b) => Object::Value(Value::Bool(*b)),
            Atom::Null => Object::Value(Value::Null),
            Atom::Bytes(b) => Object::Value(Value::Bytes(b.clone().to_vec())),
            Atom::Ident(ident) => Object::Reference(ident.to_string()),
        };
        Ok(val)
    }

    fn eval_cons(&self, op: &Op, tokens: &[TokenTree]) -> Result<Value, Error> {
        let val = match op {
            Op::Field => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?;

                dbg!(lhs, rhs);

                todo!();
            }
            Op::Not => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                match lhs {
                    Value::Bool(b) => Value::Bool(!b),
                    _ => miette::bail!("Expected bool, found {:?}", tokens[0]),
                }
            }
            Op::Plus => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs + rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs + rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs + rhs),
                    (Value::String(s1), Value::String(s2)) => {
                        Value::String(format!("{}{}", s1, s2))
                    }
                    (Value::Bytes(b1), Value::Bytes(b2)) => {
                        Value::Bytes([b1.as_slice(), b2.as_slice()].concat())
                    }
                    _ => unimplemented!(),
                }
            }
            Op::Minus => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs - rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs - rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs - rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Multiply => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs * rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs * rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs * rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Devide => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs / rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs / rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs / rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Mod => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs % rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs % rhs),
                    _ => unimplemented!(),
                }
            }
            Op::And => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs && rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Or => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    // short-circuit evaluation
                    (Value::Bool(true), _) => Value::Bool(true),
                    (_, Value::Bool(true)) => Value::Bool(true),
                    // normal evaluation
                    (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs || rhs),
                    _ => unimplemented!(),
                }
            }
            Op::NotEqual => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs != rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs != rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs != rhs),
                    (Value::String(lhs), Value::String(rhs)) => Value::Bool(lhs != rhs),
                    (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs != rhs),
                    (Value::Bytes(lhs), Value::Bytes(rhs)) => Value::Bool(lhs != rhs),
                    (Value::Null, Value::Null) => Value::Bool(false),
                    (Value::List(lhs), Value::List(rhs)) => Value::Bool(lhs != rhs),
                    (Value::Map(lhs), Value::Map(rhs)) => Value::Bool(lhs != rhs),
                    _ => unimplemented!(),
                }
            }
            Op::EqualEqual => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs == rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs == rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs == rhs),
                    (Value::String(lhs), Value::String(rhs)) => Value::Bool(lhs == rhs),
                    (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs == rhs),
                    (Value::Bytes(lhs), Value::Bytes(rhs)) => Value::Bool(lhs == rhs),
                    (Value::Null, Value::Null) => Value::Bool(true),
                    (Value::List(lhs), Value::List(rhs)) => Value::Bool(lhs == rhs),
                    (Value::Map(lhs), Value::Map(rhs)) => Value::Bool(lhs == rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Greater => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs > rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs > rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs > rhs),
                    _ => unimplemented!(),
                }
            }
            Op::GreaterEqual => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs >= rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs >= rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs >= rhs),
                    _ => unimplemented!(),
                }
            }
            Op::Less => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs < rhs),
                    (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs < rhs),
                    (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs < rhs),
                    _ => unimplemented!(),
                }
            }
            Op::LessEqual => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = self.eval_ast(&tokens[1])?.value(self.env)?;
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
                let first = self.eval_ast(iter.next().unwrap())?.value(self.env)?;
                let kind = first.kind();
                list.push(first);

                for token in iter {
                    let value = self.eval_ast(token)?.value(self.env)?;
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
                let first_key = self
                    .eval_ast(iter.next().expect("Key must be present"))?
                    .value(self.env)?;
                let first_value = self
                    .eval_ast(iter.next().expect("Value must be present"))?
                    .value(self.env)?;
                let key_kind = first_key.kind();
                let value_kind = first_value.kind();

                let mut map = HashMap::new();
                map.insert(MapKey::try_from(first_key)?, first_value);

                while let (Some(key), Some(value)) = (iter.next(), iter.next()) {
                    let key = self.eval_ast(key)?.value(self.env)?;
                    let value = self.eval_ast(value)?.value(self.env)?;
                    if key.kind() != key_kind || value.kind() != value_kind {
                        miette::bail!("Map elements must have the same type");
                    }
                    map.insert(MapKey::try_from(key)?, value);
                }

                Value::Map(map)
            }
            Op::IfTernary => {
                let lhs = match self.eval_ast(&tokens[0])?.value(self.env)? {
                    Value::Bool(b) => b,
                    _ => miette::bail!("Expected bool, found {:?}", tokens[0]),
                };

                if lhs {
                    self.eval_ast(&tokens[1])?.value(self.env)?
                } else {
                    self.eval_ast(&tokens[2])?.value(self.env)?
                }
            }
            Op::Group => self.eval_ast(&tokens[0])?.value(self.env)?,
            Op::In => {
                let lhs = self.eval_ast(&tokens[0])?.value(self.env)?;
                let rhs = match self.eval_ast(&tokens[1])?.value(self.env)? {
                    Value::List(list) => list,
                    _ => miette::bail!("Expected list, found {:?}", tokens[1]),
                };

                if rhs.contains(&lhs) {
                    Value::Bool(true)
                } else {
                    Value::Bool(false)
                }
            }
            Op::For => miette::bail!("For loop is not supported"),
            Op::While => miette::bail!("While loop is not supported"),
            _ => unimplemented!(),
        };
        Ok(val)
    }
}

#[derive(Debug, PartialEq, Clone)]
enum Object {
    Value(Value),
    Reference(String),
}

impl Object {
    fn value(&self, env: &Environment) -> Result<Value, Error> {
        match self {
            Object::Value(val) => Ok(val.clone()),
            Object::Reference(ident) => {
                if let Some(val) = env.get_variable(ident) {
                    Ok(val.clone())
                } else {
                    miette::bail!("Variable not found: {}", ident);
                }
            }
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
    Map(HashMap<MapKey, Value>),
    List(Vec<Value>),
    Bytes(Vec<u8>),
    Null,
}

impl From<i8> for Value {
    fn from(n: i8) -> Self {
        Value::Int(n as i64)
    }
}

impl From<i16> for Value {
    fn from(n: i16) -> Self {
        Value::Int(n as i64)
    }
}

impl From<i32> for Value {
    fn from(n: i32) -> Self {
        Value::Int(n as i64)
    }
}

impl From<i64> for Value {
    fn from(n: i64) -> Self {
        Value::Int(n)
    }
}

impl From<u8> for Value {
    fn from(n: u8) -> Self {
        Value::Uint(n as u64)
    }
}

impl From<u16> for Value {
    fn from(n: u16) -> Self {
        Value::Uint(n as u64)
    }
}

impl From<u32> for Value {
    fn from(n: u32) -> Self {
        Value::Uint(n as u64)
    }
}

impl From<u64> for Value {
    fn from(n: u64) -> Self {
        Value::Uint(n)
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::String(s)
    }
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

fn fn_size(vals: &[Value]) -> Result<Value, Error> {
    if vals.len() != 1 {
        miette::bail!("Expected 1 argument, found {}", vals.len());
    }

    m_size(&vals[0], vals)
}

fn m_size<'a>(this: &'a Value, _: &'a [Value]) -> Result<Value, Error> {
    let v = match this {
        Value::Bytes(b) => Value::Int(b.len() as i64),
        Value::String(s) => Value::Int(s.len() as i64),
        Value::List(list) => Value::Int(list.len() as i64),
        Value::Map(map) => Value::Int(map.len() as i64),
        _ => miette::bail!("Invalid type for size: {:?}", this),
    };

    Ok(v)
}

fn fn_type(vals: &[Value]) -> Result<Value, Error> {
    if vals.len() != 1 {
        miette::bail!("Expected 1 argument, found {}", vals.len());
    }

    match &vals[0] {
        Value::Int(_) => Ok(Value::String("int".to_string())),
        Value::Uint(_) => Ok(Value::String("uint".to_string())),
        Value::Double(_) => Ok(Value::String("double".to_string())),
        Value::String(_) => Ok(Value::String("string".to_string())),
        Value::Bool(_) => Ok(Value::String("bool".to_string())),
        Value::Map(_) => Ok(Value::String("map".to_string())),
        Value::List(_) => Ok(Value::String("list".to_string())),
        Value::Bytes(_) => Ok(Value::String("bytes".to_string())),
        Value::Null => Ok(Value::String("null".to_string())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_primitives() {
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
    fn test_not_equal() {
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
        assert_eq!(
            interpreter.eval("1 != 1").expect("1 != 1"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1 != 2").expect("1 != 2"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1u != 1u").expect("1u != 1u"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1u != 2u").expect("1u != 2u"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("1.0 != 1.0").expect("1.0 != 1.0"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("1.0 != 2.0").expect("1.0 != 2.0"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("true != true").expect("true != true"),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter.eval("true != false").expect("true != false"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter
                .eval("\"hello\" != \"hello\"")
                .expect("\"hello\" != \"hello\""),
            Value::Bool(false)
        );
        assert_eq!(
            interpreter
                .eval("\"hello\" != \"world\"")
                .expect("\"hello\" != \"world\""),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_greater() {
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
        assert_eq!(interpreter.eval("5 % 2").expect("5 % 2"), Value::Int(1));
        assert_eq!(
            interpreter.eval("5u % 2u").expect("5u % 2u"),
            Value::Uint(1)
        );
    }

    #[test]
    fn test_eval_not() {
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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

        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
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

    #[test]
    fn test_if_ternary() {
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
        assert_eq!(
            interpreter.eval("1 > 2 ? 1 : 2u").expect("1 > 2 ? 1 : 2u"),
            Value::Uint(2)
        );
        assert_eq!(
            interpreter.eval("1 < 2 ? 1 : 2u").expect("1 < 2 ? 1 : 2u"),
            Value::Int(1)
        );
    }

    #[test]
    fn test_group() {
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
        assert_eq!(
            interpreter.eval("(1 + 2) * 3").expect("(1 + 2) * 3"),
            Value::Int(9)
        );
    }

    #[test]
    fn test_in() {
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
        assert_eq!(
            interpreter.eval("1 in [1, 2, 3]").expect("1 in [1, 2, 3]"),
            Value::Bool(true)
        );
        assert_eq!(
            interpreter.eval("4 in [1, 2, 3]").expect("4 in [1, 2, 3]"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_variable() {
        let mut env = Environment::default();
        env.set_variable("x", 42i64.into());
        let interpreter = Interpreter::new(&env);
        assert_eq!(interpreter.eval("x").expect("x"), Value::Int(42));
        assert!(interpreter.eval("y").is_err());
    }

    #[test]
    fn test_size() {
        let env = Environment::default();
        let interpreter = Interpreter::new(&env);
        assert_eq!(
            interpreter.eval("size(\"\")").expect("size(\"\")"),
            Value::Int(0)
        );
        assert_eq!(
            interpreter
                .eval("size(\"hello\")")
                .expect("size(\"hello\")"),
            Value::Int(5)
        );
        assert_eq!(
            interpreter.eval("size([])").expect("size([])"),
            Value::Int(0)
        );
        assert_eq!(
            interpreter
                .eval("size([1, 2, 3])")
                .expect("size([1, 2, 3])"),
            Value::Int(3)
        );
        assert_eq!(
            interpreter.eval("size({})").expect("size({})"),
            Value::Int(0)
        );
        assert_eq!(
            interpreter
                .eval("size({1: 2, 3: 4})")
                .expect("size({1: 2, 3: 4})"),
            Value::Int(2)
        );
    }

    #[test]
    fn test_method_call() {
        let mut env = Environment::default();
        env.set_function(
            "foo",
            Box::new(|args: &[Value]| Ok(Value::Int(args.len() as i64))),
        );
        env.set_variable("x", 42i64.into());
        let interpreter = Interpreter::new(&env);
        assert_eq!(interpreter.eval("x.foo()").expect("x.foo()"), Value::Int(1));
    }
}
