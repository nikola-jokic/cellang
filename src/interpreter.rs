use core::fmt;
use miette::Error;
use std::collections::HashMap;

use crate::{
    parser::{Atom, Op, TokenTree},
    Parser,
};

// DO THIS BY REFERENCES AND NOT WITH CLONES

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

pub fn eval(env: &Environment, program: &str) -> Result<Value, Error> {
    let tree = Parser::new(program).parse()?;
    match eval_ast(env, &tree) {
        Ok(Object::Value(val)) => Ok(val),
        Ok(Object::Ident(ident)) => {
            if let Some(val) = env.get_variable(&ident) {
                Ok(val.clone())
            } else {
                miette::bail!("Variable not found: {}", ident);
            }
        }
        Err(e) => Err(e),
    }
}

fn eval_ast(env: &Environment, root: &TokenTree) -> Result<Object, Error> {
    match root {
        TokenTree::Atom(atom) => eval_atom(atom),
        TokenTree::Cons(op, tokens) => Ok(Object::Value(eval_cons(env, op, tokens)?)),
        TokenTree::Call { func, args } => {
            let f = match eval_ast(env, func)? {
                Object::Ident(name) => match env.get_function(&name) {
                    Some(f) => f,
                    None => miette::bail!("Function not found: {}", name),
                },
                _ => miette::bail!("Expected function name, found {:?}", func),
            };
            let args = args
                .iter()
                .map(|arg| eval_ast(env, arg)?.value(env))
                .collect::<Result<Vec<_>, _>>()?;

            Ok(Object::Value(f(&args)?))
        }
    }
}

fn eval_atom(atom: &Atom) -> Result<Object, Error> {
    let val = match atom {
        Atom::Int(n) => Object::Value(Value::Int(*n)),
        Atom::Uint(n) => Object::Value(Value::Uint(*n)),
        Atom::Double(n) => Object::Value(Value::Double(*n)),
        Atom::String(s) => Object::Value(Value::String(s.to_string())),
        Atom::Bool(b) => Object::Value(Value::Bool(*b)),
        Atom::Null => Object::Value(Value::Null),
        Atom::Bytes(b) => Object::Value(Value::Bytes(b.clone().to_vec())),
        Atom::Ident(ident) => Object::Ident(ident.to_string()),
    };
    Ok(val)
}

fn eval_cons(env: &Environment, op: &Op, tokens: &[TokenTree]) -> Result<Value, Error> {
    let val = match op {
        Op::Field => {
            assert!(tokens.len() == 2);

            todo!()
        }
        Op::Index => {
            assert!(tokens.len() == 2);

            match eval_ast(env, &tokens[0])?.value(env)? {
                Value::List(list) => {
                    let i = match eval_ast(env, &tokens[1])?.value(env)? {
                        Value::Int(n) => n,
                        _ => miette::bail!("Expected int index, found {:?}", tokens[1]),
                    };

                    match list {
                        List::Empty => miette::bail!("Index out of bounds"),
                        List::WithValue { inner, .. } => {
                            if i < 0 || i as usize >= inner.len() {
                                miette::bail!("Index out of bounds");
                            }
                            inner[i as usize].clone()
                        }
                    }
                }

                Value::Map(map) => {
                    let key = MapKey::try_from(eval_ast(env, &tokens[1])?.value(env)?)?;

                    match map {
                        Map::Empty => miette::bail!("No such key {key}"),
                        Map::WithValue {
                            inner, key_kind, ..
                        } => {
                            if key_kind != key.kind() {
                                miette::bail!("Invalid key type: {:?}", key);
                            }

                            match inner.get(&key) {
                                Some(val) => val.clone(),
                                None => miette::bail!("No such key {key}"),
                            }
                        }
                    }
                }

                _ => miette::bail!("Expected reference to a list, found {:?}", tokens[0]),
            }
        }
        Op::Not => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            match lhs {
                Value::Bool(b) => Value::Bool(!b),
                _ => miette::bail!("Expected bool, found {:?}", tokens[0]),
            }
        }
        Op::Plus => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
            match (lhs, rhs) {
                (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs + rhs),
                (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs + rhs),
                (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs + rhs),
                (Value::String(s1), Value::String(s2)) => Value::String(format!("{}{}", s1, s2)),
                (Value::Bytes(b1), Value::Bytes(b2)) => {
                    Value::Bytes([b1.as_slice(), b2.as_slice()].concat())
                }
                _ => unimplemented!(),
            }
        }
        Op::Minus => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
            match (lhs, rhs) {
                (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs - rhs),
                (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs - rhs),
                (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs - rhs),
                _ => unimplemented!(),
            }
        }
        Op::Multiply => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
            match (lhs, rhs) {
                (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs * rhs),
                (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs * rhs),
                (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs * rhs),
                _ => unimplemented!(),
            }
        }
        Op::Devide => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
            match (lhs, rhs) {
                (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs / rhs),
                (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs / rhs),
                (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs / rhs),
                _ => unimplemented!(),
            }
        }
        Op::Mod => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
            match (lhs, rhs) {
                (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs % rhs),
                (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs % rhs),
                _ => unimplemented!(),
            }
        }
        Op::And => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
            match (lhs, rhs) {
                (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs && rhs),
                _ => unimplemented!(),
            }
        }
        Op::Or => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
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
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
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
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
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
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
            match (lhs, rhs) {
                (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs > rhs),
                (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs > rhs),
                (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs > rhs),
                _ => unimplemented!(),
            }
        }
        Op::GreaterEqual => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
            match (lhs, rhs) {
                (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs >= rhs),
                (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs >= rhs),
                (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs >= rhs),
                _ => unimplemented!(),
            }
        }
        Op::Less => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
            match (lhs, rhs) {
                (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs < rhs),
                (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs < rhs),
                (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs < rhs),
                _ => unimplemented!(),
            }
        }
        Op::LessEqual => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.value(env)?;
            match (lhs, rhs) {
                (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs <= rhs),
                (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs <= rhs),
                (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs <= rhs),
                _ => unimplemented!(),
            }
        }
        Op::List => {
            if tokens.is_empty() {
                return Ok(Value::List(List::Empty));
            }

            let mut list = Vec::with_capacity(tokens.len());
            let mut iter = tokens.iter();
            let first = eval_ast(env, iter.next().unwrap())?.value(env)?;
            let kind = first.kind();
            list.push(first);

            for token in iter {
                let value = eval_ast(env, token)?.value(env)?;
                if value.kind() != kind {
                    miette::bail!("List elements must have the same type");
                }
                list.push(value);
            }

            Value::List(List::WithValue {
                elem_kind: kind,
                inner: list,
            })
        }
        Op::Map => {
            if tokens.is_empty() {
                return Ok(Value::Map(Map::Empty));
            }

            let mut iter = tokens.iter();
            let first_key = eval_ast(env, iter.next().expect("Key must be present"))?.value(env)?;
            let first_value =
                eval_ast(env, iter.next().expect("Value must be present"))?.value(env)?;
            let key_kind = MapKeyKind::try_from(first_key.kind())?;
            let value_kind = first_value.kind();

            let mut map = HashMap::new();
            map.insert(MapKey::try_from(first_key)?, first_value);

            while let (Some(key), Some(value)) = (iter.next(), iter.next()) {
                let key = eval_ast(env, key)?.value(env)?;
                let value = eval_ast(env, value)?.value(env)?;
                let kk = MapKeyKind::try_from(key.kind())?;
                if kk != key_kind || value.kind() != value_kind {
                    miette::bail!("Map elements must have the same type");
                }
                map.insert(MapKey::try_from(key)?, value);
            }

            Value::Map(Map::WithValue {
                key_kind,
                value_kind,
                inner: map,
            })
        }
        Op::IfTernary => {
            let lhs = match eval_ast(env, &tokens[0])?.value(env)? {
                Value::Bool(b) => b,
                _ => miette::bail!("Expected bool, found {:?}", tokens[0]),
            };

            if lhs {
                eval_ast(env, &tokens[1])?.value(env)?
            } else {
                eval_ast(env, &tokens[2])?.value(env)?
            }
        }
        Op::Group => eval_ast(env, &tokens[0])?.value(env)?,
        Op::In => {
            let lhs = eval_ast(env, &tokens[0])?.value(env)?;
            match eval_ast(env, &tokens[1])?.value(env)? {
                Value::List(list) => match list {
                    List::Empty => Value::Bool(false),
                    List::WithValue { inner, .. } => Value::Bool(inner.contains(&lhs)),
                },
                _ => miette::bail!("Expected list, found {:?}", tokens[1]),
            }
        }
        Op::For => miette::bail!("For loop is not supported"),
        Op::While => miette::bail!("While loop is not supported"),
        _ => unimplemented!(),
    };
    Ok(val)
}

#[derive(Debug, PartialEq, Clone)]
enum Object {
    Value(Value),
    Ident(String),
}

impl Object {
    fn value(&self, env: &Environment) -> Result<Value, Error> {
        match self {
            Object::Value(val) => Ok(val.clone()),
            Object::Ident(ident) => {
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
    Map(Map),
    List(List),
    Bytes(Vec<u8>),
    Null,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Uint(n) => write!(f, "{}", n),
            Value::Double(n) => write!(f, "{}", n),
            Value::String(s) => write!(f, "{}", s),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Map(map) => match map {
                Map::Empty => write!(f, "{{}}"),
                Map::WithValue { inner, .. } => {
                    write!(f, "{:?}", inner)
                }
            },
            Value::List(list) => match list {
                List::Empty => write!(f, "[]"),
                List::WithValue { inner, .. } => {
                    write!(f, "{:?}", inner)
                }
            },
            Value::Bytes(b) => write!(f, "{:?}", b),
            Value::Null => write!(f, "null"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Map {
    Empty,
    WithValue {
        key_kind: MapKeyKind,
        value_kind: ValueKind,
        inner: HashMap<MapKey, Value>,
    },
}

#[derive(Debug, PartialEq, Clone)]
pub enum List {
    Empty,
    WithValue {
        elem_kind: ValueKind,
        inner: Vec<Value>,
    },
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
pub enum ValueKind {
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

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum MapKeyKind {
    Int,
    Uint,
    String,
    Bool,
}

impl TryFrom<ValueKind> for MapKeyKind {
    type Error = Error;

    fn try_from(kind: ValueKind) -> Result<Self, Self::Error> {
        match kind {
            ValueKind::Int => Ok(MapKeyKind::Int),
            ValueKind::Uint => Ok(MapKeyKind::Uint),
            ValueKind::String => Ok(MapKeyKind::String),
            ValueKind::Bool => Ok(MapKeyKind::Bool),
            _ => miette::bail!("Invalid map key kind: {:?}", kind),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum MapKey {
    Int(i64),
    Uint(u64),
    String(String),
    Bool(bool),
}

impl MapKey {
    fn kind(&self) -> MapKeyKind {
        match self {
            MapKey::Int(_) => MapKeyKind::Int,
            MapKey::Uint(_) => MapKeyKind::Uint,
            MapKey::String(_) => MapKeyKind::String,
            MapKey::Bool(_) => MapKeyKind::Bool,
        }
    }
}

impl fmt::Display for MapKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MapKey::Int(n) => write!(f, "{}", n),
            MapKey::Uint(n) => write!(f, "{}", n),
            MapKey::String(s) => write!(f, "{}", s),
            MapKey::Bool(b) => write!(f, "{}", b),
        }
    }
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

    let v = match &vals[0] {
        Value::Bytes(b) => Value::Int(b.len() as i64),
        Value::String(s) => Value::Int(s.len() as i64),
        Value::List(list) => match list {
            List::Empty => Value::Int(0),
            List::WithValue { inner, .. } => Value::Int(inner.len() as i64),
        },
        Value::Map(map) => match map {
            Map::Empty => Value::Int(0),
            Map::WithValue { inner, .. } => Value::Int(inner.len() as i64),
        },
        _ => miette::bail!("Invalid type for size: {:?}", vals[0].kind()),
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

        assert_eq!(eval(&env, "42").expect("42"), Value::Int(42));
        assert_eq!(eval(&env, "true").expect("true"), Value::Bool(true));
        assert_eq!(eval(&env, "false").expect("false"), Value::Bool(false));
        assert_eq!(eval(&env, "null").expect("null"), Value::Null);
        assert_eq!(
            eval(&env, "\"hello\"").expect("hello"),
            Value::String("hello".to_string())
        );
    }

    #[test]
    fn test_eval_plus() {
        let env = Environment::default();

        assert_eq!(eval(&env, "1 + 2").expect("1 + 2"), Value::Int(3));
        assert_eq!(eval(&env, "1u + 2u").expect("1u + 2u"), Value::Uint(3));
        assert_eq!(
            eval(&env, "1.0 + 2.0").expect("1.0 + 2.0"),
            Value::Double(3.0)
        );
        assert_eq!(
            eval(&env, "\"hello\" + \"world\"").expect("\"hello\" + \"world\""),
            Value::String("helloworld".to_string())
        );
    }

    #[test]
    fn test_eval_minus() {
        let env = Environment::default();

        assert_eq!(eval(&env, "1 - 2").expect("1 - 2"), Value::Int(-1));
        assert_eq!(eval(&env, "2u - 1u").expect("2u - 1u"), Value::Uint(1));
        assert_eq!(
            eval(&env, "1.0 - 2.0").expect("1.0 - 2.0"),
            Value::Double(-1.0)
        );
    }

    #[test]
    fn test_eval_multiply() {
        let env = Environment::default();

        assert_eq!(eval(&env, "2 * 3").expect("2 * 3"), Value::Int(6));
        assert_eq!(eval(&env, "2u * 3u").expect("2u * 3u"), Value::Uint(6));
        assert_eq!(
            eval(&env, "2.0 * 3.0").expect("2.0 * 3.0"),
            Value::Double(6.0)
        );
    }

    #[test]
    fn test_eval_devide() {
        let env = Environment::default();

        assert_eq!(eval(&env, "6 / 3").expect("6 / 3"), Value::Int(2));
        assert_eq!(eval(&env, "6u / 3u").expect("6u / 3u"), Value::Uint(2));
        assert_eq!(
            eval(&env, "6.0 / 3.0").expect("6.0 / 3.0"),
            Value::Double(2.0)
        );
    }

    #[test]
    fn test_eval_and() {
        let env = Environment::default();

        assert_eq!(
            eval(&env, "true && false").expect("true && false"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "true && true").expect("true && true"),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_or() {
        let env = Environment::default();

        assert_eq!(
            eval(&env, "false || true").expect("false || true"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "false || false").expect("false || false"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_eval_equal_equal() {
        let env = Environment::default();

        assert_eq!(eval(&env, "1 == 1").expect("1 == 1"), Value::Bool(true));
        assert_eq!(eval(&env, "1 == 2").expect("1 == 2"), Value::Bool(false));
        assert_eq!(eval(&env, "1u == 1u").expect("1u == 1u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "1u == 2u").expect("1u == 2u"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "1.0 == 1.0").expect("1.0 == 1.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "1.0 == 2.0").expect("1.0 == 2.0"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "true == true").expect("true == true"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "true == false").expect("true == false"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "\"hello\" == \"hello\"").expect("\"hello\" == \"hello\""),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "\"hello\" == \"world\"").expect("\"hello\" == \"world\""),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_not_equal() {
        let env = Environment::default();

        assert_eq!(eval(&env, "1 != 1").expect("1 != 1"), Value::Bool(false));
        assert_eq!(eval(&env, "1 != 2").expect("1 != 2"), Value::Bool(true));
        assert_eq!(
            eval(&env, "1u != 1u").expect("1u != 1u"),
            Value::Bool(false)
        );
        assert_eq!(eval(&env, "1u != 2u").expect("1u != 2u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "1.0 != 1.0").expect("1.0 != 1.0"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "1.0 != 2.0").expect("1.0 != 2.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "true != true").expect("true != true"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "true != false").expect("true != false"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "\"hello\" != \"hello\"").expect("\"hello\" != \"hello\""),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "\"hello\" != \"world\"").expect("\"hello\" != \"world\""),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_greater() {
        let env = Environment::default();

        assert_eq!(eval(&env, "2 > 1").expect("2 > 1"), Value::Bool(true));
        assert_eq!(eval(&env, "1 > 2").expect("1 > 2"), Value::Bool(false));
        assert_eq!(eval(&env, "2u > 1u").expect("2u > 1u"), Value::Bool(true));
        assert_eq!(eval(&env, "1u > 2u").expect("1u > 2u"), Value::Bool(false));
        assert_eq!(
            eval(&env, "2.0 > 1.0").expect("2.0 > 1.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "1.0 > 2.0").expect("1.0 > 2.0"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_eval_greater_equal() {
        let env = Environment::default();

        assert_eq!(eval(&env, "2 >= 1").expect("2 >= 1"), Value::Bool(true));
        assert_eq!(eval(&env, "1 >= 2").expect("1 >= 2"), Value::Bool(false));
        assert_eq!(eval(&env, "1 >= 1").expect("1 >= 1"), Value::Bool(true));
        assert_eq!(eval(&env, "2u >= 1u").expect("2u >= 1u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "1u >= 2u").expect("1u >= 2u"),
            Value::Bool(false)
        );
        assert_eq!(eval(&env, "1u >= 1u").expect("1u >= 1u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "2.0 >= 1.0").expect("2.0 >= 1.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "1.0 >= 2.0").expect("1.0 >= 2.0"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "1.0 >= 1.0").expect("1.0 >= 1.0"),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_less() {
        let env = Environment::default();

        assert_eq!(eval(&env, "1 < 2").expect("1 < 2"), Value::Bool(true));
        assert_eq!(eval(&env, "2 < 1").expect("2 < 1"), Value::Bool(false));
        assert_eq!(eval(&env, "1u < 2u").expect("1u < 2u"), Value::Bool(true));
        assert_eq!(eval(&env, "2u < 1u").expect("2u < 1u"), Value::Bool(false));
        assert_eq!(
            eval(&env, "1.0 < 2.0").expect("1.0 < 2.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "2.0 < 1.0").expect("2.0 < 1.0"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_eval_less_equal() {
        let env = Environment::default();

        assert_eq!(eval(&env, "1 <= 2").expect("1 <= 2"), Value::Bool(true));
        assert_eq!(eval(&env, "2 <= 1").expect("2 <= 1"), Value::Bool(false));
        assert_eq!(eval(&env, "1 <= 1").expect("1 <= 1"), Value::Bool(true));
        assert_eq!(eval(&env, "1u <= 2u").expect("1u <= 2u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "2u <= 1u").expect("2u <= 1u"),
            Value::Bool(false)
        );
        assert_eq!(eval(&env, "1u <= 1u").expect("1u <= 1u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "1.0 <= 2.0").expect("1.0 <= 2.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "2.0 <= 1.0").expect("2.0 <= 1.0"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "1.0 <= 1.0").expect("1.0 <= 1.0"),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_mod() {
        let env = Environment::default();

        assert_eq!(eval(&env, "5 % 2").expect("5 % 2"), Value::Int(1));
        assert_eq!(eval(&env, "5u % 2u").expect("5u % 2u"), Value::Uint(1));
    }

    #[test]
    fn test_eval_not() {
        let env = Environment::default();

        assert_eq!(eval(&env, "!true").expect("!true"), Value::Bool(false));
        assert_eq!(eval(&env, "!false").expect("!false"), Value::Bool(true));
    }

    #[test]
    fn test_list() {
        let env = Environment::default();

        assert_eq!(eval(&env, "[]").expect("[]"), Value::List(List::Empty));
        assert_eq!(
            eval(&env, "[1, 2, 3]").expect("[1, 2, 3]"),
            Value::List(List::WithValue {
                elem_kind: ValueKind::Int,
                inner: vec![Value::Int(1), Value::Int(2), Value::Int(3)]
            })
        );
        assert_eq!(
            eval(&env, "[1u, 2u, 3u]").expect("[1u, 2u, 3u]"),
            Value::List(List::WithValue {
                elem_kind: ValueKind::Uint,
                inner: vec![Value::Uint(1), Value::Uint(2), Value::Uint(3)]
            })
        );
        assert_eq!(
            eval(&env, "[1.0, 2.0, 3.0]").expect("[1.0, 2.0, 3.0]"),
            Value::List(List::WithValue {
                elem_kind: ValueKind::Double,
                inner: vec![Value::Double(1.0), Value::Double(2.0), Value::Double(3.0)]
            })
        );
        assert_eq!(
            eval(&env, "[\"hello\", \"world\"]").expect("[\"hello\", \"world\"]"),
            Value::List(List::WithValue {
                elem_kind: ValueKind::String,
                inner: vec![
                    Value::String("hello".to_string()),
                    Value::String("world".to_string())
                ]
            })
        );
        assert_eq!(
            eval(&env, "[true, false]").expect("[true, false]"),
            Value::List(List::WithValue {
                elem_kind: ValueKind::Bool,
                inner: vec![Value::Bool(true), Value::Bool(false)]
            })
        );

        // list elements must have the same type
        let tt = [
            "[1, 2u, 3]",
            "[1, 2.0, 3]",
            "[1, \"hello\", 3]",
            "[1, true, 3]",
        ];
        for t in tt.iter() {
            let result = eval(&env, t);
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_map() {
        let tt = [
            ("{}", Value::Map(Map::Empty)),
            ("{1: 2, 3: 4}", {
                let mut map = HashMap::new();
                map.insert(MapKey::Int(1), Value::Int(2));
                map.insert(MapKey::Int(3), Value::Int(4));
                Value::Map(Map::WithValue {
                    key_kind: MapKeyKind::Int,
                    value_kind: ValueKind::Int,
                    inner: map,
                })
            }),
            ("{1u: 2u, 3u: 4u}", {
                let mut map = HashMap::new();
                map.insert(MapKey::Uint(1), Value::Uint(2));
                map.insert(MapKey::Uint(3), Value::Uint(4));
                Value::Map(Map::WithValue {
                    key_kind: MapKeyKind::Uint,
                    value_kind: ValueKind::Uint,
                    inner: map,
                })
            }),
            ("{\"hello\": \"world\"}", {
                let mut map = HashMap::new();
                map.insert(
                    MapKey::String("hello".to_string()),
                    Value::String("world".to_string()),
                );
                Value::Map(Map::WithValue {
                    key_kind: MapKeyKind::String,
                    value_kind: ValueKind::String,
                    inner: map,
                })
            }),
            ("{true: false}", {
                let mut map = HashMap::new();
                map.insert(MapKey::Bool(true), Value::Bool(false));
                Value::Map(Map::WithValue {
                    key_kind: MapKeyKind::Bool,
                    value_kind: ValueKind::Bool,
                    inner: map,
                })
            }),
        ];

        let env = Environment::default();

        for (input, expected) in tt.iter() {
            let result = eval(&env, input).expect(input);
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
            let result = eval(&env, input);
            assert!(result.is_err());
            assert_eq!(result.unwrap_err().to_string(), *expected);
        }
    }

    #[test]
    fn test_if_ternary() {
        let env = Environment::default();

        assert_eq!(
            eval(&env, "1 > 2 ? 1 : 2u").expect("1 > 2 ? 1 : 2u"),
            Value::Uint(2)
        );
        assert_eq!(
            eval(&env, "1 < 2 ? 1 : 2u").expect("1 < 2 ? 1 : 2u"),
            Value::Int(1)
        );
    }

    #[test]
    fn test_group() {
        let env = Environment::default();

        assert_eq!(
            eval(&env, "(1 + 2) * 3").expect("(1 + 2) * 3"),
            Value::Int(9)
        );
    }

    #[test]
    fn test_in() {
        let env = Environment::default();

        assert_eq!(
            eval(&env, "1 in [1, 2, 3]").expect("1 in [1, 2, 3]"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "4 in [1, 2, 3]").expect("4 in [1, 2, 3]"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_variable() {
        let mut env = Environment::default();
        env.set_variable("x", 42i64.into());

        assert_eq!(eval(&env, "x").expect("x"), Value::Int(42));
        assert!(eval(&env, "y").is_err());
    }

    #[test]
    fn test_size() {
        let env = Environment::default();

        assert_eq!(eval(&env, "size(\"\")").expect("size(\"\")"), Value::Int(0));
        assert_eq!(
            eval(&env, "size(\"hello\")").expect("size(\"hello\")"),
            Value::Int(5)
        );
        assert_eq!(eval(&env, "size([])").expect("size([])"), Value::Int(0));
        assert_eq!(
            eval(&env, "size([1, 2, 3])").expect("size([1, 2, 3])"),
            Value::Int(3)
        );
        assert_eq!(eval(&env, "size({})").expect("size({})"), Value::Int(0));
        assert_eq!(
            eval(&env, "size({1: 2, 3: 4})").expect("size({1: 2, 3: 4})"),
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

        assert_eq!(eval(&env, "x.foo()").expect("x.foo()"), Value::Int(1));
    }

    #[test]
    fn test_index_map_access() {
        let mut env = Environment::default();
        env.set_variable("x", {
            let mut leaf = HashMap::new();
            leaf.insert(MapKey::String("y".to_string()), Value::Int(42));

            let leaf = Value::Map(Map::WithValue {
                key_kind: MapKeyKind::String,
                value_kind: ValueKind::Int,
                inner: leaf,
            });

            let mut middle_level = HashMap::new();
            middle_level.insert(MapKey::Int(0), leaf);

            let middle_level = Value::Map(Map::WithValue {
                key_kind: MapKeyKind::Int,
                value_kind: ValueKind::Map,
                inner: middle_level,
            });

            let mut root = HashMap::new();
            root.insert(MapKey::Bool(true), middle_level);

            Value::Map(Map::WithValue {
                key_kind: MapKeyKind::Bool,
                value_kind: ValueKind::Map,
                inner: root,
            })
        });

        assert_eq!(
            eval(&env, "x[true][0][\"y\"]").expect("x[true][0][\"y\"]"),
            Value::Int(42)
        );
    }

    #[test]
    fn test_field_map_access() {
        let mut env = Environment::default();
        env.set_variable("x", {
            let leaf = Value::Map(Map::WithValue {
                key_kind: MapKeyKind::String,
                value_kind: ValueKind::Int,
                inner: {
                    let mut leaf = HashMap::new();
                    leaf.insert(MapKey::String("z".to_string()), Value::Uint(42));
                    leaf
                },
            });

            Value::Map(Map::WithValue {
                key_kind: MapKeyKind::String,
                value_kind: ValueKind::Map,
                inner: {
                    let mut root = HashMap::new();
                    root.insert(MapKey::String("y".to_string()), leaf);
                    root
                },
            })
        });

        assert_eq!(eval(&env, "x.y.z").expect("x.y.z"), Value::Uint(42));
    }
}
