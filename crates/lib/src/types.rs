use miette::Error;
use std::collections::hash_map::{Drain, Entry, IntoValues, Iter, IterMut, Keys, RandomState};
use std::collections::HashMap;
use std::fmt;

use crate::parser::TokenTree;
use crate::{impl_value_conversions, Environment};

pub type Function = Box<dyn Fn(&Environment, &[TokenTree]) -> Result<Value, Error>>;

#[derive(Debug, PartialEq, Clone)]
pub struct Map {
    key_type: Option<KeyType>,
    inner: HashMap<Key, Value>,
}

impl Default for Map {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashMap<Key, Value>> for Map {
    fn from(inner: HashMap<Key, Value>) -> Self {
        if inner.is_empty() {
            Self::new()
        } else {
            Self {
                key_type: Some(inner.keys().next().unwrap().kind()),
                inner,
            }
        }
    }
}

impl Map {
    /// The new returns a map with no key type and no elements.
    pub fn new() -> Self {
        Self {
            key_type: None,
            inner: HashMap::new(),
        }
    }

    pub fn with_key_type(key_type: KeyType) -> Self {
        Self {
            key_type: Some(key_type),
            inner: HashMap::new(),
        }
    }

    /// Wrapper for https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.capacity
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Wrapper for https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.clear
    /// It doesn't clear the key type.
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Wrapper for
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.contains_key
    /// It checks if the key type is the same as the key kind.
    /// If the key type is not set (map must be empty), it returns false.
    pub fn contains_key(&self, key: &Key) -> Result<bool, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.kind() {
                miette::bail!("Invalid key type: {:?}", key.kind());
            }

            Ok(self.inner.contains_key(key))
        } else {
            Ok(false)
        }
    }

    /// Wrapper for drain
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.drain
    pub fn drain(&mut self) -> Drain<'_, Key, Value> {
        self.inner.drain()
    }

    /// Wrapper for entry
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.entry
    /// It checks if the key type is the same as the key kind.
    /// If the key type is not set (map must be empty), it sets the key type.
    pub fn entry(&mut self, key: Key) -> Result<Entry<Key, Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.kind() {
                miette::bail!("Invalid key type: {:?}", key.kind());
            }
        } else {
            self.key_type = Some(key.kind());
        }

        Ok(self.inner.entry(key))
    }

    /// Wrapper for https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve
    pub fn get(&self, key: &Key) -> Result<Option<&Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.kind() {
                miette::bail!("Invalid key type: {:?}", key.kind());
            }

            Ok(self.inner.get(key))
        } else {
            Ok(None)
        }
    }

    /// Wrapper for get_key_value
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get_key_value
    pub fn get_key_value(&self, key: &Key) -> Result<Option<(&Key, &Value)>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.kind() {
                miette::bail!("Invalid key type: {:?}", key.kind());
            }

            Ok(self.inner.get_key_value(key))
        } else {
            Ok(None)
        }
    }

    /// Wrapper for get_mut
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get_mut
    pub fn get_mut(&mut self, key: &Key) -> Result<Option<&mut Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.kind() {
                miette::bail!("Invalid key type: {:?}", key.kind());
            }

            Ok(self.inner.get_mut(key))
        } else {
            Ok(None)
        }
    }

    /// Wrapper for hasher
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.hasher
    pub fn hasher(&self) -> &RandomState {
        self.inner.hasher()
    }

    /// Wrapper for insert
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.insert
    pub fn insert(&mut self, key: Key, value: Value) -> Result<&mut Self, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.kind() {
                miette::bail!("Invalid key type: {:?}", key.kind());
            }
        } else {
            self.key_type = Some(key.kind());
        }

        self.inner.insert(key, value);
        Ok(self)
    }

    /// Wrapper for into_keys
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.into_keys
    pub fn into_keys(self) -> impl Iterator<Item = Key> {
        self.inner.into_keys()
    }

    /// Wrapper for into_values
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.into_values
    pub fn into_values(self) -> IntoValues<Key, Value> {
        self.inner.into_values()
    }

    /// Wrapper for is_empty
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.is_empty
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Wrapper for iter
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.iter
    pub fn iter(&self) -> Iter<'_, Key, Value> {
        self.inner.iter()
    }

    /// Wrapper for iter_mut
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.iter_mut
    pub fn iter_mut(&mut self) -> IterMut<'_, Key, Value> {
        self.inner.iter_mut()
    }

    /// Wrapper for keys
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.keys
    pub fn keys(&self) -> Keys<'_, Key, Value> {
        self.inner.keys()
    }

    /// Wrapper for len
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.len
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Wrapper for remove
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove
    pub fn remove(&mut self, key: &Key) -> Result<Option<Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.kind() {
                miette::bail!("Invalid key type: {:?}", key.kind());
            }
        } else {
            self.key_type = Some(key.kind());
        }

        Ok(self.inner.remove(key))
    }

    /// Wrapper for reserve
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Wrapper for retain
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.retain
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&Key, &mut Value) -> bool,
    {
        self.inner.retain(f)
    }

    /// Wrapper for shrink_to
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.shrink_to
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity)
    }

    /// Wrapper for shrink_to_fit
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.shrink_to_fit
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

    /// Wrapper for try_insert
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.try_insert
    pub fn try_insert(&mut self, key: Key, value: Value) -> Result<Option<Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.kind() {
                miette::bail!("Invalid key type: {:?}", key.kind());
            }
        } else {
            self.key_type = Some(key.kind());
        }

        Ok(self.inner.insert(key, value))
    }

    /// Wrapper for try_reserve
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.try_reserve
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), Error> {
        match self.inner.try_reserve(additional) {
            Ok(_) => Ok(()),
            Err(e) => miette::bail!(e),
        }
    }

    /// Wrapper for values
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.values
    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.inner.values()
    }

    /// Wrapper for values_mut
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.values_mut
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut Value> {
        self.inner.values_mut()
    }

    /// Wrapper for with_capacity
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            key_type: None,
            inner: HashMap::with_capacity(capacity),
        }
    }

    pub fn with_type_and_capacity(key_type: KeyType, capacity: usize) -> Self {
        Self {
            key_type: Some(key_type),
            inner: HashMap::with_capacity(capacity),
        }
    }

    /// Wrapper for with_capacity_and_hasher
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity_and_hasher
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: RandomState) -> Self {
        Self {
            key_type: None,
            inner: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    pub fn with_type_capacity_and_hasher(
        key_type: KeyType,
        capacity: usize,
        hash_builder: RandomState,
    ) -> Self {
        Self {
            key_type: Some(key_type),
            inner: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    /// Wrapper for with_hasher
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_hasher
    pub fn with_hasher(hash_builder: RandomState) -> Self {
        Self {
            key_type: None,
            inner: HashMap::with_hasher(hash_builder),
        }
    }

    pub fn with_type_and_hasher(key_type: KeyType, hash_builder: RandomState) -> Self {
        Self {
            key_type: Some(key_type),
            inner: HashMap::with_hasher(hash_builder),
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
    Any(Box<Value>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Uint(n) => write!(f, "{}", n),
            Value::Double(n) => write!(f, "{}", n),
            Value::String(s) => write!(f, "{}", s),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Map(map) => write!(f, "{:?}", map.inner),
            Value::List(list) => write!(f, "{:?}", list.inner),
            Value::Bytes(b) => write!(f, "{:?}", b),
            Value::Null => write!(f, "null"),
            Value::Any(v) => write!(f, "any({})", v),
        }
    }
}

impl Value {
    pub fn downcast(&self) -> &Value {
        match self {
            Value::Any(v) => v.downcast(),
            _ => self,
        }
    }

    pub fn plus(&self, other: &Value) -> Result<Value, Error> {
        match (self.downcast(), other.downcast()) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            (Value::Uint(a), Value::Uint(b)) => Ok(Value::Uint(a + b)),
            (Value::Double(a), Value::Double(b)) => Ok(Value::Double(a + b)),
            (Value::String(a), Value::String(b)) => Ok(Value::String(format!("{}{}", a, b))),
            (Value::Bytes(a), Value::Bytes(b)) => {
                Ok(Value::Bytes([a.as_slice(), b.as_slice()].concat()))
            }
            _ => miette::bail!("Invalid types for plus: {:?} and {:?}", self, other),
        }
    }

    pub fn minus(&self, other: &Value) -> Result<Value, Error> {
        match (self.downcast(), other.downcast()) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
            (Value::Uint(a), Value::Uint(b)) => Ok(Value::Uint(a - b)),
            (Value::Double(a), Value::Double(b)) => Ok(Value::Double(a - b)),
            _ => miette::bail!("Invalid types for minus: {:?} and {:?}", self, other),
        }
    }

    pub fn equals(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self.downcast(), other.downcast()) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs == rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs == rhs),
            (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs == rhs),
            (Value::String(lhs), Value::String(rhs)) => Value::Bool(lhs == rhs),
            (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs == rhs),
            (Value::Bytes(lhs), Value::Bytes(rhs)) => Value::Bool(lhs == rhs),
            (Value::Null, Value::Null) => Value::Bool(true),
            (Value::List(lhs), Value::List(rhs)) => Value::Bool(lhs == rhs),
            (Value::Map(lhs), Value::Map(rhs)) => Value::Bool(lhs == rhs),
            (left, right) => miette::bail!("Cannot compare {:?} and {:?}", left, right),
        };

        Ok(v)
    }

    pub fn not_equals(&self, other: &Value) -> Result<Value, Error> {
        match self.equals(other) {
            Ok(Value::Bool(b)) => Ok(Value::Bool(!b)),
            Ok(_) => miette::bail!("Invalid types for not_equals: {:?} and {:?}", self, other),
            Err(e) => Err(e),
        }
    }

    pub fn greater(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self.downcast(), other.downcast()) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs > rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs > rhs),
            (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs > rhs),
            (Value::String(lhs), Value::String(rhs)) => Value::Bool(lhs > rhs),
            (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs > rhs),
            (Value::Bytes(lhs), Value::Bytes(rhs)) => Value::Bool(lhs > rhs),
            (left, right) => miette::bail!("Cannot compare {:?} and {:?}", left, right),
        };

        Ok(v)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct List {
    elem_type: Option<ValueKind>,
    inner: Vec<Value>,
}

impl From<Vec<Value>> for List {
    fn from(values: Vec<Value>) -> Self {
        if values.is_empty() {
            Self::new()
        } else {
            Self {
                elem_type: Some(values[0].kind()),
                inner: values,
            }
        }
    }
}

impl List {
    pub fn new() -> Self {
        Self {
            elem_type: None,
            inner: Vec::new(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Value> {
        self.inner.iter()
    }

    pub fn new_with_type(elem_type: ValueKind) -> Self {
        Self {
            elem_type: Some(elem_type),
            inner: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&Value> {
        self.inner.get(index)
    }

    pub fn contains(&self, value: &Value) -> Result<bool, Error> {
        match self.elem_type {
            None => Ok(false),
            Some(ref elem_type) => {
                if *elem_type != value.kind() {
                    miette::bail!("Invalid element type: {:?}", value.kind());
                }

                Ok(self.inner.contains(value))
            }
        }
    }
}

impl Default for List {
    fn default() -> Self {
        Self::new()
    }
}

impl Value {
    pub fn kind(&self) -> ValueKind {
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
            Value::Any(v) => v.kind(),
        }
    }
}

impl_value_conversions! {
    i64 => Value::Int,
    u64 => Value::Uint,
    f64 => Value::Double,
    String => Value::String,
    bool => Value::Bool,
    Map => Value::Map,
    List => Value::List,
    Vec<u8> => Value::Bytes,
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Value::String(value.to_string())
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
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

#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub enum KeyType {
    Int,
    Uint,
    String,
    Bool,
}

impl TryFrom<ValueKind> for KeyType {
    type Error = Error;

    fn try_from(kind: ValueKind) -> Result<Self, Self::Error> {
        match kind {
            ValueKind::Int => Ok(KeyType::Int),
            ValueKind::Uint => Ok(KeyType::Uint),
            ValueKind::String => Ok(KeyType::String),
            ValueKind::Bool => Ok(KeyType::Bool),
            _ => miette::bail!("Invalid map key kind: {:?}", kind),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Key {
    Int(i64),
    Uint(u64),
    String(String),
    Bool(bool),
}

impl TryFrom<Value> for Key {
    type Error = Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Int(n) => Ok(Key::Int(n)),
            Value::Uint(n) => Ok(Key::Uint(n)),
            Value::String(s) => Ok(Key::String(s)),
            Value::Bool(b) => Ok(Key::Bool(b)),
            Value::Any(v) => Key::try_from(*v),
            _ => miette::bail!("Invalid map key: {:?}", value),
        }
    }
}

impl Key {
    fn kind(&self) -> KeyType {
        match self {
            Key::Int(_) => KeyType::Int,
            Key::Uint(_) => KeyType::Uint,
            Key::String(_) => KeyType::String,
            Key::Bool(_) => KeyType::Bool,
        }
    }
}

impl fmt::Display for Key {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Key::Int(n) => write!(f, "{}", n),
            Key::Uint(n) => write!(f, "{}", n),
            Key::String(s) => write!(f, "{}", s),
            Key::Bool(b) => write!(f, "{}", b),
        }
    }
}
