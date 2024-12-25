use miette::Error;
use std::collections::hash_map::{Drain, Entry};
use std::collections::HashMap;
use std::fmt;

pub type Function = Box<dyn Fn(&[Value]) -> Result<Value, Error>>;

#[derive(Debug, PartialEq, Clone)]
pub struct Map {
    key_type: Option<MapKeyType>,
    inner: HashMap<MapKey, Value>,
}

impl Default for Map {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashMap<MapKey, Value>> for Map {
    fn from(inner: HashMap<MapKey, Value>) -> Self {
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

    pub fn new_with_key_type(key_type: MapKeyType) -> Self {
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
    pub fn contains_key(&self, key: &MapKey) -> Result<bool, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.kind() {
                miette::bail!("Invalid key type: {:?}", key.kind());
            }

            Ok(self.inner.contains_key(key))
        } else {
            Ok(false)
        }
    }

    /// Wrapper for https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.drain
    pub fn drain(&mut self) -> Drain<MapKey, Value> {
        self.inner.drain()
    }

    /// Wrapper for entry
    /// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.entry
    /// It checks if the key type is the same as the key kind.
    /// If the key type is not set (map must be empty), it sets the key type.
    pub fn entry(&mut self, key: MapKey) -> Result<Entry<MapKey, Value>, Error> {
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
    pub fn get(&self, key: &MapKey) -> Result<Option<&Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.kind() {
                miette::bail!("Invalid key type: {:?}", key.kind());
            }

            Ok(self.inner.get(key))
        } else {
            Ok(None)
        }
    }

    pub fn insert(&mut self, key: MapKey, value: Value) -> Result<&mut Self, Error> {
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

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
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
pub enum MapKeyType {
    Int,
    Uint,
    String,
    Bool,
}

impl TryFrom<ValueKind> for MapKeyType {
    type Error = Error;

    fn try_from(kind: ValueKind) -> Result<Self, Self::Error> {
        match kind {
            ValueKind::Int => Ok(MapKeyType::Int),
            ValueKind::Uint => Ok(MapKeyType::Uint),
            ValueKind::String => Ok(MapKeyType::String),
            ValueKind::Bool => Ok(MapKeyType::Bool),
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
    fn kind(&self) -> MapKeyType {
        match self {
            MapKey::Int(_) => MapKeyType::Int,
            MapKey::Uint(_) => MapKeyType::Uint,
            MapKey::String(_) => MapKeyType::String,
            MapKey::Bool(_) => MapKeyType::Bool,
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
