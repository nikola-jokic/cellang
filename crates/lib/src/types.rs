use miette::Error;
use serde::Deserializer;
use serde::{ser::Serializer, Deserialize, Serialize};
use std::collections::hash_map::{self, Entry, IntoValues, Iter, IterMut, Keys, RandomState};
use std::collections::HashMap;
use std::fmt;
use std::vec;
use time::{Duration, OffsetDateTime};

use crate::parser::TokenTree;
use crate::{impl_value_conversions, Environment};

/// Function is a wrapper for a dynamic function that can be registered in the environment.
pub type Function = Box<dyn Fn(&Environment, &[TokenTree]) -> Result<Value, Error>>;

/// Map is a wrapper around HashMap with additional type checking.
#[derive(Debug, PartialEq, Clone)]
pub struct Map {
    key_type: Option<KeyKind>,
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

    pub fn with_key_type(key_type: KeyKind) -> Self {
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
    pub fn drain(&mut self) -> hash_map::Drain<'_, Key, Value> {
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

    pub fn with_type_and_capacity(key_type: KeyKind, capacity: usize) -> Self {
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
        key_type: KeyKind,
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

    pub fn with_type_and_hasher(key_type: KeyKind, hash_builder: RandomState) -> Self {
        Self {
            key_type: Some(key_type),
            inner: HashMap::with_hasher(hash_builder),
        }
    }
}

impl Serialize for Map {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.inner.serialize(serializer)
    }
}

impl From<serde_json::Value> for Map {
    fn from(value: serde_json::Value) -> Self {
        match value {
            serde_json::Value::Object(inner) => Map::from(
                inner
                    .into_iter()
                    .map(|(k, v)| (Key::String(k), Value::from(v)))
                    .collect::<HashMap<Key, Value>>(),
            ),
            _ => Map::new(),
        }
    }
}

impl<'de> Deserialize<'de> for Map {
    fn deserialize<D>(deserializer: D) -> Result<Map, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value: serde_json::Value = Deserialize::deserialize(deserializer)?;
        if let serde_json::Value::Object(inner) = value {
            Ok(Map::from(
                inner
                    .into_iter()
                    .map(|(k, v)| (Key::String(k), Value::from(v)))
                    .collect::<HashMap<Key, Value>>(),
            ))
        } else {
            Err(serde::de::Error::custom("Invalid map"))
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
    Timestamp(OffsetDateTime),
    Duration(Duration),
}

impl From<serde_json::Value> for Value {
    fn from(value: serde_json::Value) -> Self {
        match value {
            serde_json::Value::Null => Value::Null,
            serde_json::Value::Bool(b) => Value::Bool(b),
            serde_json::Value::Number(n) => {
                if let Some(i) = n.as_i64() {
                    Value::Int(i)
                } else if let Some(u) = n.as_u64() {
                    Value::Uint(u)
                } else {
                    Value::Double(n.as_f64().unwrap())
                }
            }
            serde_json::Value::String(s) => Value::String(s),
            serde_json::Value::Array(a) => {
                if a.is_empty() {
                    Value::List(List::new())
                } else {
                    Value::List(List::from(
                        a.into_iter().map(Value::from).collect::<Vec<Value>>(),
                    ))
                }
            }
            serde_json::Value::Object(o) => {
                if o.is_empty() {
                    Value::Map(Map::new())
                } else {
                    Value::Map(Map::from(
                        o.into_iter()
                            .map(|(k, v)| (Key::String(k), Value::from(v)))
                            .collect::<HashMap<Key, Value>>(),
                    ))
                }
            }
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

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{n}"),
            Value::Uint(n) => write!(f, "{n}"),
            Value::Double(n) => write!(f, "{n}"),
            Value::String(s) => write!(f, "{s}"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Map(map) => write!(f, "{:?}", map.inner),
            Value::List(list) => write!(f, "{:?}", list.inner),
            Value::Bytes(b) => write!(f, "{b:?}"),
            Value::Null => write!(f, "null"),
            Value::Timestamp(v) => write!(f, "{v}"),
            Value::Duration(v) => write!(f, "{v:?}"),
        }
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
            Value::Timestamp(_) => ValueKind::Timestamp,
            Value::Duration(_) => ValueKind::Duration,
        }
    }

    pub fn plus(&self, other: &Value) -> Result<Value, Error> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            (Value::Uint(a), Value::Uint(b)) => Ok(Value::Uint(a + b)),
            (Value::Double(a), Value::Double(b)) => Ok(Value::Double(a + b)),
            (Value::String(a), Value::String(b)) => Ok(Value::String(format!("{}{}", a, b))),
            (Value::Bytes(a), Value::Bytes(b)) => {
                Ok(Value::Bytes([a.as_slice(), b.as_slice()].concat()))
            }
            (Value::List(a), Value::List(b)) => {
                let mut list = a.clone();
                list.append(&mut b.clone())?;
                Ok(Value::List(list))
            }
            (Value::Timestamp(t), Value::Duration(d)) => Ok(Value::Timestamp(*t + *d)),
            (Value::Duration(d), Value::Timestamp(t)) => Ok(Value::Timestamp(*t + *d)),
            (Value::Duration(d1), Value::Duration(d2)) => Ok(Value::Duration(*d1 + *d2)),

            _ => miette::bail!("Invalid types for plus: {:?} and {:?}", self, other),
        }
    }

    pub fn minus(&self, other: &Value) -> Result<Value, Error> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
            (Value::Uint(a), Value::Uint(b)) => Ok(Value::Uint(a - b)),
            (Value::Double(a), Value::Double(b)) => Ok(Value::Double(a - b)),
            (Value::Timestamp(t), Value::Duration(d)) => Ok(Value::Timestamp(*t - *d)),
            (Value::Duration(d), Value::Timestamp(t)) => Ok(Value::Timestamp(*t - *d)),
            (Value::Duration(d1), Value::Duration(d2)) => Ok(Value::Duration(*d1 - *d2)),
            _ => miette::bail!("Invalid types for minus: {:?} and {:?}", self, other),
        }
    }

    /// The equal method compares two values and returns a boolean value.
    /// Values MUST be of the same type. If they are not, an error is returned.
    pub fn equal(&self, other: &Value) -> Result<Value, Error> {
        if self.kind() != other.kind() {
            miette::bail!("Cannot compare {:?} and {:?}", self, other);
        }
        Ok(Value::Bool(self == other))
    }

    pub fn not_equal(&self, other: &Value) -> Result<Value, Error> {
        match self.equal(other) {
            Ok(Value::Bool(b)) => Ok(Value::Bool(!b)),
            Ok(_) => miette::bail!("Invalid types for not_equals: {:?} and {:?}", self, other),
            Err(e) => Err(e),
        }
    }

    pub fn greater(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self, other) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs > rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs > rhs),
            (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs > rhs),
            (Value::String(lhs), Value::String(rhs)) => Value::Bool(lhs > rhs),
            (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs > rhs),
            (Value::Bytes(lhs), Value::Bytes(rhs)) => Value::Bool(lhs > rhs),
            (Value::Timestamp(t1), Value::Timestamp(t2)) => Value::Bool(t1 > t2),
            (Value::Duration(d1), Value::Duration(d2)) => Value::Bool(d1 > d2),
            (left, right) => miette::bail!("Cannot compare {:?} and {:?}", left, right),
        };

        Ok(v)
    }

    pub fn greater_equal(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self, other) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs >= rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs >= rhs),
            (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs >= rhs),
            (Value::String(lhs), Value::String(rhs)) => Value::Bool(lhs >= rhs),
            (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs >= rhs),
            (Value::Bytes(lhs), Value::Bytes(rhs)) => Value::Bool(lhs >= rhs),
            (Value::Timestamp(t1), Value::Timestamp(t2)) => Value::Bool(t1 >= t2),
            (Value::Duration(d1), Value::Duration(d2)) => Value::Bool(d1 >= d2),
            _ => miette::bail!("Failed to compare {self:?} >= {other:?}"),
        };

        Ok(v)
    }

    pub fn less(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self, other) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs < rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs < rhs),
            (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs < rhs),
            (Value::String(lhs), Value::String(rhs)) => Value::Bool(lhs < rhs),
            (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs < rhs),
            (Value::Bytes(lhs), Value::Bytes(rhs)) => Value::Bool(lhs < rhs),
            (Value::Timestamp(t1), Value::Timestamp(t2)) => Value::Bool(t1 < t2),
            (Value::Duration(d1), Value::Duration(d2)) => Value::Bool(d1 < d2),
            _ => miette::bail!("Failed to compare {self:?} < {other:?}"),
        };

        Ok(v)
    }

    pub fn less_equal(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self, other) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs <= rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Bool(lhs <= rhs),
            (Value::Double(lhs), Value::Double(rhs)) => Value::Bool(lhs <= rhs),
            (Value::String(lhs), Value::String(rhs)) => Value::Bool(lhs <= rhs),
            (Value::Bool(lhs), Value::Bool(rhs)) => Value::Bool(lhs <= rhs),
            (Value::Bytes(lhs), Value::Bytes(rhs)) => Value::Bool(lhs <= rhs),
            (Value::Timestamp(t1), Value::Timestamp(t2)) => Value::Bool(t1 <= t2),
            (Value::Duration(d1), Value::Duration(d2)) => Value::Bool(d1 <= d2),
            _ => miette::bail!("Failed to compare {self:?} <= {other:?}"),
        };

        Ok(v)
    }

    pub fn multiply(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self, other) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs * rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs * rhs),
            (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs * rhs),
            _ => miette::bail!("Failed to multiply {self:?} * {other:?}"),
        };

        Ok(v)
    }

    pub fn devide(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self, other) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs / rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs / rhs),
            (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs / rhs),
            _ => miette::bail!("Failed to devide {self:?} / {other:?}"),
        };

        Ok(v)
    }

    pub fn reminder(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self, other) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs % rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs % rhs),
            _ => miette::bail!("Failed to get reminder {self:?} % {other:?}"),
        };

        Ok(v)
    }
}

impl Serialize for Value {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Value::Int(n) => serializer.serialize_i64(*n),
            Value::Uint(n) => serializer.serialize_u64(*n),
            Value::Double(n) => serializer.serialize_f64(*n),
            Value::String(s) => serializer.serialize_str(s),
            Value::Bool(b) => serializer.serialize_bool(*b),
            Value::Map(map) => map.serialize(serializer),
            Value::List(list) => list.serialize(serializer),
            Value::Bytes(b) => serializer.serialize_bytes(b),
            Value::Null => serializer.serialize_none(),
            Value::Timestamp(t) => time::serde::iso8601::serialize(t, serializer),
            Value::Duration(d) => serializer.serialize_str(&d.to_string()),
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

    pub fn element_type(&self) -> Option<ValueKind> {
        self.elem_type.clone()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Value> {
        self.inner.iter()
    }

    pub fn with_type(elem_type: ValueKind) -> Self {
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

    pub fn append(&mut self, other: &mut List) -> Result<&mut Self, Error> {
        if let Some(ref elem_type) = self.elem_type {
            if let Some(ref other_elem_type) = other.elem_type {
                if *elem_type != *other_elem_type {
                    miette::bail!(
                        "Invalid element type: {:?} and {:?}",
                        elem_type,
                        other_elem_type
                    );
                }
            }
        } else {
            self.elem_type = other.elem_type.take();
        }

        self.inner.append(&mut other.inner);
        Ok(self)
    }

    pub fn push(&mut self, value: Value) -> Result<&mut Self, Error> {
        self.prepare_insert(&value)?;
        self.inner.push(value);
        Ok(self)
    }

    pub fn drain<R>(&mut self, range: R) -> vec::Drain<'_, Value>
    where
        R: std::ops::RangeBounds<usize>,
    {
        self.inner.drain(range)
    }

    pub fn as_mut_ptr(&mut self) -> *mut Value {
        self.inner.as_mut_ptr()
    }

    pub fn as_mut_slice(&mut self) -> &mut [Value] {
        self.inner.as_mut_slice()
    }

    pub fn as_ptr(&self) -> *const Value {
        self.inner.as_ptr()
    }

    pub fn as_slice(&self) -> &[Value] {
        self.inner.as_slice()
    }

    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    pub fn clear(&mut self) {
        self.inner.clear();
    }

    pub fn dedup(&mut self) {
        self.inner.dedup()
    }

    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut Value, &mut Value) -> bool,
    {
        self.inner.dedup_by(same_bucket)
    }

    pub fn dedup_by_key<F, K>(&mut self, key: F)
    where
        F: FnMut(&mut Value) -> K,
        K: PartialEq<K>,
    {
        self.inner.dedup_by_key(key)
    }

    pub fn extend_from_slice(&mut self, other: &[Value]) -> Result<(), Error> {
        if other.is_empty() {
            return Ok(());
        }

        other.iter().try_for_each(|v| self.prepare_insert(v))?;
        self.inner.extend_from_slice(other);
        Ok(())
    }

    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: std::ops::RangeBounds<usize>,
    {
        self.inner.extend_from_within(src);
    }

    pub fn insert(&mut self, index: usize, element: Value) {
        self.prepare_insert(&element).unwrap();
        self.inner.insert(index, element)
    }

    pub fn into_boxed_slice(self) -> Box<[Value]> {
        self.inner.into_boxed_slice()
    }

    pub fn leak<'a>(self) -> &'a [Value] {
        self.inner.leak()
    }

    pub fn pop(&mut self) -> Option<Value> {
        self.inner.pop()
    }

    pub fn remove(&mut self, index: usize) -> Value {
        self.inner.remove(index)
    }

    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    pub fn resize(&mut self, new_len: usize, value: Value) {
        self.prepare_insert(&value).unwrap();
        self.inner.resize(new_len, value)
    }

    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> Value,
    {
        self.inner.resize_with(new_len, f)
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Value) -> bool,
    {
        self.inner.retain(|v| f(v))
    }

    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Value) -> bool,
    {
        self.inner.retain_mut(|v| f(v))
    }

    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity)
    }

    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

    pub fn split_off(&mut self, at: usize) -> List {
        List {
            elem_type: self.elem_type.clone(),
            inner: self.inner.split_off(at),
        }
    }

    pub fn swap_remove(&mut self, index: usize) -> Value {
        self.inner.swap_remove(index)
    }

    pub fn truncate(&mut self, len: usize) {
        self.inner.truncate(len)
    }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), Error> {
        match self.inner.try_reserve(additional) {
            Ok(_) => Ok(()),
            Err(e) => miette::bail!(e),
        }
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), Error> {
        match self.inner.try_reserve_exact(additional) {
            Ok(_) => Ok(()),
            Err(e) => miette::bail!(e),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            elem_type: None,
            inner: Vec::with_capacity(capacity),
        }
    }

    pub fn with_type_and_capacity(elem_type: ValueKind, capacity: usize) -> Self {
        Self {
            elem_type: Some(elem_type),
            inner: Vec::with_capacity(capacity),
        }
    }

    fn prepare_insert(&mut self, other: &Value) -> Result<(), Error> {
        match self.elem_type {
            None => {
                self.elem_type = Some(other.kind());
            }
            Some(ref elem_type) => {
                if *elem_type != other.kind() {
                    miette::bail!("Invalid element type: {:?}", other.kind());
                }
            }
        }
        Ok(())
    }
}

impl Default for List {
    fn default() -> Self {
        Self::new()
    }
}

impl Serialize for List {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.inner.serialize(serializer)
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
    Timestamp,
    Duration,
    Null,
}

#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub enum KeyKind {
    Int,
    Uint,
    String,
    Bool,
}

impl TryFrom<ValueKind> for KeyKind {
    type Error = Error;

    fn try_from(kind: ValueKind) -> Result<Self, Self::Error> {
        match kind {
            ValueKind::Int => Ok(KeyKind::Int),
            ValueKind::Uint => Ok(KeyKind::Uint),
            ValueKind::String => Ok(KeyKind::String),
            ValueKind::Bool => Ok(KeyKind::Bool),
            _ => miette::bail!("Invalid map key kind: {:?}", kind),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Serialize, Deserialize)]
#[serde(untagged)]
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
            _ => miette::bail!("Invalid map key: {:?}", value),
        }
    }
}

impl Key {
    fn kind(&self) -> KeyKind {
        match self {
            Key::Int(_) => KeyKind::Int,
            Key::Uint(_) => KeyKind::Uint,
            Key::String(_) => KeyKind::String,
            Key::Bool(_) => KeyKind::Bool,
        }
    }
}

impl fmt::Display for Key {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Key::Int(n) => write!(f, "{n}"),
            Key::Uint(n) => write!(f, "{n}"),
            Key::String(s) => write!(f, "{s}"),
            Key::Bool(b) => write!(f, "{b}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deserialize_map() {
        let map = Map::from(serde_json::json!({
            "a": 1,
            "b": 2,
            "c": 3,
        }));

        assert_eq!(map.len(), 3);
        assert_eq!(
            map.get(&Key::String("a".to_string())).unwrap().unwrap(),
            &Value::Int(1)
        );
        assert_eq!(
            map.get(&Key::String("b".to_string())).unwrap().unwrap(),
            &Value::Int(2)
        );
        assert_eq!(
            map.get(&Key::String("c".to_string())).unwrap().unwrap(),
            &Value::Int(3)
        );
    }
}
