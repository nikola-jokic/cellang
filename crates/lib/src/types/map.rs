use super::{Value, ValueKind};
use miette::Error;
use serde::Deserializer;
use serde::{ser::Serializer, Deserialize, Serialize};
use std::collections::hash_map::{self, Entry, IntoValues, Iter, IterMut, Keys, RandomState};
use std::collections::HashMap;
use std::fmt;

/// Map is a wrapper around HashMap with additional type checking.
#[derive(Debug, PartialEq, Clone)]
pub struct Map {
    key_type: Option<KeyKind>,
    inner: HashMap<Key, Value>,
}

impl fmt::Display for Map {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (key, value)) in self.inner.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", key, value)?;
        }
        write!(f, "}}")
    }
}

impl Default for Map {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> From<HashMap<K, V>> for Map
where
    K: Into<Key>,
    V: Into<Value>,
{
    fn from(inner: HashMap<K, V>) -> Self {
        if inner.is_empty() {
            Self::new()
        } else {
            let mut map = Map::new();
            for (k, v) in inner {
                map.insert(k.into(), v.into()).unwrap();
            }
            map
        }
    }
}

impl FromIterator<(Key, Value)> for Map {
    fn from_iter<T: IntoIterator<Item = (Key, Value)>>(iter: T) -> Self {
        let mut map = Map::new();
        for (k, v) in iter {
            map.insert(k, v).unwrap();
        }
        map
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

    /// Wrapper for [capacity](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.capacity)
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Wrapper for [clear](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.clear)
    /// It doesn't clear the key type.
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Wrapper for [contains_key](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.contains_key)
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

    /// Wrapper for [drain](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.drain)
    pub fn drain(&mut self) -> hash_map::Drain<'_, Key, Value> {
        self.inner.drain()
    }

    /// Wrapper for [entry](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.entry)
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

    /// Wrapper for [get](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve)
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

    /// Wrapper for [get_key_value](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get_key_value)
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

    /// Wrapper for [get_mut](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get_mut)
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

    /// Wrapper for [hasher](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.hasher)
    pub fn hasher(&self) -> &RandomState {
        self.inner.hasher()
    }

    /// Wrapper for [insert](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.insert)
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

    /// Wrapper for [into_keys](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.into_keys)
    pub fn into_keys(self) -> impl Iterator<Item = Key> {
        self.inner.into_keys()
    }

    /// Wrapper for [into_values](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.into_values)
    pub fn into_values(self) -> IntoValues<Key, Value> {
        self.inner.into_values()
    }

    /// Wrapper for [is_empty](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.is_empty)
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Wrapper for [iter](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.iter)
    pub fn iter(&self) -> Iter<'_, Key, Value> {
        self.inner.iter()
    }

    /// Wrapper for [iter_mut](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.iter_mut)
    pub fn iter_mut(&mut self) -> IterMut<'_, Key, Value> {
        self.inner.iter_mut()
    }

    /// Wrapper for [keys](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.keys)
    pub fn keys(&self) -> Keys<'_, Key, Value> {
        self.inner.keys()
    }

    /// Wrapper for [len](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.len)
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Wrapper for [remove](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove)
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

    /// Wrapper for [reserve](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve)
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Wrapper for [retain](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.retain)
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&Key, &mut Value) -> bool,
    {
        self.inner.retain(f)
    }

    /// Wrapper for [shrink_to](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.shrink_to)
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity)
    }

    /// Wrapper for [shrink_to_fit](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.shrink_to_fit)
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

    /// Wrapper for [try_insert](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.try_insert)
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

    /// Wrapper for [try_reserve](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.try_reserve)
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), Error> {
        match self.inner.try_reserve(additional) {
            Ok(_) => Ok(()),
            Err(e) => miette::bail!(e),
        }
    }

    /// Wrapper for [values](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.values)
    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.inner.values()
    }

    /// Wrapper for [values_mut](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.values_mut)
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut Value> {
        self.inner.values_mut()
    }

    /// Wrapper for [with_capacity](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity)
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            key_type: None,
            inner: HashMap::with_capacity(capacity),
        }
    }

    /// Adds key type and instantiates an inner hashmap with the capacity provided as the argument.
    pub fn with_type_and_capacity(key_type: KeyKind, capacity: usize) -> Self {
        Self {
            key_type: Some(key_type),
            inner: HashMap::with_capacity(capacity),
        }
    }

    /// Wrapper for [with_capacity_and_hasher](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity_and_hasher)
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: RandomState) -> Self {
        Self {
            key_type: None,
            inner: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    /// Creates new inner hashmap and sets the map type for type checking.
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

    /// Wrapper for [with_hasher](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_hasher)
    pub fn with_hasher(hash_builder: RandomState) -> Self {
        Self {
            key_type: None,
            inner: HashMap::with_hasher(hash_builder),
        }
    }

    /// Creates new inner hashmap and sets the map type for type checking.
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

/// KeyKind represents the type of the key.
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub enum KeyKind {
    Int,
    Uint,
    String,
    Bool,
}

impl From<Key> for KeyKind {
    fn from(key: Key) -> Self {
        key.kind()
    }
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

/// Key represents the key of the map. It has a variant for each key type and holds the value.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Key {
    Int(i64),
    Uint(u64),
    String(String),
    Bool(bool),
}

impl From<&str> for Key {
    fn from(value: &str) -> Self {
        Key::String(value.to_string())
    }
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

macro_rules! impl_owned_key_conversions {
    ($($target_type: ty => $value_variant:path),* $(,)?) => {
        $(
            impl From<$target_type> for Key {
                fn from(value: $target_type) -> Self {
                    $value_variant(value)
                }
            }

            impl From<Key> for $target_type {
                fn from(value: Key) -> Self {
                    match value {
                        $value_variant(v) => v,
                        _ => panic!("Invalid conversion from {:?} to {:?}", value, stringify!($target_type)),
                    }
                }
            }
        )*
    }
}

impl_owned_key_conversions! {
    i64 => Key::Int,
    u64 => Key::Uint,
    String => Key::String,
    bool => Key::Bool,
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
        assert_eq!(map.get(&Key::from("a")).unwrap().unwrap(), &Value::Int(1));
        assert_eq!(map.get(&Key::from("b")).unwrap().unwrap(), &Value::Int(2));
        assert_eq!(map.get(&Key::from("c")).unwrap().unwrap(), &Value::Int(3));
    }
}
