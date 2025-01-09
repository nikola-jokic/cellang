use super::{TryIntoValue, Value, ValueType};
use miette::Error;
use serde::de::DeserializeOwned;
use serde::Deserializer;
use serde::{ser::Serializer, Deserialize, Serialize};
use std::collections::hash_map::{
    self, Entry, IntoIter, IntoKeys, IntoValues, Iter, IterMut, Keys,
    RandomState, Values, ValuesMut,
};
use std::collections::HashMap;
use std::fmt;

/// Map is a wrapper around HashMap with additional type checking.
#[derive(Debug, PartialEq, Clone)]
pub struct Map {
    key_type: Option<KeyType>,
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

impl Map {
    /// The new returns a map with no key type and no elements.
    pub fn new() -> Self {
        Self {
            key_type: None,
            inner: HashMap::new(),
        }
    }

    #[inline]
    pub fn inner(&self) -> &HashMap<Key, Value> {
        &self.inner
    }

    #[inline]
    pub fn try_into<T>(self) -> Result<T, Error>
    where
        T: DeserializeOwned,
    {
        crate::try_from_map(self)
    }

    #[inline]
    pub fn key_type(&self) -> Option<KeyType> {
        self.key_type
    }

    #[inline]
    pub fn with_key_type(key_type: KeyType) -> Self {
        Self {
            key_type: Some(key_type),
            inner: HashMap::new(),
        }
    }

    #[inline]
    pub fn with_key_type_and_capacity(
        key_type: KeyType,
        capacity: usize,
    ) -> Self {
        Self {
            key_type: Some(key_type),
            inner: HashMap::with_capacity(capacity),
        }
    }

    /// Wrapper for [capacity](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.capacity)
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Wrapper for [clear](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.clear)
    /// It doesn't clear the key type.
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Wrapper for [contains_key](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.contains_key)
    /// It checks if the key type is the same as the key type.
    /// If the key type is not set (map must be empty), it returns false.
    #[inline]
    pub fn contains_key(&self, key: &Key) -> Result<bool, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.type_of() {
                miette::bail!("Invalid key type: {:?}", key.type_of());
            }

            Ok(self.inner.contains_key(key))
        } else {
            Ok(false)
        }
    }

    /// Wrapper for [drain](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.drain)
    #[inline]
    pub fn drain(&mut self) -> hash_map::Drain<'_, Key, Value> {
        self.inner.drain()
    }

    /// Wrapper for [entry](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.entry)
    /// It checks if the key type is the same as the key type.
    /// If the key type is not set (map must be empty), it sets the key type.
    #[inline]
    pub fn entry(&mut self, key: Key) -> Result<Entry<Key, Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.type_of() {
                miette::bail!("Invalid key type: {:?}", key.type_of());
            }
        } else {
            self.key_type = Some(key.type_of());
        }

        Ok(self.inner.entry(key))
    }

    /// Wrapper for [get](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve)
    #[inline]
    pub fn get(&self, key: &Key) -> Result<Option<&Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.type_of() {
                miette::bail!("Invalid key type: {:?}", key.type_of());
            }

            Ok(self.inner.get(key))
        } else {
            Ok(None)
        }
    }

    /// Wrapper for [get_key_value](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get_key_value)
    #[inline]
    pub fn get_key_value(
        &self,
        key: &Key,
    ) -> Result<Option<(&Key, &Value)>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.type_of() {
                miette::bail!("Invalid key type: {:?}", key.type_of());
            }

            Ok(self.inner.get_key_value(key))
        } else {
            Ok(None)
        }
    }

    /// Wrapper for [get_mut](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get_mut)
    #[inline]
    pub fn get_mut(&mut self, key: &Key) -> Result<Option<&mut Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.type_of() {
                miette::bail!("Invalid key type: {:?}", key.type_of());
            }

            Ok(self.inner.get_mut(key))
        } else {
            Ok(None)
        }
    }

    /// Wrapper for [hasher](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.hasher)
    #[inline]
    pub fn hasher(&self) -> &RandomState {
        self.inner.hasher()
    }

    /// Wrapper for [insert](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.insert)
    #[inline]
    pub fn insert(
        &mut self,
        key: Key,
        value: Value,
    ) -> Result<&mut Self, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.type_of() {
                miette::bail!("Invalid key type: {:?}", key.type_of());
            }
        } else {
            self.key_type = Some(key.type_of());
        }

        self.inner.insert(key, value);
        Ok(self)
    }

    /// Wrapper for [into_keys](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.into_keys)
    #[inline]
    pub fn into_keys(self) -> IntoKeys<Key, Value> {
        self.inner.into_keys()
    }

    /// Wrapper for [into_values](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.into_values)
    #[inline]
    pub fn into_values(self) -> IntoValues<Key, Value> {
        self.inner.into_values()
    }

    /// Wrapper for [is_empty](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.is_empty)
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Wrapper for [iter](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.iter)
    #[inline]
    pub fn iter(&self) -> Iter<'_, Key, Value> {
        self.inner.iter()
    }

    /// Wrapper for [iter_mut](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.iter_mut)
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, Key, Value> {
        self.inner.iter_mut()
    }

    /// Wrapper for [keys](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.keys)
    #[inline]
    pub fn keys(&self) -> Keys<'_, Key, Value> {
        self.inner.keys()
    }

    /// Wrapper for [len](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.len)
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Wrapper for [remove](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove)
    #[inline]
    pub fn remove(&mut self, key: &Key) -> Result<Option<Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.type_of() {
                miette::bail!("Invalid key type: {:?}", key.type_of());
            }
        } else {
            self.key_type = Some(key.type_of());
        }

        Ok(self.inner.remove(key))
    }

    /// Wrapper for [reserve](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve)
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Wrapper for [retain](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.retain)
    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&Key, &mut Value) -> bool,
    {
        self.inner.retain(f)
    }

    /// Wrapper for [shrink_to](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.shrink_to)
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity)
    }

    /// Wrapper for [shrink_to_fit](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.shrink_to_fit)
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

    /// Wrapper for [try_insert](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.try_insert)
    #[inline]
    pub fn try_insert(
        &mut self,
        key: Key,
        value: Value,
    ) -> Result<Option<Value>, Error> {
        if let Some(ref key_type) = self.key_type {
            if *key_type != key.type_of() {
                miette::bail!("Invalid key type: {:?}", key.type_of());
            }
        } else {
            self.key_type = Some(key.type_of());
        }

        Ok(self.inner.insert(key, value))
    }

    /// Wrapper for [try_reserve](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.try_reserve)
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), Error> {
        match self.inner.try_reserve(additional) {
            Ok(_) => Ok(()),
            Err(e) => miette::bail!(e),
        }
    }

    /// Wrapper for
    /// [values](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.values)
    #[inline]
    pub fn values(&self) -> Values<'_, Key, Value> {
        self.inner.values()
    }

    /// Wrapper for [values_mut](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.values_mut)
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, Key, Value> {
        self.inner.values_mut()
    }

    /// Wrapper for [with_capacity](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity)
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            key_type: None,
            inner: HashMap::with_capacity(capacity),
        }
    }

    /// Adds key type and instantiates an inner hashmap with the capacity provided as the argument.
    #[inline]
    pub fn with_type_and_capacity(key_type: KeyType, capacity: usize) -> Self {
        Self {
            key_type: Some(key_type),
            inner: HashMap::with_capacity(capacity),
        }
    }

    /// Wrapper for [with_capacity_and_hasher](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity_and_hasher)
    #[inline]
    pub fn with_capacity_and_hasher(
        capacity: usize,
        hash_builder: RandomState,
    ) -> Self {
        Self {
            key_type: None,
            inner: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    /// Creates new inner hashmap and sets the map type for type checking.
    #[inline]
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

    /// Wrapper for [with_hasher](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_hasher)
    #[inline]
    pub fn with_hasher(hash_builder: RandomState) -> Self {
        Self {
            key_type: None,
            inner: HashMap::with_hasher(hash_builder),
        }
    }

    /// Creates new inner hashmap and sets the map type for type checking.
    #[inline]
    pub fn with_type_and_hasher(
        key_type: KeyType,
        hash_builder: RandomState,
    ) -> Self {
        Self {
            key_type: Some(key_type),
            inner: HashMap::with_hasher(hash_builder),
        }
    }
}

impl<K, V> TryFrom<HashMap<K, V>> for Map
where
    K: Into<Key>,
    V: TryIntoValue,
{
    type Error = Error;
    fn try_from(inner: HashMap<K, V>) -> Result<Self, Error> {
        if inner.is_empty() {
            Ok(Self::new())
        } else {
            let mut map = Map::new();
            for (k, v) in inner {
                map.insert(
                    k.into(),
                    v.try_into_value().map_err(|err| {
                        miette::miette!("Failed to convert to value: {err:?}")
                    })?,
                )
                .unwrap();
            }
            Ok(map)
        }
    }
}

impl From<Map> for HashMap<Key, Value> {
    fn from(map: Map) -> Self {
        map.inner
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

impl IntoIterator for Map {
    type Item = (Key, Value);
    type IntoIter = IntoIter<Key, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
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

impl<'de> Deserialize<'de> for Map {
    fn deserialize<D>(deserializer: D) -> Result<Map, D::Error>
    where
        D: Deserializer<'de>,
    {
        let inner = HashMap::<Key, Value>::deserialize(deserializer)?;
        Map::try_from(inner).map_err(serde::de::Error::custom)
    }
}

/// KeyType represents the type of the key.
#[derive(Copy, Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub enum KeyType {
    Int,
    Uint,
    String,
    Bool,
}

impl From<Key> for KeyType {
    fn from(key: Key) -> Self {
        key.type_of()
    }
}

impl TryFrom<ValueType> for KeyType {
    type Error = Error;

    fn try_from(ty: ValueType) -> Result<Self, Self::Error> {
        match ty {
            ValueType::Int => Ok(KeyType::Int),
            ValueType::Uint => Ok(KeyType::Uint),
            ValueType::String => Ok(KeyType::String),
            ValueType::Bool => Ok(KeyType::Bool),
            ty => miette::bail!("Invalid map key kind: {ty:?}"),
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

impl From<String> for Key {
    fn from(value: String) -> Self {
        Key::String(value)
    }
}

impl From<i64> for Key {
    fn from(value: i64) -> Self {
        Key::Int(value)
    }
}

impl From<u64> for Key {
    fn from(value: u64) -> Self {
        Key::Uint(value)
    }
}

impl From<bool> for Key {
    fn from(value: bool) -> Self {
        Key::Bool(value)
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

impl TryFrom<&Value> for Key {
    type Error = Error;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        match value {
            Value::Int(n) => Ok(Key::Int(*n)),
            Value::Uint(n) => Ok(Key::Uint(*n)),
            Value::String(s) => Ok(Key::String(s.clone())),
            Value::Bool(b) => Ok(Key::Bool(*b)),
            _ => miette::bail!("Invalid map key: {:?}", value),
        }
    }
}

impl From<Key> for Value {
    fn from(key: Key) -> Self {
        match key {
            Key::Int(n) => Value::Int(n),
            Key::Uint(n) => Value::Uint(n),
            Key::String(s) => Value::String(s),
            Key::Bool(b) => Value::Bool(b),
        }
    }
}

impl From<&Key> for Value {
    fn from(key: &Key) -> Self {
        match key {
            Key::Int(n) => Value::Int(*n),
            Key::Uint(n) => Value::Uint(*n),
            Key::String(s) => Value::String(s.clone()),
            Key::Bool(b) => Value::Bool(*b),
        }
    }
}

impl Key {
    fn type_of(&self) -> KeyType {
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
            Key::Int(n) => write!(f, "{n}"),
            Key::Uint(n) => write!(f, "{n}"),
            Key::String(s) => write!(f, "{s}"),
            Key::Bool(b) => write!(f, "{b}"),
        }
    }
}
