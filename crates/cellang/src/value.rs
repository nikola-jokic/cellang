use crate::types::{Constant, Type, TypeName};
use base64::Engine;
use base64::engine::general_purpose::STANDARD;
use serde::Serialize;
use serde::ser::{SerializeMap, SerializeSeq};
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use thiserror::Error;
use time::{Duration, OffsetDateTime};

/// Primary runtime value for CEL expressions.
#[derive(Clone, Debug, PartialEq, Default)]
pub enum Value {
    Bool(bool),
    Int(i64),
    Uint(u64),
    Double(f64),
    String(String),
    Bytes(Vec<u8>),
    Timestamp(OffsetDateTime),
    Duration(Duration),
    List(ListValue),
    Map(MapValue),
    Struct(StructValue),
    #[default]
    Null,
}

/// Alias preserving the historical naming used by older versions of the crate.
pub type List = ListValue;
/// Alias preserving the historical naming used by older versions of the crate.
pub type Map = MapValue;
/// Alias preserving the historical naming used by older versions of the crate.
pub type Struct = StructValue;

impl Value {
    pub fn kind(&self) -> ValueKind {
        match self {
            Value::Bool(_) => ValueKind::Bool,
            Value::Int(_) => ValueKind::Int,
            Value::Uint(_) => ValueKind::Uint,
            Value::Double(_) => ValueKind::Double,
            Value::String(_) => ValueKind::String,
            Value::Bytes(_) => ValueKind::Bytes,
            Value::Timestamp(_) => ValueKind::Timestamp,
            Value::Duration(_) => ValueKind::Duration,
            Value::List(_) => ValueKind::List,
            Value::Map(_) => ValueKind::Map,
            Value::Struct(_) => ValueKind::Struct,
            Value::Null => ValueKind::Null,
        }
    }

    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }

    pub fn cel_type(&self) -> Type {
        match self {
            Value::Bool(_) => Type::Bool,
            Value::Int(_) => Type::Int,
            Value::Uint(_) => Type::Uint,
            Value::Double(_) => Type::Double,
            Value::String(_) => Type::String,
            Value::Bytes(_) => Type::Bytes,
            Value::Timestamp(_) => Type::Timestamp,
            Value::Duration(_) => Type::Duration,
            Value::Null => Type::Null,
            Value::Struct(value) => Type::struct_type(value.type_name.clone()),
            Value::List(list) => {
                let element_ty = list
                    .iter()
                    .map(|value| value.cel_type())
                    .reduce(
                        |left, right| {
                            if left == right { left } else { Type::Dyn }
                        },
                    )
                    .unwrap_or(Type::Dyn);
                Type::list(element_ty)
            }
            Value::Map(map) => {
                let (key_ty, value_ty) = map.type_projection();
                Type::map(key_ty, value_ty)
            }
        }
    }

    pub fn try_as<T: TryFromValue>(&self) -> Result<T, ValueError> {
        T::try_from_value(self)
    }

    pub fn try_into<T: TryFromValue>(self) -> Result<T, ValueError> {
        T::try_from_value(&self)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(v) => write!(f, "{v}"),
            Value::Int(v) => write!(f, "{v}"),
            Value::Uint(v) => write!(f, "{v}u"),
            Value::Double(v) => write!(f, "{v}"),
            Value::String(v) => write!(f, "\"{v}\""),
            Value::Bytes(v) => write!(f, "b\"{}\"", STANDARD.encode(v)),
            Value::Timestamp(ts) => write!(f, "{ts}"),
            Value::Duration(dur) => write!(f, "{dur}"),
            Value::List(list) => {
                write!(f, "[")?;
                for (idx, item) in list.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{item}")?;
                }
                write!(f, "]")
            }
            Value::Map(map) => {
                write!(f, "{{")?;
                for (idx, (key, value)) in map.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{key}: {value}")?;
                }
                write!(f, "}}")
            }
            Value::Struct(strct) => {
                write!(f, "{} {{", strct.type_name)?;
                for (idx, (field, value)) in strct.fields.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{field}: {value}")?;
                }
                write!(f, "}}")
            }
            Value::Null => write!(f, "null"),
        }
    }
}

impl Serialize for Value {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Value::Bool(v) => serializer.serialize_bool(*v),
            Value::Int(v) => serializer.serialize_i64(*v),
            Value::Uint(v) => serializer.serialize_u64(*v),
            Value::Double(v) => serializer.serialize_f64(*v),
            Value::String(v) => serializer.serialize_str(v),
            Value::Bytes(v) => serializer.serialize_bytes(v),
            Value::Timestamp(v) => serializer.serialize_str(&v.to_string()),
            Value::Duration(v) => serializer.serialize_str(&format!("{v}")),
            Value::Null => serializer.serialize_unit(),
            Value::List(v) => v.serialize(serializer),
            Value::Map(v) => v.serialize(serializer),
            Value::Struct(v) => v.serialize(serializer),
        }
    }
}

impl From<&Constant> for Value {
    fn from(value: &Constant) -> Self {
        match value {
            Constant::Bool(v) => Value::Bool(*v),
            Constant::Int(v) => Value::Int(*v),
            Constant::Uint(v) => Value::Uint(*v),
            Constant::Double(v) => Value::Double(*v),
            Constant::String(v) => Value::String(v.clone()),
            Constant::Bytes(v) => Value::Bytes(v.clone()),
            Constant::Null => Value::Null,
        }
    }
}

/// Wrapper around a CEL list value.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ListValue {
    items: Vec<Value>,
}

impl ListValue {
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn push<V: IntoValue>(&mut self, value: V) {
        self.items.push(value.into_value());
    }

    pub fn get(&self, index: usize) -> Option<&Value> {
        self.items.get(index)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Value> {
        self.items.iter()
    }

    pub fn into_vec(self) -> Vec<Value> {
        self.items
    }
}

impl<T> From<Vec<T>> for ListValue
where
    T: IntoValue,
{
    fn from(value: Vec<T>) -> Self {
        let items = value.into_iter().map(|item| item.into_value()).collect();
        ListValue { items }
    }
}

impl IntoIterator for ListValue {
    type Item = Value;
    type IntoIter = std::vec::IntoIter<Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.into_iter()
    }
}

impl Serialize for ListValue {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.items.len()))?;
        for value in &self.items {
            seq.serialize_element(value)?;
        }
        seq.end()
    }
}

/// Wrapper around a CEL map value.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct MapValue {
    entries: BTreeMap<Key, Value>,
}

impl MapValue {
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn insert<K, V>(&mut self, key: K, value: V)
    where
        K: Into<Key>,
        V: IntoValue,
    {
        self.entries.insert(key.into(), value.into_value());
    }

    pub fn get_by_key(&self, key: &Key) -> Option<&Value> {
        self.entries.get(key)
    }

    pub fn get_str(&self, key: &str) -> Option<&Value> {
        self.entries.get(&Key::from(key))
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Key, &Value)> {
        self.entries.iter()
    }

    pub fn contains_key(&self, key: &Key) -> bool {
        self.entries.contains_key(key)
    }

    pub fn type_projection(&self) -> (Type, Type) {
        let key_ty = self
            .entries
            .keys()
            .map(Key::cel_type)
            .reduce(|left, right| if left == right { left } else { Type::Dyn })
            .unwrap_or(Type::Dyn);
        let value_ty = self
            .entries
            .values()
            .map(Value::cel_type)
            .reduce(|left, right| if left == right { left } else { Type::Dyn })
            .unwrap_or(Type::Dyn);
        (key_ty, value_ty)
    }
}

impl<K, V> From<BTreeMap<K, V>> for MapValue
where
    K: Into<Key>,
    V: IntoValue,
{
    fn from(value: BTreeMap<K, V>) -> Self {
        let mut map = MapValue::new();
        for (key, val) in value {
            map.insert(key.into(), val);
        }
        map
    }
}

impl IntoIterator for MapValue {
    type Item = (Key, Value);
    type IntoIter = std::collections::btree_map::IntoIter<Key, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}

impl Serialize for MapValue {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.entries.len()))?;
        for (key, value) in &self.entries {
            map.serialize_entry(key, value)?;
        }
        map.end()
    }
}

/// Runtime struct/message representation.
#[derive(Clone, Debug, PartialEq)]
pub struct StructValue {
    pub type_name: TypeName,
    pub fields: BTreeMap<String, Value>,
}

impl StructValue {
    pub fn new(name: impl Into<TypeName>) -> Self {
        StructValue {
            type_name: name.into(),
            fields: BTreeMap::new(),
        }
    }

    pub fn with_fields(
        name: impl Into<TypeName>,
        fields: impl IntoIterator<Item = (String, Value)>,
    ) -> Self {
        StructValue {
            type_name: name.into(),
            fields: fields.into_iter().collect::<BTreeMap<_, _>>(),
        }
    }

    pub fn set_field<K, V>(&mut self, name: K, value: V)
    where
        K: Into<String>,
        V: IntoValue,
    {
        self.fields.insert(name.into(), value.into_value());
    }

    pub fn get(&self, name: &str) -> Option<&Value> {
        self.fields.get(name)
    }
}

impl Serialize for StructValue {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_map(Some(self.fields.len()))?;
        for (name, value) in &self.fields {
            state.serialize_entry(name, value)?;
        }
        state.end()
    }
}

/// Supported CEL map keys.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Key {
    Bool(bool),
    Int(i64),
    Uint(u64),
    String(String),
    Bytes(Vec<u8>),
}

impl Key {
    pub fn cel_type(&self) -> Type {
        match self {
            Key::Bool(_) => Type::Bool,
            Key::Int(_) => Type::Int,
            Key::Uint(_) => Type::Uint,
            Key::String(_) => Type::String,
            Key::Bytes(_) => Type::Bytes,
        }
    }
}

impl fmt::Display for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Key::Bool(value) => write!(f, "{value}"),
            Key::Int(value) => write!(f, "{value}"),
            Key::Uint(value) => write!(f, "{value}u"),
            Key::String(value) => write!(f, "{value}"),
            Key::Bytes(value) => write!(f, "b\"{}\"", STANDARD.encode(value)),
        }
    }
}

impl From<&Key> for Value {
    fn from(key: &Key) -> Self {
        match key {
            Key::Bool(value) => Value::Bool(*value),
            Key::Int(value) => Value::Int(*value),
            Key::Uint(value) => Value::Uint(*value),
            Key::String(value) => Value::String(value.clone()),
            Key::Bytes(value) => Value::Bytes(value.clone()),
        }
    }
}

impl From<Key> for Value {
    fn from(key: Key) -> Self {
        Value::from(&key)
    }
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

impl From<bool> for Key {
    fn from(value: bool) -> Self {
        Key::Bool(value)
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

impl From<Vec<u8>> for Key {
    fn from(value: Vec<u8>) -> Self {
        Key::Bytes(value)
    }
}

impl TryFrom<&Value> for Key {
    type Error = ValueError;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        match value {
            Value::Bool(v) => Ok(Key::Bool(*v)),
            Value::Int(v) => Ok(Key::Int(*v)),
            Value::Uint(v) => Ok(Key::Uint(*v)),
            Value::String(v) => Ok(Key::String(v.clone())),
            Value::Bytes(v) => Ok(Key::Bytes(v.clone())),
            _ => Err(ValueError::InvalidMapKey(value.kind())),
        }
    }
}

impl Serialize for Key {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Key::Bool(value) => serializer.serialize_bool(*value),
            Key::Int(value) => serializer.serialize_i64(*value),
            Key::Uint(value) => serializer.serialize_u64(*value),
            Key::String(value) => serializer.serialize_str(value),
            Key::Bytes(value) => serializer.serialize_bytes(value),
        }
    }
}

/// Helper trait used to convert rust values into CEL runtime values.
pub trait IntoValue {
    fn into_value(self) -> Value;
}

impl IntoValue for Value {
    fn into_value(self) -> Value {
        self
    }
}

impl IntoValue for &Value {
    fn into_value(self) -> Value {
        self.clone()
    }
}

impl IntoValue for bool {
    fn into_value(self) -> Value {
        Value::Bool(self)
    }
}

impl IntoValue for i64 {
    fn into_value(self) -> Value {
        Value::Int(self)
    }
}

impl IntoValue for i32 {
    fn into_value(self) -> Value {
        Value::Int(i64::from(self))
    }
}

impl IntoValue for u64 {
    fn into_value(self) -> Value {
        Value::Uint(self)
    }
}

impl IntoValue for u32 {
    fn into_value(self) -> Value {
        Value::Uint(u64::from(self))
    }
}

impl IntoValue for f64 {
    fn into_value(self) -> Value {
        Value::Double(self)
    }
}

impl IntoValue for f32 {
    fn into_value(self) -> Value {
        Value::Double(f64::from(self))
    }
}

impl IntoValue for String {
    fn into_value(self) -> Value {
        Value::String(self)
    }
}

impl IntoValue for &str {
    fn into_value(self) -> Value {
        Value::String(self.to_string())
    }
}

impl IntoValue for Vec<u8> {
    fn into_value(self) -> Value {
        Value::Bytes(self)
    }
}

impl IntoValue for &[u8] {
    fn into_value(self) -> Value {
        Value::Bytes(self.to_vec())
    }
}

impl IntoValue for Duration {
    fn into_value(self) -> Value {
        Value::Duration(self)
    }
}

impl IntoValue for OffsetDateTime {
    fn into_value(self) -> Value {
        Value::Timestamp(self)
    }
}

impl IntoValue for ListValue {
    fn into_value(self) -> Value {
        Value::List(self)
    }
}

impl IntoValue for MapValue {
    fn into_value(self) -> Value {
        Value::Map(self)
    }
}

impl IntoValue for StructValue {
    fn into_value(self) -> Value {
        Value::Struct(self)
    }
}

impl<K, V> IntoValue for BTreeMap<K, V>
where
    K: Into<Key>,
    V: IntoValue,
{
    fn into_value(self) -> Value {
        Value::Map(MapValue::from(self))
    }
}

impl<K, V> IntoValue for HashMap<K, V>
where
    K: Into<Key>,
    V: IntoValue,
{
    fn into_value(self) -> Value {
        let btree_map: BTreeMap<_, _> = self
            .into_iter()
            .map(|(k, v)| (k.into(), v.into_value()))
            .collect();
        Value::Map(MapValue { entries: btree_map })
    }
}

impl<T> IntoValue for Vec<T>
where
    T: IntoValue,
{
    fn into_value(self) -> Value {
        let mut list = ListValue::new();
        for item in self {
            list.push(item);
        }
        Value::List(list)
    }
}

impl<T> IntoValue for Option<T>
where
    T: IntoValue,
{
    fn into_value(self) -> Value {
        match self {
            Some(value) => value.into_value(),
            None => Value::Null,
        }
    }
}

/// Helper trait for converting CEL values into typed rust values.
pub trait TryFromValue: Sized {
    fn try_from_value(value: &Value) -> Result<Self, ValueError>;
}

impl TryFromValue for Value {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        Ok(value.clone())
    }
}

impl TryFromValue for bool {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Bool(v) => Ok(*v),
            _ => Err(ValueError::unexpected("bool", value.kind())),
        }
    }
}

impl TryFromValue for i64 {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Int(v) => Ok(*v),
            _ => Err(ValueError::unexpected("int", value.kind())),
        }
    }
}

impl TryFromValue for u64 {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Uint(v) => Ok(*v),
            _ => Err(ValueError::unexpected("uint", value.kind())),
        }
    }
}

impl TryFromValue for f64 {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Double(v) => Ok(*v),
            Value::Int(v) => Ok(*v as f64),
            Value::Uint(v) => Ok(*v as f64),
            _ => Err(ValueError::unexpected("double", value.kind())),
        }
    }
}

impl TryFromValue for String {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::String(v) => Ok(v.clone()),
            _ => Err(ValueError::unexpected("string", value.kind())),
        }
    }
}

impl TryFromValue for Vec<u8> {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Bytes(v) => Ok(v.clone()),
            _ => Err(ValueError::unexpected("bytes", value.kind())),
        }
    }
}

impl TryFromValue for Duration {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Duration(v) => Ok(*v),
            _ => Err(ValueError::unexpected("duration", value.kind())),
        }
    }
}

impl TryFromValue for OffsetDateTime {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Timestamp(v) => Ok(*v),
            _ => Err(ValueError::unexpected("timestamp", value.kind())),
        }
    }
}

impl TryFromValue for ListValue {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::List(v) => Ok(v.clone()),
            _ => Err(ValueError::unexpected("list", value.kind())),
        }
    }
}

impl TryFromValue for MapValue {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Map(v) => Ok(v.clone()),
            _ => Err(ValueError::unexpected("map", value.kind())),
        }
    }
}

impl TryFromValue for StructValue {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Struct(v) => Ok(v.clone()),
            _ => Err(ValueError::unexpected("struct", value.kind())),
        }
    }
}

impl<T> TryFromValue for Vec<T>
where
    T: TryFromValue,
{
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::List(list) => list
                .iter()
                .map(T::try_from_value)
                .collect::<Result<Vec<_>, _>>(),
            _ => Err(ValueError::unexpected("list", value.kind())),
        }
    }
}

impl<T> TryFromValue for BTreeMap<String, T>
where
    T: TryFromValue,
{
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Map(map) => map
                .iter()
                .map(|(key, value)| match key {
                    Key::String(name) => {
                        let typed = T::try_from_value(value)?;
                        Ok((name.clone(), typed))
                    }
                    _ => Err(ValueError::InvalidMapKey(key.kind())),
                })
                .collect::<Result<BTreeMap<_, _>, _>>(),
            _ => Err(ValueError::unexpected("map", value.kind())),
        }
    }
}

impl<T> TryFromValue for HashMap<String, T>
where
    T: TryFromValue,
{
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        match value {
            Value::Map(map) => map
                .iter()
                .map(|(key, value)| match key {
                    Key::String(name) => {
                        let typed = T::try_from_value(value)?;
                        Ok((name.clone(), typed))
                    }
                    _ => Err(ValueError::InvalidMapKey(key.kind())),
                })
                .collect::<Result<HashMap<_, _>, _>>(),
            _ => Err(ValueError::unexpected("map", value.kind())),
        }
    }
}

impl<T> TryFromValue for Option<T>
where
    T: TryFromValue,
{
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        if value.is_null() {
            Ok(None)
        } else {
            Ok(Some(T::try_from_value(value)?))
        }
    }
}

/// Classification of runtime values used for diagnostics.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ValueKind {
    Null,
    Bool,
    Int,
    Uint,
    Double,
    String,
    Bytes,
    Timestamp,
    Duration,
    List,
    Map,
    Struct,
}

impl fmt::Display for ValueKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ValueKind::Null => "null",
            ValueKind::Bool => "bool",
            ValueKind::Int => "int",
            ValueKind::Uint => "uint",
            ValueKind::Double => "double",
            ValueKind::String => "string",
            ValueKind::Bytes => "bytes",
            ValueKind::Timestamp => "timestamp",
            ValueKind::Duration => "duration",
            ValueKind::List => "list",
            ValueKind::Map => "map",
            ValueKind::Struct => "struct",
        })
    }
}

impl Key {
    fn kind(&self) -> ValueKind {
        match self {
            Key::Bool(_) => ValueKind::Bool,
            Key::Int(_) => ValueKind::Int,
            Key::Uint(_) => ValueKind::Uint,
            Key::String(_) => ValueKind::String,
            Key::Bytes(_) => ValueKind::Bytes,
        }
    }
}

/// Errors that may occur while converting between CEL values and rust values.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum ValueError {
    #[error("expected {expected}, got {actual}")]
    UnexpectedType {
        expected: &'static str,
        actual: ValueKind,
    },
    #[error("unsupported map key type: {0}")]
    InvalidMapKey(ValueKind),
    #[error("index {index} is out of bounds for length {len}")]
    IndexOutOfBounds { index: usize, len: usize },
    #[error("{0}")]
    Message(String),
}

impl ValueError {
    pub fn unexpected(expected: &'static str, actual: ValueKind) -> Self {
        ValueError::UnexpectedType { expected, actual }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value as JsonValue, json};
    use time::Duration;

    #[test]
    fn value_serializes_scalars() {
        let cases = vec![
            (Value::Bool(true), json!(true)),
            (Value::Int(-42), json!(-42)),
            (Value::Uint(7), json!(7)),
            (Value::Double(3.14), json!(3.14)),
            (Value::String("hi".into()), json!("hi")),
            (Value::Bytes(vec![1, 2, 3]), json!([1, 2, 3])),
            (Value::Duration(Duration::seconds(5)), json!("5s")),
            (Value::Null, JsonValue::Null),
        ];
        for (value, expected) in cases {
            let serialized = serde_json::to_value(&value).unwrap();
            assert_eq!(serialized, expected);
        }
    }

    #[test]
    fn value_serializes_nested_structures() {
        let mut struct_value = StructValue::new("example.User");
        struct_value.set_field("name", "Ada");
        struct_value.set_field("roles", ListValue::from(vec!["admin", "user"]));

        let mut map = MapValue::new();
        map.insert("user", Value::Struct(struct_value.clone()));
        map.insert("active", true);

        let list = ListValue::from(vec![
            Value::Map(map.clone()),
            Value::Struct(struct_value),
        ]);
        let serialized = serde_json::to_value(&list).unwrap();

        assert_eq!(
            serialized,
            json!([
                {"user": {"name": "Ada", "roles": ["admin", "user"]}, "active": true},
                {"name": "Ada", "roles": ["admin", "user"]}
            ])
        );
    }

    #[test]
    fn json_deserializes_into_struct_value() {
        let json = json!({
            "name": "Ada",
            "roles": ["admin", "user"],
            "active": true
        });
        let expected = {
            let mut map = MapValue::new();
            map.insert("name", "Ada");
            map.insert("roles", ListValue::from(vec!["admin", "user"]));
            map.insert("active", true);
            Value::Map(map)
        };
        assert_eq!(json_to_value(json), expected);
    }

    #[test]
    fn json_deserializes_complex_map() {
        let json = json!({
            "users": [
                {"name": "Ada", "roles": ["admin"]},
                {"name": "Bob", "roles": ["user"]}
            ],
            "count": 2
        });
        let mut user_one = MapValue::new();
        user_one.insert("name", "Ada");
        user_one.insert("roles", ListValue::from(vec!["admin"]));

        let mut user_two = MapValue::new();
        user_two.insert("name", "Bob");
        user_two.insert("roles", ListValue::from(vec!["user"]));

        let expected = {
            let mut map = MapValue::new();
            map.insert(
                "users",
                Value::List(ListValue::from(vec![
                    Value::Map(user_one),
                    Value::Map(user_two),
                ])),
            );
            map.insert("count", 2);
            Value::Map(map)
        };
        assert_eq!(json_to_value(json), expected);
    }

    fn json_to_value(value: JsonValue) -> Value {
        match value {
            JsonValue::Null => Value::Null,
            JsonValue::Bool(flag) => Value::Bool(flag),
            JsonValue::Number(num) => num
                .as_i64()
                .map(Value::Int)
                .or_else(|| num.as_u64().map(Value::Uint))
                .or_else(|| num.as_f64().map(Value::Double))
                .unwrap_or(Value::Null),
            JsonValue::String(text) => Value::String(text),
            JsonValue::Array(items) => {
                let converted =
                    items.into_iter().map(json_to_value).collect::<Vec<_>>();
                Value::List(ListValue::from(converted))
            }
            JsonValue::Object(map) => {
                let mut cel_map = MapValue::new();
                for (key, value) in map {
                    cel_map.insert(key, json_to_value(value));
                }
                Value::Map(cel_map)
            }
        }
    }
}
