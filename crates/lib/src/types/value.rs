use super::{deserialize_duration, serialize_duration, Key, List, Map};
use base64::prelude::*;
use miette::Error;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::{collections::HashMap, str::FromStr};
use time::format_description::well_known::Rfc3339;
use time::OffsetDateTime;

/// ValueType is an enum that represents the different types of values that can be stored in a
/// Value.
#[derive(
    Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord, Serialize, Deserialize,
)]
pub enum ValueType {
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

pub trait TryIntoValue {
    type Error: std::error::Error + 'static;
    fn try_into_value(self) -> Result<Value, Self::Error>;
}

impl<T> TryIntoValue for T
where
    T: serde::Serialize,
{
    type Error = super::ser::SerializeError;
    fn try_into_value(self) -> Result<Value, Self::Error> {
        self.serialize(super::ser::Serializer)
    }
}

pub trait TryFromValue: Sized {
    type Error: std::error::Error + 'static;
    fn try_from_value(value: Value) -> Result<Self, Self::Error>;
}

impl<T> TryFromValue for T
where
    T: serde::de::DeserializeOwned,
{
    type Error = super::de::DeserializeError;
    fn try_from_value(value: Value) -> Result<Self, Self::Error> {
        T::deserialize(value)
    }
}

/// Value is a primitive value for each ValueType. Resolution for a value could be a constant,
/// for example, an Int(1), or a resolved value from a variable.
#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
#[serde(untagged)]
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
    #[serde(
        serialize_with = "serialize_duration",
        deserialize_with = "deserialize_duration"
    )]
    Duration(time::Duration),
}

impl FromStr for Value {
    type Err = miette::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Value::String(s.to_string()))
    }
}

impl From<i8> for Value {
    fn from(value: i8) -> Self {
        Value::Int(value as i64)
    }
}

impl From<Value> for i8 {
    fn from(value: Value) -> Self {
        match value {
            Value::Int(n) => n as i8,
            _ => panic!("Cannot convert {:?} to i8", value),
        }
    }
}

impl From<i16> for Value {
    fn from(value: i16) -> Self {
        Value::Int(value as i64)
    }
}

impl From<Value> for i16 {
    fn from(value: Value) -> Self {
        match value {
            Value::Int(n) => n as i16,
            _ => panic!("Cannot convert {:?} to i16", value),
        }
    }
}

impl From<i32> for Value {
    fn from(value: i32) -> Self {
        Value::Uint(value as u64)
    }
}

impl From<Value> for i32 {
    fn from(value: Value) -> Self {
        match value {
            Value::Int(n) => n as i32,
            _ => panic!("Cannot convert {:?} to i32", value),
        }
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Value::Int(value)
    }
}

impl From<isize> for Value {
    fn from(value: isize) -> Self {
        Value::Int(value as i64)
    }
}

impl From<Value> for isize {
    fn from(value: Value) -> Self {
        match value {
            Value::Int(n) => n as isize,
            _ => panic!("Cannot convert {:?} to isize", value),
        }
    }
}

impl From<Value> for i64 {
    fn from(value: Value) -> Self {
        match value {
            Value::Int(n) => n,
            _ => panic!("Cannot convert {:?} to i64", value),
        }
    }
}

impl From<u8> for Value {
    fn from(value: u8) -> Self {
        Value::Uint(value as u64)
    }
}

impl From<Value> for u8 {
    fn from(value: Value) -> Self {
        match value {
            Value::Uint(n) => n as u8,
            _ => panic!("Cannot convert {:?} to u8", value),
        }
    }
}

impl From<u16> for Value {
    fn from(value: u16) -> Self {
        Value::Uint(value as u64)
    }
}

impl From<Value> for u16 {
    fn from(value: Value) -> Self {
        match value {
            Value::Uint(n) => n as u16,
            _ => panic!("Cannot convert {:?} to u16", value),
        }
    }
}

impl From<u32> for Value {
    fn from(value: u32) -> Self {
        Value::Uint(value as u64)
    }
}

impl From<Value> for u32 {
    fn from(value: Value) -> Self {
        match value {
            Value::Uint(n) => n as u32,
            _ => panic!("Cannot convert {:?} to u32", value),
        }
    }
}

impl From<u64> for Value {
    fn from(value: u64) -> Self {
        Value::Uint(value)
    }
}

impl From<usize> for Value {
    fn from(value: usize) -> Self {
        Value::Uint(value as u64)
    }
}

impl From<Value> for u64 {
    fn from(value: Value) -> Self {
        match value {
            Value::Uint(n) => n,
            _ => panic!("Cannot convert {:?} to u64", value),
        }
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Value::Double(value)
    }
}

impl From<Value> for f64 {
    fn from(value: Value) -> Self {
        match value {
            Value::Double(n) => n,
            _ => panic!("Cannot convert {:?} to f64", value),
        }
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Value::String(value)
    }
}

impl From<&String> for Value {
    fn from(value: &String) -> Self {
        Value::String(value.clone())
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Value::String(value.to_string())
    }
}

impl From<Value> for String {
    fn from(value: Value) -> Self {
        match value {
            Value::String(s) => s,
            _ => panic!("Cannot convert {:?} to String", value),
        }
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Value::Bool(value)
    }
}

impl From<Value> for bool {
    fn from(value: Value) -> Self {
        match value {
            Value::Bool(b) => b,
            _ => panic!("Cannot convert {:?} to bool", value),
        }
    }
}

impl From<Map> for Value {
    fn from(value: Map) -> Self {
        Value::Map(value)
    }
}

impl<K, V> From<HashMap<K, V>> for Value
where
    K: Into<Key>,
    V: TryIntoValue,
{
    fn from(value: HashMap<K, V>) -> Self {
        Value::Map(value.into())
    }
}

impl<K, V> FromIterator<(K, V)> for Value
where
    K: Into<Key>,
    V: TryIntoValue,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let mut map = Map::new();
        for (k, v) in iter {
            map.insert(k.into(), v.try_into_value().unwrap()).unwrap();
        }
        Value::Map(map)
    }
}

impl From<List> for Value {
    fn from(value: List) -> Self {
        Value::List(value)
    }
}

impl From<Vec<Value>> for Value {
    fn from(value: Vec<Value>) -> Self {
        Value::List(value.into())
    }
}

impl From<Vec<&Value>> for Value {
    fn from(value: Vec<&Value>) -> Self {
        Value::List(value.iter().cloned().cloned().collect())
    }
}

impl From<Vec<i8>> for Value {
    fn from(value: Vec<i8>) -> Self {
        Value::List(
            value
                .iter()
                .map(|v| Value::Int(*v as i64))
                .collect::<Vec<Value>>()
                .into(),
        )
    }
}

impl From<Vec<isize>> for Value {
    fn from(value: Vec<isize>) -> Self {
        Value::List(
            value
                .iter()
                .map(|v| Value::Int(*v as i64))
                .collect::<Vec<Value>>()
                .into(),
        )
    }
}

impl From<Vec<i16>> for Value {
    fn from(value: Vec<i16>) -> Self {
        Value::List(
            value
                .iter()
                .map(|v| Value::Int(*v as i64))
                .collect::<Vec<Value>>()
                .into(),
        )
    }
}

impl From<Vec<i32>> for Value {
    fn from(value: Vec<i32>) -> Self {
        Value::List(
            value
                .iter()
                .map(|v| Value::Int(*v as i64))
                .collect::<Vec<Value>>()
                .into(),
        )
    }
}

impl From<Vec<i64>> for Value {
    fn from(value: Vec<i64>) -> Self {
        Value::List(
            value
                .iter()
                .map(|v| Value::Int(*v))
                .collect::<Vec<Value>>()
                .into(),
        )
    }
}

impl From<Vec<u16>> for Value {
    fn from(value: Vec<u16>) -> Self {
        Value::List(
            value
                .iter()
                .map(|v| Value::Uint(*v as u64))
                .collect::<Vec<Value>>()
                .into(),
        )
    }
}

impl From<Vec<u32>> for Value {
    fn from(value: Vec<u32>) -> Self {
        Value::List(
            value
                .iter()
                .map(|v| Value::Uint(*v as u64))
                .collect::<Vec<Value>>()
                .into(),
        )
    }
}

impl From<Vec<u64>> for Value {
    fn from(value: Vec<u64>) -> Self {
        Value::List(
            value
                .iter()
                .map(|v| Value::Uint(*v))
                .collect::<Vec<Value>>()
                .into(),
        )
    }
}

impl From<Vec<u8>> for Value {
    fn from(value: Vec<u8>) -> Self {
        Value::Bytes(value)
    }
}

impl From<Value> for Vec<u8> {
    fn from(value: Value) -> Self {
        match value {
            Value::Bytes(b) => b,
            _ => panic!("Cannot convert {:?} to Vec<u8>", value),
        }
    }
}

impl From<&[u8]> for Value {
    fn from(value: &[u8]) -> Self {
        Value::Bytes(value.to_vec())
    }
}

impl From<OffsetDateTime> for Value {
    fn from(value: OffsetDateTime) -> Self {
        Value::Timestamp(value)
    }
}

impl From<Value> for OffsetDateTime {
    fn from(value: Value) -> Self {
        match value {
            Value::Timestamp(t) => t,
            _ => panic!("Cannot convert {:?} to OffsetDateTime", value),
        }
    }
}

impl From<time::Duration> for Value {
    fn from(value: time::Duration) -> Self {
        Value::Duration(value)
    }
}

impl From<Value> for time::Duration {
    fn from(value: Value) -> Self {
        match value {
            Value::Duration(d) => d,
            _ => panic!("Cannot convert {:?} to Duration", value),
        }
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
            Value::Map(map) => write!(f, "{map}"),
            Value::List(list) => write!(f, "{list}"),
            Value::Bytes(b) => BASE64_STANDARD.encode(b).fmt(f),
            Value::Null => write!(f, "null"),
            Value::Timestamp(v) => write!(f, "{}", v.format(&Rfc3339).unwrap()),
            Value::Duration(v) => write!(f, "{v:?}"),
        }
    }
}

impl Value {
    pub fn type_of(&self) -> ValueType {
        match self {
            Value::Int(_) => ValueType::Int,
            Value::Uint(_) => ValueType::Uint,
            Value::Double(_) => ValueType::Double,
            Value::String(_) => ValueType::String,
            Value::Bool(_) => ValueType::Bool,
            Value::Map(_) => ValueType::Map,
            Value::List(_) => ValueType::List,
            Value::Bytes(_) => ValueType::Bytes,
            Value::Null => ValueType::Null,
            Value::Timestamp(_) => ValueType::Timestamp,
            Value::Duration(_) => ValueType::Duration,
        }
    }

    pub fn try_into<T>(self) -> Result<T, Error>
    where
        T: DeserializeOwned,
    {
        crate::try_from_value(self)
    }

    pub fn plus(&self, other: &Value) -> Result<Value, Error> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            (Value::Uint(a), Value::Uint(b)) => Ok(Value::Uint(a + b)),
            (Value::Double(a), Value::Double(b)) => Ok(Value::Double(a + b)),
            (Value::String(a), Value::String(b)) => {
                Ok(Value::String(format!("{}{}", a, b)))
            }
            (Value::Bytes(a), Value::Bytes(b)) => {
                Ok(Value::Bytes([a.as_slice(), b.as_slice()].concat()))
            }
            (Value::List(a), Value::List(b)) => {
                let mut list = a.clone();
                list.append(&mut b.clone())?;
                Ok(Value::List(list))
            }
            (Value::Timestamp(t), Value::Duration(d)) => {
                Ok(Value::Timestamp(*t + *d))
            }
            (Value::Duration(d), Value::Timestamp(t)) => {
                Ok(Value::Timestamp(*t + *d))
            }
            (Value::Duration(d1), Value::Duration(d2)) => {
                Ok(Value::Duration(*d1 + *d2))
            }

            _ => miette::bail!(
                "Invalid types for plus: {:?} and {:?}",
                self,
                other
            ),
        }
    }

    pub fn minus(&self, other: &Value) -> Result<Value, Error> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
            (Value::Uint(a), Value::Uint(b)) => Ok(Value::Uint(a - b)),
            (Value::Double(a), Value::Double(b)) => Ok(Value::Double(a - b)),
            (Value::Timestamp(t), Value::Duration(d)) => {
                Ok(Value::Timestamp(*t - *d))
            }
            (Value::Duration(d), Value::Timestamp(t)) => {
                Ok(Value::Timestamp(*t - *d))
            }
            (Value::Duration(d1), Value::Duration(d2)) => {
                Ok(Value::Duration(*d1 - *d2))
            }
            _ => miette::bail!(
                "Invalid types for minus: {:?} and {:?}",
                self,
                other
            ),
        }
    }

    /// The equal method compares two values and returns a boolean value.
    /// Values MUST be of the same type. If they are not, an error is returned.
    pub fn equal(&self, other: &Value) -> Result<Value, Error> {
        if self.type_of() != other.type_of() {
            miette::bail!("Cannot compare {:?} and {:?}", self, other);
        }
        Ok(Value::Bool(self == other))
    }

    pub fn not_equal(&self, other: &Value) -> Result<Value, Error> {
        match self.equal(other) {
            Ok(Value::Bool(b)) => Ok(Value::Bool(!b)),
            Ok(_) => miette::bail!(
                "Invalid types for not_equals: {:?} and {:?}",
                self,
                other
            ),
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
            (Value::Timestamp(t1), Value::Timestamp(t2)) => {
                Value::Bool(t1 > t2)
            }
            (Value::Duration(d1), Value::Duration(d2)) => Value::Bool(d1 > d2),
            (left, right) => {
                miette::bail!("Cannot compare {:?} and {:?}", left, right)
            }
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
            (Value::Timestamp(t1), Value::Timestamp(t2)) => {
                Value::Bool(t1 >= t2)
            }
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
            (Value::Timestamp(t1), Value::Timestamp(t2)) => {
                Value::Bool(t1 < t2)
            }
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
            (Value::Timestamp(t1), Value::Timestamp(t2)) => {
                Value::Bool(t1 <= t2)
            }
            (Value::Duration(d1), Value::Duration(d2)) => Value::Bool(d1 <= d2),
            _ => miette::bail!("Failed to compare {self:?} <= {other:?}"),
        };

        Ok(v)
    }

    pub fn multiply(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self, other) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs * rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs * rhs),
            (Value::Double(lhs), Value::Double(rhs)) => {
                Value::Double(lhs * rhs)
            }
            _ => miette::bail!("Failed to multiply {self:?} * {other:?}"),
        };

        Ok(v)
    }

    pub fn devide(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self, other) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs / rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs / rhs),
            (Value::Double(lhs), Value::Double(rhs)) => {
                Value::Double(lhs / rhs)
            }
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

#[cfg(test)]
mod test_serialize {
    use super::*;

    #[test]
    fn test_vector() {
        let v = vec![1, 2, 3, 4, 5];
        let value: Value = v.into();
        let expected = Value::List(
            vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
                Value::Int(4),
                Value::Int(5),
            ]
            .into(),
        );
        assert_eq!(value, expected);
    }

    #[test]
    fn test_hashmap() {
        let mut map = HashMap::new();
        map.insert("a", 1);
        map.insert("b", 2);
        map.insert("c", 3);

        let value: Value = map.into();
        let expected = Value::Map(
            vec![
                (Key::from("a"), Value::Int(1)),
                (Key::from("b"), Value::Int(2)),
                (Key::from("c"), Value::Int(3)),
            ]
            .into_iter()
            .collect::<HashMap<Key, Value>>()
            .into(),
        );

        assert_eq!(value, expected);
    }

    #[test]
    fn test_object() {
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct Object {
            a: i32,
            b: String,
            c: bool,
        }

        let obj = Object {
            a: 1,
            b: "hello".to_string(),
            c: true,
        };

        let value: Value = obj.try_into_value().unwrap();

        let expected = Value::Map(
            vec![
                (Key::from("a"), Value::Int(1)),
                (Key::from("b"), Value::String("hello".to_string())),
                (Key::from("c"), Value::Bool(true)),
            ]
            .into_iter()
            .collect::<HashMap<Key, Value>>()
            .into(),
        );

        assert_eq!(value, expected);
    }

    #[test]
    fn test_serialize_duration() {
        let duration = time::Duration::hours(1) + time::Duration::minutes(30);
        let value: Value = duration.into();

        let got = serde_json::to_string(&value).unwrap();
        let want = r#""1h30m""#;
        assert_eq!(want, got);
    }
}
