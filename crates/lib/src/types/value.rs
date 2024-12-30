use super::{Key, List, Map};
use base64::prelude::*;
use miette::Error;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use time::{Duration, OffsetDateTime};

/// ValueKind is an enum that represents the different types of values that can be stored in a
/// Value.
#[derive(
    Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord, Serialize, Deserialize,
)]
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

/// Value is a primitive value for each ValueKind. Resolution for a value could be a constant,
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
    Duration(Duration),
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

impl From<HashMap<Key, Value>> for Value {
    fn from(value: HashMap<Key, Value>) -> Self {
        Value::Map(value.into())
    }
}

impl From<List> for Value {
    fn from(value: List) -> Self {
        Value::List(value)
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

impl From<Duration> for Value {
    fn from(value: Duration) -> Self {
        Value::Duration(value)
    }
}

impl From<Value> for Duration {
    fn from(value: Value) -> Self {
        match value {
            Value::Duration(d) => d,
            _ => panic!("Cannot convert {:?} to Duration", value),
        }
    }
}

// impl From<Value> for serde_json::Value {
//     fn from(value: Value) -> Self {
//         match value {
//             Value::Int(n) => serde_json::Value::Number(n.into()),
//             Value::Uint(n) => serde_json::Value::Number(n.into()),
//             Value::Double(n) => serde_json::to_value(n).unwrap(),
//             Value::String(s) => serde_json::Value::String(s),
//             Value::Bool(b) => serde_json::Value::Bool(b),
//             Value::Map(map) => serde_json::to_value(map).unwrap(),
//             Value::List(list) => serde_json::to_value(list).unwrap(),
//             Value::Bytes(b) => serde_json::Value::Array(
//                 b.into_iter().map(|b| b.into()).collect(),
//             ),
//             Value::Null => serde_json::Value::Null,
//             Value::Timestamp(t) => {
//                 serde_json::Value::String(t.format(&Rfc3339).unwrap())
//             }
//             Value::Duration(d) => serde_json::Value::String(d.to_string()),
//         }
//     }
// }
//
// impl From<&Value> for serde_json::Value {
//     fn from(value: &Value) -> Self {
//         match value {
//             Value::Int(n) => serde_json::Value::from(*n),
//             Value::Uint(n) => serde_json::Value::from(*n),
//             Value::Double(n) => serde_json::to_value(n).unwrap(),
//             Value::String(s) => serde_json::Value::String(s.clone()),
//             Value::Bool(b) => serde_json::Value::Bool(*b),
//             Value::Map(map) => serde_json::to_value(map).unwrap(),
//             Value::List(list) => serde_json::to_value(list).unwrap(),
//             Value::Bytes(b) => {
//                 serde_json::Value::String(BASE64_STANDARD.encode(b))
//             }
//             Value::Null => serde_json::Value::Null,
//             Value::Timestamp(t) => {
//                 serde_json::Value::String(t.format(&Rfc3339).unwrap())
//             }
//             Value::Duration(d) => serde_json::Value::String(d.to_string()),
//         }
//     }
// }

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
        if self.kind() != other.kind() {
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
