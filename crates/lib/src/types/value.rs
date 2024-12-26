use super::{Key, List, Map};
use miette::Error;
use serde::{ser::Serializer, Serialize};
use std::fmt;
use std::{collections::HashMap, sync::Arc};
use time::{Duration, OffsetDateTime};

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

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Int(i64),
    Uint(u64),
    Double(f64),
    String(Arc<String>),
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
            serde_json::Value::String(s) => Value::String(Arc::new(s)),
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
                            .map(|(k, v)| (Key::from(k), Value::from(v)))
                            .collect::<HashMap<Key, Value>>(),
                    ))
                }
            }
        }
    }
}

macro_rules! impl_owned_value_conversions {
    ($($target_type: ty => $value_variant:path),* $(,)?) => {
        $(
            impl From<$target_type> for Value {
                fn from(value: $target_type) -> Self {
                    $value_variant(value)
                }
            }

            impl From<Value> for $target_type {
                fn from(value: Value) -> Self {
                    match value {
                        $value_variant(v) => v,
                        _ => panic!("Invalid conversion from {:?} to {:?}", value, stringify!($target_type)),
                    }
                }
            }
        )*
    }
}

impl_owned_value_conversions! {
    i64 => Value::Int,
    u64 => Value::Uint,
    f64 => Value::Double,
    bool => Value::Bool,
    Arc<String> => Value::String,
    Map => Value::Map,
    List => Value::List,
    Vec<u8> => Value::Bytes,
    OffsetDateTime => Value::Timestamp,
    Duration => Value::Duration,
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Value::String(Arc::new(value))
    }
}

impl From<Value> for String {
    fn from(value: Value) -> Self {
        match value {
            Value::String(s) => s.as_ref().clone(),
            _ => panic!("Invalid conversion from {:?} to String", value),
        }
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Value::String(Arc::new(value.to_string()))
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
            (Value::String(a), Value::String(b)) => {
                Ok(Value::String(Arc::new(format!("{}{}", a, b))))
            }
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