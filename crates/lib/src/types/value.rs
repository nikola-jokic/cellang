use super::dynamic::Dyn;
use super::{
    deserialize_duration, serialize_duration, Key, KeyType, List, Map,
};
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
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub enum ValueType {
    Int,
    Uint,
    Double,
    String,
    Bool,
    MapOf {
        key_type: Option<Box<KeyType>>,
    },
    ListOf {
        element_type: Option<Box<ValueType>>,
    },
    Bytes,
    Timestamp,
    Duration,
    Null,
    Dyn,
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
    Dyn(Dyn),
}

impl FromStr for Value {
    type Err = miette::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Value::String(s.to_string()))
    }
}

macro_rules! simple_conv {
    ($($($t:ty)* => $p:path as $as:ty)*) => {
        $(
            $(
                impl From<$t> for Value {
                    fn from(value: $t) -> Self {
                        $p(value as $as)
                    }
                }

                impl From<Value> for $t {
                    fn from(value: Value) -> Self {
                        match value {
                            $p(n) => n as $t,
                            _ => panic!("Cannot convert {:?} to {}", value, stringify!($t)),
                        }
                    }
                }
            )*
        )*
    };
}

simple_conv! {
    i8 i16 i32 i64 isize => Value::Int as i64
    u8 u16 u32 u64 usize => Value::Uint as u64
    f32 f64 => Value::Double as f64
    bool => Value::Bool as bool
    String => Value::String as String
    Map => Value::Map as Map
    List => Value::List as List
    Vec<u8> => Value::Bytes as Vec<u8>
    OffsetDateTime => Value::Timestamp as OffsetDateTime
    time::Duration => Value::Duration as time::Duration
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

impl<K, V> TryFrom<HashMap<K, V>> for Value
where
    K: Into<Key>,
    V: TryIntoValue,
{
    type Error = Error;
    fn try_from(value: HashMap<K, V>) -> Result<Self, Error> {
        Ok(Value::Map(value.try_into()?))
    }
}

impl From<Vec<Value>> for Value {
    fn from(value: Vec<Value>) -> Self {
        Value::List(value.try_into().unwrap())
    }
}

macro_rules! vec_conv {
    ($($($t:ty)* => $p:path as $as:ty)*) => {
        $(
            $(
                impl From<Vec<$t>> for Value {
                    fn from(value: Vec<$t>) -> Self {
                        Value::List(value.into_iter().map(|v| $p(v as $as)).collect())
                    }
                }
            )*
        )*
    };
}

vec_conv! {
    i8 i16 i32 i64 isize => Value::Int as i64
    u16 u32 u64 usize => Value::Uint as u64
    f32 f64 => Value::Double as f64
    bool => Value::Bool as bool
    String => Value::String as String
}

impl From<Vec<&Value>> for Value {
    fn from(value: Vec<&Value>) -> Self {
        Value::List(value.into_iter().cloned().collect())
    }
}

impl From<&[u8]> for Value {
    fn from(value: &[u8]) -> Self {
        Value::Bytes(value.to_vec())
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
            Value::Dyn(v) => write!(f, "{v}"),
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
            Value::Map(ref m) => ValueType::MapOf {
                key_type: m.key_type().map(Box::new),
            },
            Value::List(ref l) => ValueType::ListOf {
                element_type: l.element_type().map(Box::new),
            },
            Value::Bytes(_) => ValueType::Bytes,
            Value::Null => ValueType::Null,
            Value::Timestamp(_) => ValueType::Timestamp,
            Value::Duration(_) => ValueType::Duration,
            Value::Dyn(_) => ValueType::Dyn,
        }
    }

    pub fn try_into<T>(self) -> Result<T, Error>
    where
        T: DeserializeOwned,
    {
        crate::try_from_value(self)
    }

    pub fn try_to_key_of_type(&self, key_type: KeyType) -> Result<Key, Error> {
        match (self, key_type) {
            (Value::Int(n), KeyType::Int) => Ok(Key::Int(*n)),
            (Value::Uint(n), KeyType::Uint) => Ok(Key::Uint(*n)),
            (Value::String(s), KeyType::String) => Ok(Key::String(s.clone())),
            (Value::Bool(b), KeyType::Bool) => Ok(Key::Bool(*b)),
            (Value::Dyn(d), _) => d.clone().try_to_key_of_type(key_type),
            _ => miette::bail!("Cannot convert {:?} to Key", self),
        }
    }

    #[inline]
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
            (Value::Timestamp(t), Value::Duration(d))
            | (Value::Duration(d), Value::Timestamp(t)) => {
                Ok(Value::Timestamp(*t + *d))
            }
            (Value::Duration(d1), Value::Duration(d2)) => {
                Ok(Value::Duration(*d1 + *d2))
            }
            (Value::Dyn(d1), Value::Dyn(d2)) => {
                let v1: Value = d1.clone().try_literal_value()?;
                let v2 = d2.try_to_type(v1.type_of())?;
                v1.plus(&v2)
            }
            (Value::Dyn(d), other) => {
                let v = d.try_to_type(other.type_of())?;
                v.plus(other)
            }
            (base, Value::Dyn(d)) => {
                // plus is not associative, so we need to try both ways
                let other = d.try_to_type(base.type_of())?;
                base.plus(&other)
            }
            _ => miette::bail!(
                "Invalid types for plus: {:?} and {:?}",
                self,
                other
            ),
        }
    }

    #[inline]
    pub fn minus(&self, other: &Value) -> Result<Value, Error> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
            (Value::Uint(a), Value::Uint(b)) => Ok(Value::Uint(a - b)),
            (Value::Double(a), Value::Double(b)) => Ok(Value::Double(a - b)),
            (Value::Timestamp(t), Value::Duration(d))
            | (Value::Duration(d), Value::Timestamp(t)) => {
                Ok(Value::Timestamp(*t - *d))
            }
            (Value::Duration(d1), Value::Duration(d2)) => {
                Ok(Value::Duration(*d1 - *d2))
            }
            (Value::Dyn(d1), Value::Dyn(d2)) => {
                let v1: Value = d1.clone().try_literal_value()?;
                let v2 = d2.try_to_type(v1.type_of())?;
                v1.minus(&v2)
            }
            (Value::Dyn(d), other) => {
                let v = d.try_to_type(other.type_of())?;
                v.minus(other)
            }
            (base, Value::Dyn(d)) => {
                // minus is not associative, so we need to try both ways
                let other = d.try_to_type(base.type_of())?;
                base.minus(&other)
            }
            _ => miette::bail!(
                "Invalid types for minus: {:?} and {:?}",
                self,
                other
            ),
        }
    }

    /// The equal method compares two values and returns a boolean value.
    /// Values MUST be of the same type except for dyn.
    /// If they are not, an error is returned.
    #[inline]
    pub fn equal(&self, other: &Value) -> Result<Value, Error> {
        match (self, other) {
            (Value::Dyn(d1), Value::Dyn(d2)) => {
                let v1: Value = d1.clone().try_literal_value()?;
                let v2 = d2.try_to_type(v1.type_of())?;
                v1.equal(&v2)
            }
            (Value::Dyn(d), other) => {
                let v = d.try_to_type(other.type_of())?;
                v.equal(other)
            }
            (base, Value::Dyn(d)) => {
                // equal is not associative, so we need to try both ways
                let other = d.try_to_type(base.type_of())?;
                base.equal(&other)
            }
            (lhs, rhs) => {
                if lhs.type_of() != rhs.type_of() {
                    miette::bail!("Cannot compare {:?} and {:?}", self, other);
                }
                Ok(Value::Bool(self == other))
            }
        }
    }

    #[inline]
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

    #[inline]
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
            (Value::Dyn(d1), Value::Dyn(d2)) => {
                let v1: Value = d1.clone().try_literal_value()?;
                let v2 = d2.try_to_type(v1.type_of())?;
                v1.greater(&v2)?
            }
            (Value::Dyn(d), other) => {
                let v = d.try_to_type(other.type_of())?;
                v.greater(other)?
            }
            (base, Value::Dyn(d)) => {
                // greater is not associative, so we need to try both ways
                let other = d.try_to_type(base.type_of())?;
                base.greater(&other)?
            }
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
            (Value::Dyn(d1), Value::Dyn(d2)) => {
                let v1: Value = d1.clone().try_literal_value()?;
                let v2 = d2.try_to_type(v1.type_of())?;
                v1.greater_equal(&v2)?
            }
            (Value::Dyn(d), other) => {
                let v = d.try_to_type(other.type_of())?;
                v.greater_equal(other)?
            }
            (base, Value::Dyn(d)) => {
                let other = d.try_to_type(base.type_of())?;
                base.greater_equal(&other)?
            }
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
            (Value::Dyn(d1), Value::Dyn(d2)) => {
                let v1: Value = d1.clone().try_literal_value()?;
                let v2 = d2.try_to_type(v1.type_of())?;
                v1.less(&v2)?
            }
            (Value::Dyn(d), other) => {
                let v = d.try_to_type(other.type_of())?;
                v.less(other)?
            }
            (base, Value::Dyn(d)) => {
                let other = d.try_to_type(base.type_of())?;
                base.less(&other)?
            }
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
            (Value::Dyn(d1), Value::Dyn(d2)) => {
                let v1: Value = d1.clone().try_literal_value()?;
                let v2 = d2.try_to_type(v1.type_of())?;
                v1.less_equal(&v2)?
            }
            (Value::Dyn(d), other) => {
                let v = d.try_to_type(other.type_of())?;
                v.less_equal(other)?
            }
            (base, Value::Dyn(d)) => {
                let other = d.try_to_type(base.type_of())?;
                base.less_equal(&other)?
            }
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
            (Value::Dyn(d1), Value::Dyn(d2)) => {
                let v1: Value = d1.clone().try_literal_value()?;
                let v2 = d2.try_to_type(v1.type_of())?;
                v1.multiply(&v2)?
            }
            (Value::Dyn(d), other) => {
                let v = d.try_to_type(other.type_of())?;
                v.multiply(other)?
            }
            (base, Value::Dyn(d)) => {
                let other = d.try_to_type(base.type_of())?;
                base.multiply(&other)?
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
            (Value::Dyn(d1), Value::Dyn(d2)) => {
                let v1: Value = d1.clone().try_literal_value()?;
                let v2 = d2.try_to_type(v1.type_of())?;
                v1.devide(&v2)?
            }
            (Value::Dyn(d), other) => {
                let v = d.try_to_type(other.type_of())?;
                v.devide(other)?
            }
            (base, Value::Dyn(d)) => {
                let other = d.try_to_type(base.type_of())?;
                base.devide(&other)?
            }
            _ => miette::bail!("Failed to devide {self:?} / {other:?}"),
        };

        Ok(v)
    }

    pub fn reminder(&self, other: &Value) -> Result<Value, Error> {
        let v = match (self, other) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs % rhs),
            (Value::Uint(lhs), Value::Uint(rhs)) => Value::Uint(lhs % rhs),
            (Value::Dyn(d1), Value::Dyn(d2)) => {
                let v1: Value = d1.clone().try_literal_value()?;
                let v2 = d2.try_to_type(v1.type_of())?;
                v1.reminder(&v2)?
            }
            (Value::Dyn(d), other) => {
                let v = d.try_to_type(other.type_of())?;
                v.reminder(other)?
            }
            (base, Value::Dyn(d)) => {
                let other = d.try_to_type(base.type_of())?;
                base.reminder(&other)?
            }
            _ => miette::bail!("Failed to get reminder {self:?} % {other:?}"),
        };

        Ok(v)
    }

    pub fn index(&self, other: &Value) -> Result<Value, Error> {
        match (self, other) {
            (Value::List(list), Value::Int(index)) => {
                match list.get(*index as usize) {
                    Some(v) => Ok(v.clone()),
                    None => miette::bail!("Index out of range: {:?}", index),
                }
            }
            (Value::List(list), Value::Dyn(d)) => {
                let index = d.try_to_i64()?;
                match list.get(index as usize) {
                    Some(v) => Ok(v.clone()),
                    None => miette::bail!("Index out of range: {:?}", index),
                }
            }
            (Value::Map(list), index) => {
                if list.is_empty() {
                    miette::bail!("Cannot index into an empty map");
                }

                let key = index.try_to_key_of_type(list.key_type().unwrap())?;

                match list.get(&key)? {
                    Some(v) => Ok(v.clone()),
                    None => miette::bail!("Key not found: {:?}", key),
                }
            }
            (Value::Dyn(d), index) => match d {
                Dyn::List(list) => {
                    let index = match index {
                        Value::Int(n) => *n,
                        Value::Dyn(d) => d.try_to_i64()?,
                        _ => miette::bail!("Cannot index into {:?}", index),
                    };
                    match list.get(index as usize) {
                        Some(v) => Ok(v.clone().try_into()?),
                        None => {
                            miette::bail!("Index out of range: {:?}", index)
                        }
                    }
                }
                Dyn::Map(map) => {
                    // the key must be of key type and not dynamic
                    let key = Key::try_from(index)?;
                    match map.get(&key) {
                        Some(d) => Ok(d.clone().try_into()?),
                        None => miette::bail!("Key not found: {:?}", key),
                    }
                }
                _ => miette::bail!("Cannot index into {:?}", d),
            },
            _ => miette::bail!("Cannot index into {:?} with {:?}", self, other),
        }
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
            .try_into()
            .unwrap(),
        );
        assert_eq!(value, expected);
    }

    #[test]
    fn test_hashmap() {
        let mut map = HashMap::new();
        map.insert("a", 1);
        map.insert("b", 2);
        map.insert("c", 3);

        let value: Value = map.try_into().unwrap();
        let expected = Value::Map(
            vec![
                (Key::from("a"), Value::Int(1)),
                (Key::from("b"), Value::Int(2)),
                (Key::from("c"), Value::Int(3)),
            ]
            .into_iter()
            .collect::<HashMap<Key, Value>>()
            .try_into()
            .unwrap(),
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
            .try_into()
            .unwrap(),
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
