use super::{
    deserialize_duration, serialize_duration, Key, KeyType, List, Map, Value,
    ValueType,
};
use base64::prelude::*;
use miette::{Error, IntoDiagnostic};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use time::format_description::well_known::Rfc3339;
use time::OffsetDateTime;

/// Represents dynamic value that is type checked or converted
/// during evaluation time. It is associated with `dyn(<type>)` expression.
#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Dyn {
    Int(i64),
    Uint(u64),
    Double(f64),
    String(String),
    Bool(bool),
    Map(HashMap<Key, Dyn>),
    List(Vec<Dyn>),
    Bytes(Vec<u8>),
    Null,
    Timestamp(OffsetDateTime),
    #[serde(
        serialize_with = "serialize_duration",
        deserialize_with = "deserialize_duration"
    )]
    Duration(time::Duration),
}

impl Dyn {
    /// Tries to convert self into i64
    #[inline]
    pub fn try_into_i64(self) -> Result<i64, Error> {
        match self {
            Dyn::Int(n) => Ok(n),
            Dyn::Uint(n) => Ok(i64::try_from(n).into_diagnostic()?),
            Dyn::Double(n) => Ok(n.round() as i64),
            Dyn::String(s) => match s.parse::<i64>() {
                Ok(n) => Ok(n),
                Err(e) => miette::bail!("Failed to convert to int: {e:?}"),
            },
            Dyn::Timestamp(t) => Ok(t.unix_timestamp()),
            _ => miette::bail!("Failed to convert to int"),
        }
    }

    /// Tries to convert &self to i64
    #[inline]
    pub fn try_to_i64(&self) -> Result<i64, Error> {
        self.clone().try_into_i64()
    }

    /// Tries to convert self into u64
    #[inline]
    pub fn try_into_u64(self) -> Result<u64, Error> {
        match self {
            Dyn::Int(n) => Ok(u64::try_from(n).into_diagnostic()?),
            Dyn::Uint(n) => Ok(n),
            Dyn::Double(n) => Ok(n.round() as u64),
            Dyn::String(s) => match s.parse::<u64>() {
                Ok(n) => Ok(n),
                Err(e) => miette::bail!("Failed to convert to uint: {e:?}"),
            },
            _ => miette::bail!("Failed to convert to uint"),
        }
    }

    /// Tries to convert &self to u64
    #[inline]
    pub fn try_to_u64(&self) -> Result<u64, Error> {
        self.clone().try_into_u64()
    }

    /// Tries to convert self into f64
    #[inline]
    pub fn try_into_f64(self) -> Result<f64, Error> {
        match self {
            Dyn::Int(n) => {
                if n > f64::MAX as i64 || n < f64::MIN as i64 {
                    miette::bail!("Failed to convert to double: out of range")
                } else {
                    Ok(n as f64)
                }
            }
            Dyn::Uint(n) => {
                if n > f64::MAX as u64 {
                    miette::bail!("Failed to convert to double: out of range")
                } else {
                    Ok(n as f64)
                }
            }
            Dyn::Double(n) => Ok(n),
            Dyn::String(s) => match s.parse::<f64>() {
                Ok(n) => Ok(n),
                Err(e) => miette::bail!("Failed to convert to double: {e:?}"),
            },
            _ => miette::bail!("Failed to convert to double"),
        }
    }

    /// Tries to convert &self into f64
    #[inline]
    pub fn try_to_f64(&self) -> Result<f64, Error> {
        self.clone().try_into_f64()
    }

    /// Tries to convert self into bool
    #[inline]
    pub fn try_into_string(self) -> Result<String, Error> {
        match self {
            Dyn::Int(n) => Ok(n.to_string()),
            Dyn::Uint(n) => Ok(n.to_string()),
            Dyn::Double(n) => Ok(n.to_string()),
            Dyn::String(s) => Ok(s.clone()),
            Dyn::Bool(b) => Ok(b.to_string()),
            Dyn::Bytes(s) => Ok(String::from_utf8_lossy(&s).to_string()),
            Dyn::Null => Ok("null".to_string()),
            Dyn::Timestamp(v) => Ok(v.format(&Rfc3339).unwrap()),
            Dyn::Duration(v) => Ok(v.to_string()),
            _ => miette::bail!("Failed to convert to string"),
        }
    }

    /// Tries to convert &self to string
    #[inline]
    pub fn try_to_string(&self) -> Result<String, Error> {
        self.clone().try_into_string()
    }

    /// Tries to convert self into bytes
    #[inline]
    pub fn try_into_bytes(self) -> Result<Vec<u8>, Error> {
        match self {
            Dyn::Bytes(b) => Ok(b),
            Dyn::String(s) => Ok(s.as_bytes().to_vec()),
            _ => miette::bail!("Failed to convert to bytes"),
        }
    }

    /// Tries to convert &self to bytes
    #[inline]
    pub fn try_to_bytes(&self) -> Result<Vec<u8>, Error> {
        self.clone().try_into_bytes()
    }

    /// Tries to convert self into list
    #[inline]
    pub fn try_into_list_of(self, ty: ValueType) -> Result<List, Error> {
        match self {
            Dyn::List(list) => match ty {
                ValueType::ListOf { element_type } => match element_type {
                    None => {
                        assert!(list.is_empty());
                        Ok(List::new())
                    }
                    Some(ty) => {
                        let mut new_list = List::with_type_and_capacity(
                            *ty.clone(),
                            list.len(),
                        );
                        for item in list.iter() {
                            new_list.push(
                                item.clone().try_into_type(*ty.clone())?,
                            )?;
                        }
                        Ok(new_list)
                    }
                },
                d => miette::bail!("Failed to convert to list, got: {:?}", d),
            },
            d => miette::bail!("Failed to convert to list, got: {:?}", d),
        }
    }

    /// Tries to convert &self to list
    #[inline]
    pub fn try_to_list_of(&self, ty: ValueType) -> Result<List, Error> {
        self.clone().try_into_list_of(ty)
    }

    /// Tries to convert self into map
    #[inline]
    pub fn try_into_map_of(self, ty: ValueType) -> Result<Map, Error> {
        match self {
            Dyn::Map(map) => match ty {
                ValueType::MapOf { key_type } => match key_type {
                    None => {
                        assert!(map.is_empty());
                        Ok(Map::new())
                    }
                    Some(ty) => {
                        let mut new_map = Map::with_key_type_and_capacity(
                            *ty.clone(),
                            map.len(),
                        );
                        for (k, v) in map.iter() {
                            let k_value: Dyn = k.into();
                            new_map.insert(
                                k_value.try_into_key_type(*ty.clone())?,
                                v.clone().try_into()?,
                            )?;
                        }
                        Ok(new_map)
                    }
                },
                d => miette::bail!("Failed to convert to map, got: {:?}", d),
            },
            d => miette::bail!("Failed to convert to map, got: {:?}", d),
        }
    }

    /// Tries to convert self into key
    #[inline]
    pub fn try_into_key_type(self, ty: KeyType) -> Result<Key, Error> {
        match ty {
            KeyType::Int => Ok(Key::Int(self.try_into_i64()?)),
            KeyType::Uint => Ok(Key::Uint(self.try_into_u64()?)),
            KeyType::String => Ok(Key::String(self.try_into_string()?)),
            KeyType::Bool => match self {
                Dyn::Bool(b) => Ok(Key::Bool(b)),
                _ => miette::bail!("Failed to convert to bool"),
            },
        }
    }

    /// Tries to convert &self to map
    #[inline]
    pub fn try_to_map_of(&self, ty: ValueType) -> Result<Map, Error> {
        self.clone().try_into_map_of(ty)
    }

    /// Tries to convert self into value
    #[inline]
    pub fn try_into_type(self, ty: ValueType) -> Result<Value, Error> {
        match ty {
            ValueType::Int => Ok(Value::Int(self.try_into_i64()?)),
            ValueType::Uint => Ok(Value::Uint(self.try_into_u64()?)),
            ValueType::Double => Ok(Value::Double(self.try_into_f64()?)),
            ValueType::String => Ok(Value::String(self.try_into_string()?)),
            ValueType::Bool => match self {
                Dyn::Bool(b) => Ok(Value::Bool(b)),
                _ => miette::bail!("Failed to convert to bool"),
            },
            ValueType::Bytes => Ok(Value::Bytes(self.try_into_bytes()?)),
            ValueType::Timestamp => match self {
                Dyn::Timestamp(v) => Ok(Value::Timestamp(v)),
                _ => miette::bail!("Failed to convert to timestamp"),
            },
            ValueType::Duration => match self {
                Dyn::Duration(v) => Ok(Value::Duration(v)),
                _ => miette::bail!("Failed to convert to duration"),
            },
            ValueType::ListOf { .. } => Ok(self.try_into_list_of(ty)?.into()),
            ValueType::MapOf { .. } => Ok(self.try_into_map_of(ty)?.into()),
            ValueType::Null => match self {
                Dyn::Null => Ok(Value::Null),
                _ => miette::bail!("Failed to convert to null"),
            },
            ValueType::Dyn => miette::bail!("Failed to convert to dyn"),
        }
    }

    /// Tries to convert &self to value of type
    #[inline]
    pub fn try_to_type(&self, ty: ValueType) -> Result<Value, Error> {
        self.clone().try_into_type(ty)
    }
}

impl fmt::Display for Dyn {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Dyn::Int(n) => write!(f, "{n}"),
            Dyn::Uint(n) => write!(f, "{n}"),
            Dyn::Double(n) => write!(f, "{n}"),
            Dyn::String(s) => write!(f, "{s}"),
            Dyn::Bool(b) => write!(f, "{b}"),
            Dyn::Map(map) => write!(f, "{map:?}"),
            Dyn::List(list) => write!(f, "{list:?}"),
            Dyn::Bytes(b) => BASE64_STANDARD.encode(b).fmt(f),
            Dyn::Null => write!(f, "null"),
            Dyn::Timestamp(v) => {
                write!(f, "{}", v.format(&Rfc3339).unwrap())
            }
            Dyn::Duration(v) => write!(f, "{v:?}"),
        }
    }
}

impl TryFrom<Dyn> for Value {
    type Error = Error;

    fn try_from(d: Dyn) -> Result<Value, Error> {
        let val = match d {
            Dyn::Int(n) => Value::Int(n),
            Dyn::Uint(n) => Value::Uint(n),
            Dyn::Double(n) => Value::Double(n),
            Dyn::String(s) => Value::String(s),
            Dyn::Bool(b) => Value::Bool(b),
            Dyn::Map(map) => {
                let mut new_map = Map::with_capacity(map.len());
                for (k, v) in map.into_iter() {
                    new_map.insert(k, v.try_into()?)?;
                }
                Value::Map(new_map.try_into()?)
            }
            Dyn::List(list) => {
                let mut new_list = List::new();
                for item in list.into_iter() {
                    new_list.push(item.try_into()?)?;
                }
                Value::List(new_list)
            }
            Dyn::Bytes(b) => Value::Bytes(b),
            Dyn::Null => Value::Null,
            Dyn::Timestamp(v) => Value::Timestamp(v),
            Dyn::Duration(v) => Value::Duration(v),
        };
        Ok(val)
    }
}

impl From<Value> for Dyn {
    fn from(v: Value) -> Self {
        match v {
            Value::Int(n) => Dyn::Int(n),
            Value::Uint(n) => Dyn::Uint(n),
            Value::Double(n) => Dyn::Double(n),
            Value::String(s) => Dyn::String(s),
            Value::Bool(b) => Dyn::Bool(b),
            Value::Map(map) => {
                let mut new_map = HashMap::new();
                for (k, v) in map.into_iter() {
                    new_map.insert(k, v.into());
                }
                Dyn::Map(new_map)
            }
            Value::List(list) => {
                let mut new_list = Vec::new();
                for item in list.into_iter() {
                    new_list.push(item.into());
                }
                Dyn::List(new_list)
            }
            Value::Bytes(b) => Dyn::Bytes(b),
            Value::Null => Dyn::Null,
            Value::Timestamp(v) => Dyn::Timestamp(v),
            Value::Duration(v) => Dyn::Duration(v),
            Value::Dyn(d) => d,
        }
    }
}

impl From<Key> for Dyn {
    fn from(k: Key) -> Self {
        match k {
            Key::String(s) => Dyn::String(s),
            Key::Int(n) => Dyn::Int(n),
            Key::Uint(n) => Dyn::Uint(n),
            Key::Bool(b) => Dyn::Bool(b),
        }
    }
}

impl From<&Key> for Dyn {
    fn from(k: &Key) -> Self {
        match k {
            Key::String(s) => Dyn::String(s.clone()),
            Key::Int(n) => Dyn::Int(*n),
            Key::Uint(n) => Dyn::Uint(*n),
            Key::Bool(b) => Dyn::Bool(*b),
        }
    }
}
