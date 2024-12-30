use crate::Value;
use serde::{
    de::{DeserializeSeed, SeqAccess},
    forward_to_deserialize_any,
};
use std::collections::hash_map::{IntoKeys, IntoValues};
use thiserror::Error;

use super::{Key, List, Map};

#[derive(Debug, Error, PartialEq)]
pub enum DeserializeError {
    #[error("deserialization error")]
    DeserializationError(String),
}

impl serde::de::Error for DeserializeError {
    fn custom<T: std::fmt::Display>(msg: T) -> Self {
        DeserializeError::DeserializationError(msg.to_string())
    }
}

struct SeqDeserializer {
    iter: std::vec::IntoIter<Value>,
}

impl SeqDeserializer {
    fn new(vec: Vec<Value>) -> Self {
        SeqDeserializer {
            iter: vec.into_iter(),
        }
    }
}

impl<'de> SeqAccess<'de> for SeqDeserializer {
    type Error = DeserializeError;

    fn next_element_seed<T>(
        &mut self,
        seed: T,
    ) -> Result<Option<T::Value>, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        match self.iter.next() {
            Some(value) => seed.deserialize(value).map(Some),
            None => Ok(None),
        }
    }

    fn size_hint(&self) -> Option<usize> {
        match self.iter.size_hint() {
            (lower, Some(upper)) if lower == upper => Some(upper),
            _ => None,
        }
    }
}

struct MapDeserializer<'a> {
    keys: IntoKeys<Key, Value>,
    values: IntoValues<Key, Value>,
    lifetime: std::marker::PhantomData<&'a ()>,
}

impl MapDeserializer<'_> {
    fn new(map: Map) -> Self {
        MapDeserializer {
            keys: map.clone().into_keys(),
            values: map.into_values(),
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'de> serde::de::MapAccess<'de> for MapDeserializer<'_> {
    type Error = DeserializeError;

    fn next_key_seed<K>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, Self::Error>
    where
        K: serde::de::DeserializeSeed<'de>,
    {
        match self.keys.next() {
            Some(key) => seed.deserialize(key).map(Some),
            None => Ok(None),
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::DeserializeSeed<'de>,
    {
        seed.deserialize(self.values.next().unwrap())
    }
}

impl<'de> serde::de::Deserializer<'de> for Key {
    type Error = DeserializeError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Key::String(s) => visitor.visit_string(s),
            Key::Int(i) => visitor.visit_i64(i),
            Key::Uint(i) => visitor.visit_u64(i),
            Key::Bool(b) => visitor.visit_bool(b),
        }
    }

    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string bytes byte_buf option map unit unit_struct newtype_struct seq tuple tuple_struct struct enum identifier ignored_any
    }
}

impl<'de> serde::de::Deserializer<'de> for Map {
    type Error = DeserializeError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_map(MapDeserializer::new(self))
    }

    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string bytes byte_buf option unit map unit_struct newtype_struct seq tuple tuple_struct struct enum identifier ignored_any
    }
}

impl<'de> serde::de::Deserializer<'de> for List {
    type Error = DeserializeError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_seq(SeqDeserializer::new(self.inner().clone()))
    }

    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string bytes byte_buf option map unit unit_struct newtype_struct seq tuple tuple_struct struct enum identifier ignored_any
    }
}

impl<'de> serde::de::Deserializer<'de> for Value {
    type Error = DeserializeError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        let m = match self {
            Value::Map(m) => m,
            v => {
                return Err(DeserializeError::DeserializationError(format!(
                    "unexpected value: {v:?}"
                )))
            }
        };

        visitor.visit_map(MapDeserializer::new(m))
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Bool(b) => visitor.visit_bool(b),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Int(i) => visitor.visit_i8(i as i8),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}",
            ))),
        }
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Int(i) => visitor.visit_i16(i as i16),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Int(i) => visitor.visit_i32(i as i32),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Int(i) => visitor.visit_i64(i),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Uint(i) => visitor.visit_u8(i as u8),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Uint(i) => visitor.visit_u16(i as u16),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Uint(i) => visitor.visit_u32(i as u32),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Uint(i) => visitor.visit_u64(i),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}",
            ))),
        }
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Double(f) => visitor.visit_f32(f as f32),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Double(f) => visitor.visit_f64(f),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::String(s) => {
                if s.len() == 1 {
                    visitor.visit_char(s.chars().next().unwrap())
                } else {
                    Err(DeserializeError::DeserializationError(
                        "expected a single character".to_string(),
                    ))
                }
            }
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::String(s) => visitor.visit_str(&s),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}",
            ))),
        }
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::String(s) => visitor.visit_string(s),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}",
            ))),
        }
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Bytes(b) => visitor.visit_bytes(&b),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}",
            ))),
        }
    }

    fn deserialize_byte_buf<V>(
        self,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Bytes(b) => visitor.visit_byte_buf(b),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}",
            ))),
        }
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Null => visitor.visit_none(),
            _ => visitor.visit_some(self),
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Null => visitor.visit_unit(),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}"
            ))),
        }
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Value::Null => visitor.visit_unit(),
            v => Err(DeserializeError::DeserializationError(format!(
                "unexpected value: {v:?}",
            ))),
        }
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        let vec = match self {
            Value::List(l) => l.inner().clone(),
            v => {
                return Err(DeserializeError::DeserializationError(format!(
                    "unexpected value: {v:?}",
                )))
            }
        };

        let seq = SeqDeserializer::new(vec);
        visitor.visit_seq(seq)
    }

    fn deserialize_tuple<V>(
        self,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        let vals = match self {
            Value::Map(m) => {
                let mut v = m
                    .into_iter()
                    .map(|(k, v)| match k {
                        Key::Int(i) => (i, v),
                        _ => panic!("unexpected key type"),
                    })
                    .collect::<Vec<(i64, Value)>>();
                v.sort_by_key(|(k, _)| *k);
                v.into_iter().map(|(_, v)| v).collect()
            }
            v => {
                return Err(DeserializeError::DeserializationError(format!(
                    "unexpected value: {v:?}"
                )))
            }
        };

        let seq = SeqDeserializer::new(vals);
        visitor.visit_seq(seq)
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.deserialize_tuple(len, visitor)
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        let m = match self {
            Value::Map(m) => m,
            v => {
                return Err(DeserializeError::DeserializationError(format!(
                    "unexpected value: {v:?}",
                )))
            }
        };

        visitor.visit_map(MapDeserializer::new(m))
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }

    fn deserialize_identifier<V>(
        self,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.deserialize_string(visitor)
    }

    fn deserialize_ignored_any<V>(
        self,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        drop(self);
        visitor.visit_unit()
    }
}
