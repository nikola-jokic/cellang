use super::{Key, List, Map, Value};
use thiserror::Error;

#[derive(Error, Debug, PartialEq, Clone)]
pub enum SerializeError {
    #[error("Invalid key {0}")]
    InvalidKey(String),
    #[error("Serde error: {0}")]
    SerdeError(String),
}

impl serde::ser::Error for SerializeError {
    fn custom<T: std::fmt::Display>(msg: T) -> Self {
        SerializeError::SerdeError(msg.to_string())
    }
}

pub(crate) struct SerializeSeq {
    inner: Vec<Value>,
}

impl serde::ser::SerializeSeq for SerializeSeq {
    type Ok = Value;
    type Error = SerializeError;

    fn serialize_element<T: ?Sized + serde::Serialize>(
        &mut self,
        value: &T,
    ) -> Result<(), SerializeError> {
        self.inner.push(value.serialize(Serializer)?);
        Ok(())
    }

    fn end(self) -> Result<Value, SerializeError> {
        Ok(Value::List(match List::try_from(self.inner) {
            Ok(list) => list,
            Err(err) => {
                return Err(SerializeError::InvalidKey(err.to_string()))
            }
        }))
    }
}

impl serde::ser::SerializeTuple for SerializeSeq {
    type Ok = Value;
    type Error = SerializeError;

    fn serialize_element<T: ?Sized + serde::Serialize>(
        &mut self,
        value: &T,
    ) -> Result<(), SerializeError> {
        self.inner.push(value.serialize(Serializer)?);
        Ok(())
    }

    fn end(self) -> Result<Value, SerializeError> {
        let mut m = Map::new();
        for (i, v) in self.inner.into_iter().enumerate() {
            let key = Key::from(i as i64);
            m.insert(key, v)
                .map_err(|err| SerializeError::InvalidKey(err.to_string()))?;
        }
        Ok(Value::Map(m))
    }
}

impl serde::ser::SerializeTupleStruct for SerializeSeq {
    type Ok = Value;
    type Error = SerializeError;

    fn serialize_field<T: ?Sized + serde::Serialize>(
        &mut self,
        value: &T,
    ) -> Result<(), SerializeError> {
        self.inner.push(value.serialize(Serializer)?);
        Ok(())
    }

    fn end(self) -> Result<Value, SerializeError> {
        let mut m = Map::new();
        for (i, v) in self.inner.into_iter().enumerate() {
            let key = Key::from(i as i64);
            m.insert(key, v)
                .map_err(|err| SerializeError::InvalidKey(err.to_string()))?;
        }
        Ok(Value::Map(m))
    }
}

pub(crate) struct SerializeTupleVariant {
    key: Key,
    inner: Vec<Value>,
}

impl serde::ser::SerializeTupleVariant for SerializeTupleVariant {
    type Ok = Value;
    type Error = SerializeError;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + serde::Serialize,
    {
        self.inner.push(value.serialize(Serializer)?);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let mut m = Map::new();
        for (i, v) in self.inner.into_iter().enumerate() {
            let key = Key::from(i as i64);
            m.insert(key, v)
                .map_err(|err| SerializeError::InvalidKey(err.to_string()))?;
        }
        let value = Value::Map(m);
        let key = self.key;
        Ok(Value::Map(vec![(key, value)].into_iter().collect()))
    }
}

pub(crate) struct SerializeMap {
    keys: Vec<Key>,
    values: Vec<Value>,
}

impl serde::ser::SerializeMap for SerializeMap {
    type Ok = Value;
    type Error = SerializeError;

    fn serialize_key<T: ?Sized + serde::Serialize>(
        &mut self,
        key: &T,
    ) -> Result<(), SerializeError> {
        let key = key.serialize(Serializer)?;
        match Key::try_from(&key) {
            Ok(key) => self.keys.push(key),
            Err(_) => return Err(SerializeError::InvalidKey(key.to_string())),
        }
        Ok(())
    }

    fn serialize_value<T: ?Sized + serde::Serialize>(
        &mut self,
        value: &T,
    ) -> Result<(), SerializeError> {
        self.values.push(value.serialize(Serializer)?);
        Ok(())
    }

    fn end(self) -> Result<Value, SerializeError> {
        let mut map = Map::with_capacity(self.keys.len());
        for (key, value) in self.keys.into_iter().zip(self.values.into_iter()) {
            map.insert(key, value)
                .map_err(|err| SerializeError::InvalidKey(err.to_string()))?;
        }
        Ok(Value::Map(map))
    }
}

impl serde::ser::SerializeStruct for SerializeMap {
    type Ok = Value;
    type Error = SerializeError;

    fn serialize_field<T>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error>
    where
        T: ?Sized + serde::Serialize,
    {
        let key = Key::from(key);
        let value = value.serialize(Serializer)?;
        self.keys.push(key);
        self.values.push(value);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let mut map = Map::with_capacity(self.keys.len());
        for (key, value) in self.keys.into_iter().zip(self.values.into_iter()) {
            map.insert(key, value)
                .map_err(|err| SerializeError::InvalidKey(err.to_string()))?;
        }
        Ok(Value::Map(map))
    }
}

pub(crate) struct SerializeMapVariant {
    name: Key,
    keys: Vec<Key>,
    values: Vec<Value>,
}

impl serde::ser::SerializeStructVariant for SerializeMapVariant {
    type Ok = Value;
    type Error = SerializeError;

    fn serialize_field<T>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error>
    where
        T: ?Sized + serde::Serialize,
    {
        let key = Key::from(key);
        let value = value.serialize(Serializer)?;
        self.keys.push(key);
        self.values.push(value);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let mut map = Map::with_capacity(self.keys.len());
        for (key, value) in self.keys.into_iter().zip(self.values.into_iter()) {
            map.insert(key, value)
                .map_err(|err| SerializeError::InvalidKey(err.to_string()))?;
        }
        let key = self.name;
        Ok(Value::Map(
            vec![(key, Value::Map(map))].into_iter().collect(),
        ))
    }
}

pub(crate) struct Serializer;

impl serde::ser::Serializer for Serializer {
    type Ok = Value;
    type Error = SerializeError;

    // SerializeSeq produces a List<Value>
    type SerializeSeq = SerializeSeq;
    // SerializeTuple produces a Map<Key::Int, Value>
    type SerializeTuple = SerializeSeq;
    // SerializeTupleStruct produces a Map<Key::Int, Value>
    type SerializeTupleStruct = SerializeSeq;
    // SerializeTupleVariant produces a Map<Key::Int, Value>
    type SerializeTupleVariant = SerializeTupleVariant;
    type SerializeMap = SerializeMap;
    type SerializeStruct = SerializeMap;
    type SerializeStructVariant = SerializeMapVariant;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Bool(v))
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Int(v as i64))
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Int(v as i64))
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Int(v as i64))
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Int(v))
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Uint(v as u64))
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Uint(v as u64))
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Uint(v as u64))
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Uint(v))
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Double(v as f64))
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Double(v))
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        self.serialize_str(&v.to_string())
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        Ok(Value::String(v.to_string()))
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Bytes(v.to_vec()))
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Null)
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + serde::Serialize,
    {
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Null)
    }

    // struct Unit => null
    fn serialize_unit_struct(
        self,
        _name: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Ok(Value::Null)
    }

    /// enum E { V } => { "V": null }
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        let key = Key::from(variant);
        let value = Value::Null;
        Ok(Value::Map(vec![(key, value)].into_iter().collect()))
    }

    fn serialize_newtype_struct<T>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + serde::Serialize,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + serde::Serialize,
    {
        value.serialize(self)
    }

    fn serialize_seq(
        self,
        len: Option<usize>,
    ) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(SerializeSeq {
            inner: Vec::with_capacity(len.unwrap_or(0)),
        })
    }

    fn serialize_tuple(
        self,
        len: usize,
    ) -> Result<Self::SerializeTuple, Self::Error> {
        Ok(SerializeSeq {
            inner: Vec::with_capacity(len),
        })
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Ok(SerializeTupleVariant {
            key: Key::from(variant),
            inner: Vec::with_capacity(len),
        })
    }

    fn serialize_map(
        self,
        len: Option<usize>,
    ) -> Result<Self::SerializeMap, Self::Error> {
        Ok(SerializeMap {
            keys: Vec::with_capacity(len.unwrap_or(0)),
            values: Vec::with_capacity(len.unwrap_or(0)),
        })
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Ok(SerializeMap {
            keys: Vec::with_capacity(len),
            values: Vec::with_capacity(len),
        })
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Ok(SerializeMapVariant {
            name: Key::from(variant),
            keys: Vec::with_capacity(len),
            values: Vec::with_capacity(len),
        })
    }
}
