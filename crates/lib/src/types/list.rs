use super::{Value, ValueKind};
use miette::Error;
use serde::{ser::Serializer, Serialize};
use serde::{Deserialize, Deserializer};
use std::fmt;
use std::vec;

#[derive(Debug, PartialEq, Clone)]
pub struct List {
    elem_type: Option<ValueKind>,
    inner: Vec<Value>,
}

impl<T> From<Vec<T>> for List
where
    T: Into<Value>,
{
    fn from(values: Vec<T>) -> Self {
        if values.is_empty() {
            Self::new()
        } else {
            let mut list = List::with_capacity(values.len());
            list.inner = values.into_iter().map(Into::into).collect();
            list.elem_type = list.inner.first().map(Value::kind);
            list
        }
    }
}

impl List {
    pub fn new() -> Self {
        Self {
            elem_type: None,
            inner: Vec::new(),
        }
    }

    pub fn element_type(&self) -> Option<ValueKind> {
        self.elem_type.clone()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Value> {
        self.inner.iter()
    }

    pub fn with_type(elem_type: ValueKind) -> Self {
        Self {
            elem_type: Some(elem_type),
            inner: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&Value> {
        self.inner.get(index)
    }

    pub fn contains(&self, value: &Value) -> Result<bool, Error> {
        match self.elem_type {
            None => Ok(false),
            Some(ref elem_type) => {
                if *elem_type != value.kind() {
                    miette::bail!("Invalid element type: {:?}", value.kind());
                }

                Ok(self.inner.contains(value))
            }
        }
    }

    pub fn append(&mut self, other: &mut List) -> Result<&mut Self, Error> {
        if let Some(ref elem_type) = self.elem_type {
            if let Some(ref other_elem_type) = other.elem_type {
                if *elem_type != *other_elem_type {
                    miette::bail!(
                        "Invalid element type: {:?} and {:?}",
                        elem_type,
                        other_elem_type
                    );
                }
            }
        } else {
            self.elem_type = other.elem_type.take();
        }

        self.inner.append(&mut other.inner);
        Ok(self)
    }

    pub fn push(&mut self, value: Value) -> Result<&mut Self, Error> {
        self.prepare_insert(&value)?;
        self.inner.push(value);
        Ok(self)
    }

    pub fn drain<R>(&mut self, range: R) -> vec::Drain<'_, Value>
    where
        R: std::ops::RangeBounds<usize>,
    {
        self.inner.drain(range)
    }

    pub fn as_mut_ptr(&mut self) -> *mut Value {
        self.inner.as_mut_ptr()
    }

    pub fn as_mut_slice(&mut self) -> &mut [Value] {
        self.inner.as_mut_slice()
    }

    pub fn as_ptr(&self) -> *const Value {
        self.inner.as_ptr()
    }

    pub fn as_slice(&self) -> &[Value] {
        self.inner.as_slice()
    }

    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    pub fn clear(&mut self) {
        self.inner.clear();
    }

    pub fn dedup(&mut self) {
        self.inner.dedup()
    }

    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut Value, &mut Value) -> bool,
    {
        self.inner.dedup_by(same_bucket)
    }

    pub fn dedup_by_key<F, K>(&mut self, key: F)
    where
        F: FnMut(&mut Value) -> K,
        K: PartialEq<K>,
    {
        self.inner.dedup_by_key(key)
    }

    pub fn extend_from_slice(&mut self, other: &[Value]) -> Result<(), Error> {
        if other.is_empty() {
            return Ok(());
        }

        other.iter().try_for_each(|v| self.prepare_insert(v))?;
        self.inner.extend_from_slice(other);
        Ok(())
    }

    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: std::ops::RangeBounds<usize>,
    {
        self.inner.extend_from_within(src);
    }

    pub fn insert(&mut self, index: usize, element: Value) {
        self.prepare_insert(&element).unwrap();
        self.inner.insert(index, element)
    }

    pub fn into_boxed_slice(self) -> Box<[Value]> {
        self.inner.into_boxed_slice()
    }

    pub fn leak<'a>(self) -> &'a [Value] {
        self.inner.leak()
    }

    pub fn pop(&mut self) -> Option<Value> {
        self.inner.pop()
    }

    pub fn remove(&mut self, index: usize) -> Value {
        self.inner.remove(index)
    }

    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    pub fn resize(&mut self, new_len: usize, value: Value) {
        self.prepare_insert(&value).unwrap();
        self.inner.resize(new_len, value)
    }

    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> Value,
    {
        self.inner.resize_with(new_len, f)
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Value) -> bool,
    {
        self.inner.retain(|v| f(v))
    }

    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Value) -> bool,
    {
        self.inner.retain_mut(|v| f(v))
    }

    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity)
    }

    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

    pub fn split_off(&mut self, at: usize) -> List {
        List {
            elem_type: self.elem_type.clone(),
            inner: self.inner.split_off(at),
        }
    }

    pub fn swap_remove(&mut self, index: usize) -> Value {
        self.inner.swap_remove(index)
    }

    pub fn truncate(&mut self, len: usize) {
        self.inner.truncate(len)
    }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), Error> {
        match self.inner.try_reserve(additional) {
            Ok(_) => Ok(()),
            Err(e) => miette::bail!(e),
        }
    }

    pub fn try_reserve_exact(
        &mut self,
        additional: usize,
    ) -> Result<(), Error> {
        match self.inner.try_reserve_exact(additional) {
            Ok(_) => Ok(()),
            Err(e) => miette::bail!(e),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            elem_type: None,
            inner: Vec::with_capacity(capacity),
        }
    }

    pub fn with_type_and_capacity(
        elem_type: ValueKind,
        capacity: usize,
    ) -> Self {
        Self {
            elem_type: Some(elem_type),
            inner: Vec::with_capacity(capacity),
        }
    }

    fn prepare_insert(&mut self, other: &Value) -> Result<(), Error> {
        match self.elem_type {
            None => {
                self.elem_type = Some(other.kind());
            }
            Some(ref elem_type) => {
                if *elem_type != other.kind() {
                    miette::bail!("Invalid element type: {:?}", other.kind());
                }
            }
        }
        Ok(())
    }
}

impl IntoIterator for List {
    type Item = Value;
    type IntoIter = vec::IntoIter<Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl Default for List {
    fn default() -> Self {
        Self::new()
    }
}

impl Serialize for List {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.inner.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for List {
    fn deserialize<D>(deserializer: D) -> Result<List, D::Error>
    where
        D: Deserializer<'de>,
    {
        let inner: Vec<serde_json::Value> = Vec::deserialize(deserializer)?;
        Ok(List::from(inner))
    }
}

impl fmt::Display for List {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        for (i, value) in self.inner.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", value)?;
        }
        write!(f, "]")
    }
}
