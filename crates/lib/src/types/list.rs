use super::{Value, ValueType};
use miette::Error;
use serde::de::DeserializeOwned;
use serde::{ser::Serializer, Serialize};
use serde::{Deserialize, Deserializer};
use std::fmt;
use std::vec;

#[derive(Debug, PartialEq, Clone)]
pub struct List {
    elem_type: Option<ValueType>,
    inner: Vec<Value>,
}

impl List {
    pub fn new() -> Self {
        Self {
            elem_type: None,
            inner: Vec::new(),
        }
    }

    #[inline]
    pub fn inner(&self) -> &Vec<Value> {
        &self.inner
    }

    #[inline]
    pub fn element_type(&self) -> Option<ValueType> {
        self.elem_type.clone()
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &Value> {
        self.inner.iter()
    }

    #[inline]
    pub fn try_into<T>(self) -> Result<T, Error>
    where
        T: DeserializeOwned,
    {
        crate::try_from_list(self)
    }

    #[inline]
    pub fn with_type(elem_type: ValueType) -> Self {
        Self {
            elem_type: Some(elem_type),
            inner: Vec::new(),
        }
    }

    /// Returns the number of elements in the list.
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<&Value> {
        self.inner.get(index)
    }

    #[inline]
    pub fn contains(&self, value: &Value) -> Result<bool, Error> {
        match self.elem_type {
            None => Ok(false),
            Some(ref elem_type) => {
                if *elem_type != value.type_of() {
                    miette::bail!(
                        "Invalid element type: {:?}",
                        value.type_of()
                    );
                }

                Ok(self.inner.contains(value))
            }
        }
    }

    #[inline]
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

    #[inline]
    pub fn push(&mut self, value: Value) -> Result<&mut Self, Error> {
        self.prepare_insert(&value)?;
        self.inner.push(value);
        Ok(self)
    }

    #[inline]
    pub fn drain<R>(&mut self, range: R) -> vec::Drain<'_, Value>
    where
        R: std::ops::RangeBounds<usize>,
    {
        self.inner.drain(range)
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut Value {
        self.inner.as_mut_ptr()
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [Value] {
        self.inner.as_mut_slice()
    }

    #[inline]
    pub fn as_ptr(&self) -> *const Value {
        self.inner.as_ptr()
    }

    #[inline]
    pub fn as_slice(&self) -> &[Value] {
        self.inner.as_slice()
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    #[inline]
    pub fn dedup(&mut self) {
        self.inner.dedup()
    }

    #[inline]
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut Value, &mut Value) -> bool,
    {
        self.inner.dedup_by(same_bucket)
    }

    #[inline]
    pub fn dedup_by_key<F, K>(&mut self, key: F)
    where
        F: FnMut(&mut Value) -> K,
        K: PartialEq<K>,
    {
        self.inner.dedup_by_key(key)
    }

    #[inline]
    pub fn extend_from_slice(&mut self, other: &[Value]) -> Result<(), Error> {
        if other.is_empty() {
            return Ok(());
        }

        other.iter().try_for_each(|v| self.prepare_insert(v))?;
        self.inner.extend_from_slice(other);
        Ok(())
    }

    #[inline]
    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: std::ops::RangeBounds<usize>,
    {
        self.inner.extend_from_within(src);
    }

    #[inline]
    pub fn insert(&mut self, index: usize, element: Value) {
        self.prepare_insert(&element).unwrap();
        self.inner.insert(index, element)
    }

    #[inline]
    pub fn into_boxed_slice(self) -> Box<[Value]> {
        self.inner.into_boxed_slice()
    }

    #[inline]
    pub fn leak<'a>(self) -> &'a [Value] {
        self.inner.leak()
    }

    #[inline]
    pub fn pop(&mut self) -> Option<Value> {
        self.inner.pop()
    }

    #[inline]
    pub fn remove(&mut self, index: usize) -> Value {
        self.inner.remove(index)
    }

    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    #[inline]
    pub fn resize(&mut self, new_len: usize, value: Value) {
        self.prepare_insert(&value).unwrap();
        self.inner.resize(new_len, value)
    }

    #[inline]
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> Value,
    {
        self.inner.resize_with(new_len, f)
    }

    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Value) -> bool,
    {
        self.inner.retain(|v| f(v))
    }

    #[inline]
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Value) -> bool,
    {
        self.inner.retain_mut(|v| f(v))
    }

    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity)
    }

    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

    #[inline]
    pub fn split_off(&mut self, at: usize) -> List {
        List {
            elem_type: self.elem_type.clone(),
            inner: self.inner.split_off(at),
        }
    }

    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> Value {
        self.inner.swap_remove(index)
    }

    #[inline]
    pub fn truncate(&mut self, len: usize) {
        self.inner.truncate(len)
    }

    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), Error> {
        match self.inner.try_reserve(additional) {
            Ok(_) => Ok(()),
            Err(e) => miette::bail!(e),
        }
    }

    #[inline]
    pub fn try_reserve_exact(
        &mut self,
        additional: usize,
    ) -> Result<(), Error> {
        match self.inner.try_reserve_exact(additional) {
            Ok(_) => Ok(()),
            Err(e) => miette::bail!(e),
        }
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            elem_type: None,
            inner: Vec::with_capacity(capacity),
        }
    }

    #[inline]
    pub fn with_type_and_capacity(
        elem_type: ValueType,
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
                self.elem_type = Some(other.type_of());
            }
            Some(ref elem_type) => {
                if *elem_type != other.type_of() {
                    miette::bail!(
                        "Invalid element type: {:?}",
                        other.type_of()
                    );
                }
            }
        }
        Ok(())
    }
}

impl Extend<Value> for List {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = Value>,
    {
        for value in iter {
            self.push(value).unwrap();
        }
    }
}

impl FromIterator<Value> for List {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Value>,
    {
        let mut list = List::new();
        list.extend(iter);
        list
    }
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
            list.elem_type = list.inner.first().map(Value::type_of);
            list
        }
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
        let inner: Vec<Value> = Vec::deserialize(deserializer)?;
        Ok(List::from(inner))
    }
}

impl fmt::Display for List {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
