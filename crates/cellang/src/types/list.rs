use super::{Value, ValueType};
use miette::Error;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Deserializer};
use serde::{Serialize, ser::Serializer};
use std::fmt;
use std::ops::{Deref, DerefMut};
use std::slice::{Iter, IterMut};
use std::vec::{self};

/// Wrapper for [Vec](https://doc.rust-lang.org/std/vec/struct.Vec.html) that
/// can only contain `Value`.
/// It also stores the type of the elements.
/// The type is checked when inserting a new element.
#[derive(Debug, PartialEq, Clone)]
pub struct List {
    elem_type: Option<ValueType>,
    inner: Vec<Value>,
}

impl Deref for List {
    type Target = [Value];

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for List {
    fn deref_mut(&mut self) -> &mut [Value] {
        self.inner.deref_mut()
    }
}

impl List {
    /// Creates a new empty list without a type.
    /// First push will set the type.
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

    /// Wrapper for [iter](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.iter)
    #[inline]
    pub fn iter(&self) -> Iter<'_, Value> {
        self.inner.iter()
    }

    /// Wrapper for [iter_mut](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.iter_mut)
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, Value> {
        self.inner.iter_mut()
    }

    /// Wrapper for [first](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.first)
    #[inline]
    pub fn first(&self) -> Option<&Value> {
        self.inner.first()
    }

    /// Wrapper for [first_mut](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.first_mut)
    #[inline]
    pub fn first_mut(&mut self) -> Option<&mut Value> {
        self.inner.first_mut()
    }

    /// Wrapper for [last](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.last)
    #[inline]
    pub fn last(&self) -> Option<&Value> {
        self.inner.last()
    }

    /// Wrapper for [last_mut](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.last_mut)
    #[inline]
    pub fn last_mut(&mut self) -> Option<&mut Value> {
        self.inner.last_mut()
    }

    /// Wrapper for [reverse](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.reverse)
    #[inline]
    pub fn reverse(&mut self) {
        self.inner.reverse()
    }

    /// Wrapper for
    /// [rotate_left](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.rotate_left)
    #[inline]
    pub fn rotate_left(&mut self, mid: usize) {
        self.inner.rotate_left(mid)
    }

    /// Wrapper for
    /// [rotate_right](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.rotate_right)
    #[inline]
    pub fn rotate_right(&mut self, mid: usize) {
        self.inner.rotate_right(mid)
    }

    /// Wrapper for [fill](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.fill)
    #[inline]
    pub fn fill(&mut self, value: Value) {
        self.prepare_insert(&value).unwrap();
        self.inner.fill(value)
    }

    /// Converts the list into a type that implements `DeserializeOwned`.
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

    /// Wrapper for [is_empty](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.is_empty)
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Wrapper for [get](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.get)
    #[inline]
    pub fn get(&self, index: usize) -> Option<&Value> {
        self.inner.get(index)
    }

    /// Wrapper for [contains](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.contains)
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

    /// Wrapper for [append](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.append)
    #[inline]
    pub fn append(&mut self, other: &mut List) -> Result<&mut Self, Error> {
        if let Some(ref elem_type) = self.elem_type {
            if let Some(ref other_elem_type) = other.elem_type
                && *elem_type != *other_elem_type
            {
                miette::bail!(
                    "Invalid element type: {:?} and {:?}",
                    elem_type,
                    other_elem_type
                );
            }
        } else {
            self.elem_type = other.elem_type.take();
        }

        self.inner.append(&mut other.inner);
        Ok(self)
    }

    /// Wrapper for [push](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push)
    #[inline]
    pub fn push(&mut self, value: Value) -> Result<&mut Self, Error> {
        self.prepare_insert(&value)?;
        self.inner.push(value);
        Ok(self)
    }

    /// Wrapper for [drain](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.drain)
    #[inline]
    pub fn drain<R>(&mut self, range: R) -> vec::Drain<'_, Value>
    where
        R: std::ops::RangeBounds<usize>,
    {
        self.inner.drain(range)
    }

    /// Wrapper for [as_mut_ptr](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_mut_ptr)
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut Value {
        self.inner.as_mut_ptr()
    }

    /// Wrapper for [as_mut_slice](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_mut_slice)
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [Value] {
        self.inner.as_mut_slice()
    }

    /// Wrapper for [as_ptr](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_ptr)
    #[inline]
    pub fn as_ptr(&self) -> *const Value {
        self.inner.as_ptr()
    }

    /// Wrapper for [as_slice](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_slice)
    #[inline]
    pub fn as_slice(&self) -> &[Value] {
        self.inner.as_slice()
    }

    /// Wrapper for [capacity](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.capacity)
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Wrapper for [clear](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.clear)
    /// It doesn't clear the list type.
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Wrapper for [dedup](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.dedup)
    #[inline]
    pub fn dedup(&mut self) {
        self.inner.dedup()
    }

    /// Wrapper for [dedup_by](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.dedup_by)
    #[inline]
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut Value, &mut Value) -> bool,
    {
        self.inner.dedup_by(same_bucket)
    }

    /// Wrapper for [dedup_by_key](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.dedup_by_key)
    #[inline]
    pub fn dedup_by_key<F, K>(&mut self, key: F)
    where
        F: FnMut(&mut Value) -> K,
        K: PartialEq<K>,
    {
        self.inner.dedup_by_key(key)
    }

    /// Wrapper for [extend_from_slice](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.extend_from_slice)
    #[inline]
    pub fn extend_from_slice(&mut self, other: &[Value]) -> Result<(), Error> {
        if other.is_empty() {
            return Ok(());
        }

        other.iter().try_for_each(|v| self.prepare_insert(v))?;
        self.inner.extend_from_slice(other);
        Ok(())
    }

    /// Wrapper for [extend_from_within](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.extend_from_within)
    #[inline]
    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: std::ops::RangeBounds<usize>,
    {
        self.inner.extend_from_within(src);
    }

    /// Wrapper for [insert](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.insert)
    #[inline]
    pub fn insert(&mut self, index: usize, element: Value) {
        self.prepare_insert(&element).unwrap();
        self.inner.insert(index, element)
    }

    /// Wrapper for [into_boxed_slice](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.into_boxed_slice)
    #[inline]
    pub fn into_boxed_slice(self) -> Box<[Value]> {
        self.inner.into_boxed_slice()
    }

    /// Wrapper for [leak](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.leak)
    #[inline]
    pub fn leak<'a>(self) -> &'a [Value] {
        self.inner.leak()
    }

    /// Wrapper for [pop](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.pop)
    #[inline]
    pub fn pop(&mut self) -> Option<Value> {
        self.inner.pop()
    }

    /// Wrapper for [remove](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.remove)
    #[inline]
    pub fn remove(&mut self, index: usize) -> Value {
        self.inner.remove(index)
    }

    /// Wrapper for [reserve](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.reserve)
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Wrapper for [reserve_exact](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.reserve_exact)
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    /// Wrapper for [resize](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.resize)
    #[inline]
    pub fn resize(&mut self, new_len: usize, value: Value) {
        self.prepare_insert(&value).unwrap();
        self.inner.resize(new_len, value)
    }

    /// Wrapper for [resize_with](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.resize_with)
    #[inline]
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> Value,
    {
        self.inner.resize_with(new_len, f)
    }

    /// Wrapper for [retain](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.retain)
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Value) -> bool,
    {
        self.inner.retain(|v| f(v))
    }

    /// Wrapper for [retain_mut](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.retain_mut)
    #[inline]
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Value) -> bool,
    {
        self.inner.retain_mut(|v| f(v))
    }

    /// Wrapper for [shrink_to](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.shrink_to)
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity)
    }

    /// Wrapper for [shrink_to_fit](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.shrink_to_fit)
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

    /// Wrapper for [split_off](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.split_off)
    #[inline]
    pub fn split_off(&mut self, at: usize) -> List {
        List {
            elem_type: self.elem_type.clone(),
            inner: self.inner.split_off(at),
        }
    }

    /// Wrapper for [swap_remove](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.swap_remove)
    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> Value {
        self.inner.swap_remove(index)
    }

    /// Wrapper for [truncate](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.truncate)
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        self.inner.truncate(len)
    }

    /// Wrapper for [try_reserve](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.try_reserve)
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), Error> {
        match self.inner.try_reserve(additional) {
            Ok(_) => Ok(()),
            Err(e) => miette::bail!(e),
        }
    }

    /// Wrapper for [try_reserve_exact](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.try_reserve_exact)
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

    /// Wrapper for [with_capacity](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.with_capacity)
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

impl<T> TryFrom<Vec<T>> for List
where
    T: Into<Value>,
{
    type Error = Error;
    fn try_from(values: Vec<T>) -> Result<Self, Error> {
        if values.is_empty() {
            Ok(Self::new())
        } else {
            let mut list = List::with_capacity(values.len());
            for value in values {
                list.push(value.into())?;
            }
            Ok(list)
        }
    }
}

impl From<List> for Vec<Value> {
    fn from(list: List) -> Self {
        list.inner
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
        List::try_from(inner).map_err(serde::de::Error::custom)
    }
}

impl fmt::Display for List {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
