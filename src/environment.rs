use crate::functions::{size, type_fn};
use crate::types::{Key, Value};
use crate::{Function, Map};
use miette::Error;
use std::collections::HashMap;

pub struct Environment<'a> {
    pub variables: Map,
    pub functions: HashMap<String, Function>,
    pub parent: Option<&'a Environment<'a>>,
}

impl Default for Environment<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> Environment<'a> {
    /// The new returns a root environment.
    pub fn new() -> Self {
        Self {
            variables: Map::new(),
            functions: {
                let mut m = HashMap::new();
                m.insert("size".to_string(), Box::new(size) as Function);
                m.insert("type".to_string(), Box::new(type_fn) as Function);
                m
            },
            parent: None,
        }
    }

    pub fn new_child(&'a self) -> Self {
        Self {
            variables: Map::new(),
            functions: HashMap::new(),
            parent: Some(self),
        }
    }

    pub fn get_variable(&self, name: &Key) -> Result<Option<&Value>, Error> {
        if let Some(val) = self.variables.get(name)? {
            Ok(Some(val))
        } else if let Some(parent) = self.parent {
            parent.get_variable(name)
        } else {
            Ok(None)
        }
    }

    pub fn set_variable(&mut self, name: &str, value: Value) -> Result<&mut Self, Error> {
        self.variables
            .insert(Key::String(name.to_string()), value)?;
        Ok(self)
    }

    pub fn get_function(&self, name: &str) -> Option<&Function> {
        self.functions
            .get(name)
            .or_else(|| self.parent.and_then(|parent| parent.get_function(name)))
    }

    pub fn set_function(&mut self, name: &str, function: Function) {
        self.functions.insert(name.to_string(), function);
    }
}
