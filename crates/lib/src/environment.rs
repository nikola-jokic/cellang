use crate::functions;
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
                m.insert("size".to_string(), Box::new(functions::size) as Function);
                m.insert("type".to_string(), Box::new(functions::type_fn) as Function);
                m.insert("has".to_string(), Box::new(functions::has) as Function);
                m.insert("all".to_string(), Box::new(functions::all) as Function);
                m.insert(
                    "exists".to_string(),
                    Box::new(functions::exists) as Function,
                );
                m.insert(
                    "exists_one".to_string(),
                    Box::new(functions::exists_one) as Function,
                );
                m.insert("map".to_string(), Box::new(functions::map) as Function);
                m.insert(
                    "filter".to_string(),
                    Box::new(functions::filter) as Function,
                );
                m.insert(
                    "contains".to_string(),
                    Box::new(functions::contains) as Function,
                );
                m.insert(
                    "startsWith".to_string(), // for some reason, this is cammel case in spec
                    Box::new(functions::starts_with) as Function,
                );
                m.insert(
                    "matches".to_string(),
                    Box::new(functions::matches) as Function,
                );
                m
            },
            parent: None,
        }
    }

    pub fn child(&'a self) -> Self {
        Self {
            variables: Map::new(),
            functions: HashMap::new(),
            parent: Some(self),
        }
    }

    pub fn with_variables(self, variables: Map) -> Self {
        Self { variables, ..self }
    }

    pub fn with_functions(self, functions: HashMap<String, Function>) -> Self {
        Self { functions, ..self }
    }

    pub fn with_parent(self, parent: &'a Environment<'a>) -> Self {
        Self {
            parent: Some(parent),
            ..self
        }
    }

    pub fn lookup_variable(&self, name: &Key) -> Result<Option<&Value>, Error> {
        if let Some(val) = self.variables.get(name)? {
            Ok(Some(val))
        } else if let Some(parent) = self.parent {
            parent.lookup_variable(name)
        } else {
            Ok(None)
        }
    }

    pub fn set_variable(&mut self, name: &str, value: Value) -> Result<&mut Self, Error> {
        self.variables
            .insert(Key::String(name.to_string()), value)?;
        Ok(self)
    }

    pub fn lookup_function(&self, name: &str) -> Option<&Function> {
        self.functions
            .get(name)
            .or_else(|| self.parent.and_then(|parent| parent.lookup_function(name)))
    }

    pub fn set_function(&mut self, name: &str, function: Function) {
        self.functions.insert(name.to_string(), function);
    }
}
