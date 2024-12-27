use crate::functions;
use crate::types::{Key, Value};
use crate::{Function, Map};
use miette::Error;
use std::collections::HashMap;

/// Environment builder can be used to gradually build up the environment.
pub struct EnvironmentBuilder<'a> {
    variables: Map,
    functions: HashMap<String, Function>,
    parent: Option<&'a Environment<'a>>,
}

/// The environment is a collection of variables and functions.
/// The environment can have a parent environment, which is used for scoping.
/// When looking up a variable or function, the environment will first look in its own variables
/// and functions. If the variable or function is not found, it will look in the parent
/// environment.
pub struct Environment<'a> {
    variables: &'a Map,
    functions: &'a HashMap<String, Function>,
    parent: Option<&'a Environment<'a>>,
}

impl<'a> Environment<'a> {
    pub fn child(&self) -> Self {
        Environment {
            variables: self.variables,
            functions: self.functions,
            parent: self.parent,
        }
    }

    pub fn set_variables(&mut self, variables: &'a Map) {
        self.variables = variables;
    }
}

impl<'a> Environment<'a> {
    pub fn lookup_variable(&self, name: &Key) -> Result<Option<&Value>, Error> {
        if let Some(val) = self.variables.get(name)? {
            Ok(Some(val))
        } else if let Some(parent) = self.parent {
            parent.lookup_variable(name)
        } else {
            Ok(None)
        }
    }

    pub fn lookup_function(&self, name: &str) -> Option<&Function> {
        self.functions
            .get(name)
            .or_else(|| self.parent.and_then(|parent| parent.lookup_function(name)))
    }
}

impl Default for EnvironmentBuilder<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> EnvironmentBuilder<'a> {
    pub fn to_sealed(&'a self) -> Environment<'a> {
        Environment {
            variables: &self.variables,
            functions: &self.functions,
            parent: self.parent,
        }
    }
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
                m.insert(
                    "int".to_string(), // for some reason, this is cammel case in spec
                    Box::new(functions::int) as Function,
                );
                m.insert(
                    "uint".to_string(), // for some reason, this is cammel case in spec
                    Box::new(functions::uint) as Function,
                );
                m.insert(
                    "string".to_string(), // for some reason, this is cammel case in spec
                    Box::new(functions::string) as Function,
                );
                m.insert(
                    "timestamp".to_string(),
                    Box::new(functions::timestamp) as Function,
                );
                m.insert("dyn".to_string(), Box::new(functions::dyn_fn) as Function);
                m.insert(
                    "duration".to_string(),
                    Box::new(functions::duration) as Function,
                );
                m
            },
            parent: None,
        }
    }

    /// Replaces the variables in the environment with the given variables.
    pub fn with_variables(self, variables: Map) -> Self {
        Self { variables, ..self }
    }

    /// Replaces the functions in the environment with the given functions.
    pub fn with_functions(self, functions: HashMap<String, Function>) -> Self {
        Self { functions, ..self }
    }

    /// Looks up the variable with the given name in the environment, going from the current
    /// environment to the parent environment.
    pub fn lookup_variable(&self, name: &Key) -> Result<Option<&Value>, Error> {
        if let Some(val) = self.variables.get(name)? {
            Ok(Some(val))
        } else if let Some(parent) = self.parent {
            parent.lookup_variable(name)
        } else {
            Ok(None)
        }
    }

    pub fn set_variable(&mut self, name: Key, value: Value) -> Result<&mut Self, Error> {
        self.variables.insert(name, value)?;
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
