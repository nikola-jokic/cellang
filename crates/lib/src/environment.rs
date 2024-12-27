use crate::functions;
use crate::types::{Key, Value};
use crate::{Function, Map};
use miette::Error;
use std::collections::HashMap;

/// Environment builder can be used to gradually build up the environment.
pub struct EnvironmentBuilder<'a> {
    variables: Option<Map>,
    /// Option here is used to allow for child environments not to have functions.
    /// The root environment is responsible for always allocating this map and providing
    /// default functions.
    functions: Option<HashMap<String, Function>>,
    parent: Option<&'a Environment<'a>>,
}

/// The environment is a collection of variables and functions.
/// The environment can have a parent environment, which is used for scoping.
/// When looking up a variable or function, the environment will first look in its own variables
/// and functions. If the variable or function is not found, it will look in the parent
/// environment.
pub struct Environment<'a> {
    variables: Option<&'a Map>,
    functions: Option<&'a HashMap<String, Function>>,
    parent: Option<&'a Environment<'a>>,
}

impl<'a> Environment<'a> {
    pub fn child(&self) -> Self {
        Environment {
            variables: None,
            functions: None,
            parent: self.parent,
        }
    }

    pub fn set_variables(&mut self, variables: &'a Map) {
        self.variables = Some(variables);
    }
}

impl Environment<'_> {
    pub fn lookup_variable(&self, name: &Key) -> Option<&Value> {
        self.variables
            .and_then(|variables| variables.get(name).unwrap_or(None))
            .or_else(|| self.parent.and_then(|parent| parent.lookup_variable(name)))
    }

    pub fn lookup_function(&self, name: &str) -> Option<&Function> {
        self.functions
            .and_then(|functions| functions.get(name))
            .or_else(|| self.parent.and_then(|parent| parent.lookup_function(name)))
    }
}

impl Default for EnvironmentBuilder<'_> {
    fn default() -> Self {
        Self::root(None, None)
    }
}

impl<'a> EnvironmentBuilder<'a> {
    pub fn build(&'a self) -> Environment<'a> {
        Environment {
            variables: self.variables.as_ref(),
            functions: self.functions.as_ref(),
            parent: self.parent,
        }
    }
    /// The new returns a root environment.
    pub fn root(variables: Option<Map>, functions: Option<HashMap<String, Function>>) -> Self {
        Self {
            variables,
            functions: {
                let mut m = functions.unwrap_or_default();
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
                Some(m)
            },
            parent: None,
        }
    }

    /// Replaces the variables in the environment with the given variables.
    pub fn set_variables(self, variables: Option<Map>) -> Self {
        Self { variables, ..self }
    }

    /// Replaces the functions in the environment with the given functions.
    pub fn set_functions(self, functions: Option<HashMap<String, Function>>) -> Self {
        Self { functions, ..self }
    }

    pub fn set_variable(&mut self, name: Key, value: Value) -> Result<(), Error> {
        self.variables
            .get_or_insert(Map::new())
            .insert(name, value)?;
        Ok(())
    }

    pub fn set_function(&mut self, name: &str, function: Function) {
        self.functions
            .get_or_insert(HashMap::new())
            .insert(name.to_string(), function);
    }
}
