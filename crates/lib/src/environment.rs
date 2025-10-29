use crate::types::{Key, Value};
use crate::{Function, Map};
use crate::{TryIntoValue, functions};
use miette::Error;
use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, OnceLock};

/// The environment is a collection of variables and functions.
/// The environment can have a parent environment, which is used for scoping.
/// When looking up a variable or function, the environment will first look in its own variables
/// and functions. If the variable or function is not found, it will look in the parent
/// environment.
#[derive(Clone)]
pub struct Environment<'a> {
    variables: Option<&'a Map>,
    functions: Option<&'a HashMap<String, Function>>,
    parent: Option<&'a Environment<'a>>,
}

impl fmt::Debug for Environment<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Environment")
            .field("variables", &self.variables)
            .field(
                "functions",
                &self
                    .functions
                    .as_ref()
                    .map(|v| v.keys().collect::<Vec<_>>()),
            )
            .field("parent", &self.parent)
            .finish()
    }
}

impl<'a> Environment<'a> {
    /// Creates a root environment with empty variables and only default functions.
    pub fn root() -> Environment<'a> {
        Environment {
            variables: None,
            functions: Some(default_functions()),
            parent: None,
        }
    }

    /// Creates a new child environment with empty variables and functions.
    pub fn child_builder(&'_ self) -> EnvironmentBuilder<'_> {
        EnvironmentBuilder {
            variables: None,
            functions: None,
            parent: self.parent,
        }
    }

    /// Creates a new child environment with empty variables and functions.
    /// If you need to set variables gradually, use child_builder instead.
    pub fn child(&'a self) -> Environment<'a> {
        Environment {
            variables: None,
            functions: None,
            parent: Some(self),
        }
    }

    /// Sets the variables in the environment. This is useful especially
    /// when evaluating sub-expressions. For example, a.b would evaluate
    /// a first, then would create new environment with a map set to it,
    /// and then evaluate b in that environment.
    ///
    /// This can be also acomplished by creating a new child environment
    /// with the EnvironmentBuilder, but since the map is already allocated,
    /// and stored inside the interpreter, it is more efficient to set it
    /// than to clone it.
    pub fn set_variables(&mut self, variables: &'a Map) {
        self.variables = Some(variables);
    }

    pub fn variables(&self) -> Option<&'a Map> {
        self.variables
    }

    pub fn functions(&self) -> Option<&'a HashMap<String, Function>> {
        self.functions
    }

    pub fn parent(&self) -> Option<&'a Environment<'a>> {
        self.parent
    }
}

impl Environment<'_> {
    pub fn lookup_variable<K>(&self, name: K) -> Option<&Value>
    where
        K: Into<Key>,
    {
        let name = name.into();
        self.variables
            .and_then(|variables| variables.get(&name).unwrap_or(None))
            .or_else(|| {
                self.parent.and_then(|parent| parent.lookup_variable(name))
            })
    }

    pub fn lookup_function(&self, name: &str) -> Option<&Function> {
        self.functions
            .and_then(|functions| functions.get(name))
            .or_else(|| {
                self.parent.and_then(|parent| parent.lookup_function(name))
            })
    }
}

/// standard functions exposed by each environment, created during root environment creation
pub fn default_functions() -> &'static HashMap<String, Function> {
    static FUNCTIONS: OnceLock<HashMap<String, Function>> = OnceLock::new();
    FUNCTIONS.get_or_init(|| {
        let mut m = HashMap::new();
        m.insert("size".to_string(), Arc::new(functions::size) as Function);
        m.insert("type".to_string(), Arc::new(functions::type_fn) as Function);
        m.insert("has".to_string(), Arc::new(functions::has) as Function);
        m.insert("all".to_string(), Arc::new(functions::all) as Function);
        m.insert(
            "exists".to_string(),
            Arc::new(functions::exists) as Function,
        );
        m.insert(
            "exists_one".to_string(),
            Arc::new(functions::exists_one) as Function,
        );
        m.insert("map".to_string(), Arc::new(functions::map) as Function);
        m.insert(
            "filter".to_string(),
            Arc::new(functions::filter) as Function,
        );
        m.insert(
            "contains".to_string(),
            Arc::new(functions::contains) as Function,
        );
        m.insert(
            "startsWith".to_string(), // for some reason, this is cammel case in spec
            Arc::new(functions::starts_with) as Function,
        );
        m.insert(
            "endsWith".to_string(),
            Arc::new(functions::ends_with) as Function,
        );
        m.insert(
            "matches".to_string(),
            Arc::new(functions::matches) as Function,
        );
        m.insert("int".to_string(), Arc::new(functions::int) as Function);
        m.insert("uint".to_string(), Arc::new(functions::uint) as Function);
        m.insert(
            "string".to_string(),
            Arc::new(functions::string) as Function,
        );
        m.insert(
            "timestamp".to_string(),
            Arc::new(functions::timestamp) as Function,
        );
        m.insert(
            "duration".to_string(),
            Arc::new(functions::duration) as Function,
        );
        m
    })
}

/// Environment builder can be used to gradually build up the environment.
#[derive(Clone)]
pub struct EnvironmentBuilder<'a> {
    variables: Option<Map>,
    /// Option here is used to allow for child environments not to have functions.
    /// The root environment is responsible for always allocating this map and providing
    /// default functions.
    functions: Option<HashMap<String, Function>>,
    parent: Option<&'a Environment<'a>>,
}

impl fmt::Debug for EnvironmentBuilder<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EnvironmentBuilder")
            .field("variables", &self.variables)
            .field(
                "functions",
                &self
                    .functions
                    .as_ref()
                    .map(|v| v.keys().collect::<Vec<_>>()),
            )
            .field("parent", &self.parent)
            .finish()
    }
}

impl Default for EnvironmentBuilder<'_> {
    fn default() -> Self {
        Self::root(None, None)
    }
}

impl<'a> EnvironmentBuilder<'a> {
    /// The new returns a root environment.
    pub fn root(
        variables: Option<Map>,
        functions: Option<HashMap<String, Function>>,
    ) -> Self {
        Self {
            variables,
            functions: {
                let mut m = functions.unwrap_or_default();
                m.extend(default_functions().clone());
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
    /// This can override the default functions.
    pub fn set_functions(
        self,
        functions: Option<HashMap<String, Function>>,
    ) -> Self {
        Self { functions, ..self }
    }

    /// Sets a variable in the environment variables map.
    pub fn set_variable<K, V>(&mut self, name: K, value: V) -> Result<(), Error>
    where
        K: Into<Key>,
        V: TryIntoValue,
    {
        self.variables.get_or_insert(Map::new()).insert(
            name.into(),
            value.try_into_value().map_err(|err| {
                miette::miette!("Failed to convert value {err:?}")
            })?,
        )?;
        Ok(())
    }

    /// Sets a function in the environment function map.
    pub fn set_function(&mut self, name: &str, function: Function) {
        self.functions
            .get_or_insert(HashMap::new())
            .insert(name.to_string(), function);
    }

    pub fn take_variables(&mut self) -> Option<Map> {
        self.variables.take()
    }

    pub fn take_functions(&mut self) -> Option<HashMap<String, Function>> {
        self.functions.take()
    }

    /// Builds the environment. It holds a reference to the environment builder so it can
    /// reference the environment maps without allocations.
    pub fn build(&'a self) -> Environment<'a> {
        Environment {
            variables: self.variables.as_ref(),
            functions: self.functions.as_ref(),
            parent: self.parent,
        }
    }
}
