use crate::env::{Env, EnvBuilder};
use crate::error::{EnvError, RuntimeError};
use crate::types::{FunctionDecl, IdentDecl, NamedType};
use crate::value::{IntoValue, ListValue, TryFromValue, Value, ValueError};
use std::collections::BTreeMap;
use std::sync::Arc;

pub type NativeFunction = Arc<
    dyn Fn(&CallContext<'_>) -> Result<Value, RuntimeError> + Send + Sync + 'static,
>;

/// User facing runtime environment that stores variables, types and callable functions.
#[derive(Clone)]
pub struct Runtime {
    env: Env,
    variables: Arc<BTreeMap<String, Value>>,
    functions: Arc<BTreeMap<String, NativeFunction>>,
}

impl Runtime {
    pub fn builder() -> RuntimeBuilder {
        RuntimeBuilder::default()
    }

    pub fn env(&self) -> &Env {
        &self.env
    }

    pub fn variables(&self) -> &BTreeMap<String, Value> {
        self.variables.as_ref()
    }

    pub fn functions(&self) -> &BTreeMap<String, NativeFunction> {
        self.functions.as_ref()
    }

    pub fn child_builder(&self) -> RuntimeBuilder {
        RuntimeBuilder::from_runtime(self)
    }

    pub fn eval(&self, source: &str) -> Result<Value, RuntimeError> {
        crate::interpreter::eval(self, source)
    }

    pub fn get_variable(&self, name: &str) -> Option<&Value> {
        self.variables.get(name)
    }

    pub(crate) fn resolve_identifier(&self, name: &str) -> Option<Value> {
        if let Some(value) = self.variables.get(name) {
            return Some(value.clone());
        }
        self.env
            .lookup_ident(name)
            .and_then(|decl| decl.value.as_ref().map(Value::from))
    }

    pub(crate) fn lookup_function(&self, name: &str) -> Option<NativeFunction> {
        self.functions.get(name).cloned()
    }
}

/// Immutable view passed to native functions during invocation.
pub struct CallContext<'a> {
    runtime: &'a Runtime,
    args: &'a [Value],
}

impl<'a> CallContext<'a> {
    pub(crate) fn new(runtime: &'a Runtime, args: &'a [Value]) -> Self {
        Self { runtime, args }
    }

    pub fn runtime(&self) -> &'a Runtime {
        self.runtime
    }

    pub fn args(&self) -> &'a [Value] {
        self.args
    }

    pub fn arg(&self, index: usize) -> Option<&'a Value> {
        self.args.get(index)
    }
}

#[derive(Clone, Default)]
pub struct RuntimeBuilder {
    env_builder: EnvBuilder,
    variables: BTreeMap<String, Value>,
    functions: BTreeMap<String, NativeFunction>,
}

impl RuntimeBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_runtime(runtime: &Runtime) -> Self {
        let mut env_builder = Env::builder();
        env_builder
            .import_env(runtime.env())
            .expect("parent environment is always valid");
        RuntimeBuilder {
            env_builder,
            variables: runtime.variables.as_ref().clone(),
            functions: runtime
                .functions
                .iter()
                .map(|(name, fun)| (name.clone(), fun.clone()))
                .collect(),
        }
    }

    pub fn import_env(&mut self, env: &Env) -> Result<&mut Self, EnvError> {
        self.env_builder
            .import_env(env)
            .map_err(|err| EnvError::new(err.to_string()))?;
        Ok(self)
    }

    pub fn add_type(&mut self, ty: NamedType) -> Result<&mut Self, EnvError> {
        self.env_builder
            .add_type(ty)
            .map_err(|err| EnvError::new(err.to_string()))?;
        Ok(self)
    }

    pub fn add_ident(&mut self, ident: IdentDecl) -> Result<&mut Self, EnvError> {
        self.env_builder
            .add_ident(ident)
            .map_err(|err| EnvError::new(err.to_string()))?;
        Ok(self)
    }

    pub fn add_function_decl(
        &mut self,
        decl: FunctionDecl,
    ) -> Result<&mut Self, EnvError> {
        self.env_builder
            .add_function(decl)
            .map_err(|err| EnvError::new(err.to_string()))?;
        Ok(self)
    }

    pub fn set_variable<V>(&mut self, name: impl Into<String>, value: V) -> &mut Self
    where
        V: IntoValue,
    {
        self.variables.insert(name.into(), value.into_value());
        self
    }

    pub fn set_variables<I, K, V>(&mut self, entries: I) -> &mut Self
    where
        I: IntoIterator<Item = (K, V)>,
        K: Into<String>,
        V: IntoValue,
    {
        for (key, value) in entries {
            self.set_variable(key, value);
        }
        self
    }

    pub fn register_function<F, Args, Out>(
        &mut self,
        name: impl Into<String>,
        function: F,
    ) -> Result<&mut Self, RuntimeError>
    where
        F: IntoNativeFunction<Args, Out>,
    {
        let name = name.into();
        let native = function.into_native(name.clone());
        self.insert_function(name, native)
    }

    pub fn register_native_function(
        &mut self,
        name: impl Into<String>,
        function: NativeFunction,
    ) -> Result<&mut Self, RuntimeError> {
        self.insert_function(name.into(), function)
    }

    fn insert_function(
        &mut self,
        name: String,
        handler: NativeFunction,
    ) -> Result<&mut Self, RuntimeError> {
        if self.functions.contains_key(&name) {
            return Err(RuntimeError::new(format!(
                "Function '{name}' is already registered",
            )));
        }
        self.functions.insert(name, handler);
        Ok(self)
    }

    pub fn build(self) -> Runtime {
        Runtime {
            env: self.env_builder.build(),
            variables: Arc::new(self.variables),
            functions: Arc::new(self.functions),
        }
    }
}

pub trait IntoNativeFunction<Args, Out> {
    fn into_native(self, name: String) -> NativeFunction;
}

impl IntoNativeFunction<(), Value> for NativeFunction {
    fn into_native(self, _name: String) -> NativeFunction {
        self
    }
}

impl<F, R> IntoNativeFunction<(), R> for F
where
    F: Fn() -> R + Send + Sync + 'static,
    R: FunctionOutput,
{
    fn into_native(self, name: String) -> NativeFunction {
        let fname = name.clone();
        Arc::new(move |ctx| {
            if !ctx.args.is_empty() {
                return Err(RuntimeError::wrong_arity(&fname, 0, ctx.args.len()));
            }
            let result = self();
            result.into_runtime_result()
        })
    }
}

impl<F, R, A0> IntoNativeFunction<(A0,), R> for F
where
    F: Fn(A0) -> R + Send + Sync + 'static,
    R: FunctionOutput,
    A0: TryFromValue,
{
    fn into_native(self, name: String) -> NativeFunction {
        let fname = name.clone();
        Arc::new(move |ctx| {
            if ctx.args.len() != 1 {
                return Err(RuntimeError::wrong_arity(&fname, 1, ctx.args.len()));
            }
            let arg0 = A0::try_from_value(&ctx.args[0])
                .map_err(|err| RuntimeError::argument(&fname, 0, err))?;
            let result = self(arg0);
            result.into_runtime_result()
        })
    }
}

impl<F, R, A0, A1> IntoNativeFunction<(A0, A1), R> for F
where
    F: Fn(A0, A1) -> R + Send + Sync + 'static,
    R: FunctionOutput,
    A0: TryFromValue,
    A1: TryFromValue,
{
    fn into_native(self, name: String) -> NativeFunction {
        let fname = name.clone();
        Arc::new(move |ctx| {
            if ctx.args.len() != 2 {
                return Err(RuntimeError::wrong_arity(&fname, 2, ctx.args.len()));
            }
            let arg0 = A0::try_from_value(&ctx.args[0])
                .map_err(|err| RuntimeError::argument(&fname, 0, err))?;
            let arg1 = A1::try_from_value(&ctx.args[1])
                .map_err(|err| RuntimeError::argument(&fname, 1, err))?;
            let result = self(arg0, arg1);
            result.into_runtime_result()
        })
    }
}

impl<F, R, A0, A1, A2> IntoNativeFunction<(A0, A1, A2), R> for F
where
    F: Fn(A0, A1, A2) -> R + Send + Sync + 'static,
    R: FunctionOutput,
    A0: TryFromValue,
    A1: TryFromValue,
    A2: TryFromValue,
{
    fn into_native(self, name: String) -> NativeFunction {
        let fname = name.clone();
        Arc::new(move |ctx| {
            if ctx.args.len() != 3 {
                return Err(RuntimeError::wrong_arity(&fname, 3, ctx.args.len()));
            }
            let arg0 = A0::try_from_value(&ctx.args[0])
                .map_err(|err| RuntimeError::argument(&fname, 0, err))?;
            let arg1 = A1::try_from_value(&ctx.args[1])
                .map_err(|err| RuntimeError::argument(&fname, 1, err))?;
            let arg2 = A2::try_from_value(&ctx.args[2])
                .map_err(|err| RuntimeError::argument(&fname, 2, err))?;
            let result = self(arg0, arg1, arg2);
            result.into_runtime_result()
        })
    }
}

impl<F, R, A0, A1, A2, A3> IntoNativeFunction<(A0, A1, A2, A3), R> for F
where
    F: Fn(A0, A1, A2, A3) -> R + Send + Sync + 'static,
    R: FunctionOutput,
    A0: TryFromValue,
    A1: TryFromValue,
    A2: TryFromValue,
    A3: TryFromValue,
{
    fn into_native(self, name: String) -> NativeFunction {
        let fname = name.clone();
        Arc::new(move |ctx| {
            if ctx.args.len() != 4 {
                return Err(RuntimeError::wrong_arity(&fname, 4, ctx.args.len()));
            }
            let arg0 = A0::try_from_value(&ctx.args[0])
                .map_err(|err| RuntimeError::argument(&fname, 0, err))?;
            let arg1 = A1::try_from_value(&ctx.args[1])
                .map_err(|err| RuntimeError::argument(&fname, 1, err))?;
            let arg2 = A2::try_from_value(&ctx.args[2])
                .map_err(|err| RuntimeError::argument(&fname, 2, err))?;
            let arg3 = A3::try_from_value(&ctx.args[3])
                .map_err(|err| RuntimeError::argument(&fname, 3, err))?;
            let result = self(arg0, arg1, arg2, arg3);
            result.into_runtime_result()
        })
    }
}

pub trait FunctionOutput {
    fn into_runtime_result(self) -> Result<Value, RuntimeError>;
}

impl<R> FunctionOutput for R
where
    R: IntoValue,
{
    fn into_runtime_result(self) -> Result<Value, RuntimeError> {
        Ok(self.into_value())
    }
}

impl<R> FunctionOutput for Result<R, RuntimeError>
where
    R: FunctionOutput,
{
    fn into_runtime_result(self) -> Result<Value, RuntimeError> {
        match self {
            Ok(value) => value.into_runtime_result(),
            Err(err) => Err(err),
        }
    }
}

impl<R> FunctionOutput for Result<R, ValueError>
where
    R: FunctionOutput,
{
    fn into_runtime_result(self) -> Result<Value, RuntimeError> {
        match self {
            Ok(value) => value.into_runtime_result(),
            Err(err) => Err(RuntimeError::from(err)),
        }
    }
}

impl<T> FunctionOutput for Vec<T>
where
    T: IntoValue,
{
    fn into_runtime_result(self) -> Result<Value, RuntimeError> {
        Ok(Value::List(ListValue::from(self)))
    }
}
