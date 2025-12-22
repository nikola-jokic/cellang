use crate::builtins;
use crate::env::{Env, EnvBuilder};
use crate::error::{EnvError, RuntimeError};
use crate::types::{FunctionDecl, IdentDecl, NamedType};
use crate::value::{IntoValue, ListValue, TryFromValue, Value, ValueError};
use std::collections::BTreeMap;
use std::sync::Arc;

pub type NativeFunction = Arc<
    dyn Fn(&CallContext<'_>) -> Result<Value, RuntimeError>
        + Send
        + Sync
        + 'static,
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

#[derive(Clone)]
pub struct RuntimeBuilder {
    env_builder: EnvBuilder,
    variables: BTreeMap<String, Value>,
    functions: BTreeMap<String, NativeFunction>,
}

impl Default for RuntimeBuilder {
    fn default() -> Self {
        let mut builder = RuntimeBuilder {
            env_builder: EnvBuilder::default(),
            variables: BTreeMap::new(),
            functions: BTreeMap::new(),
        };
        builder
            .install_standard_library()
            .expect("core functions must register");
        builder
    }
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

    pub fn add_ident(
        &mut self,
        ident: IdentDecl,
    ) -> Result<&mut Self, EnvError> {
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

    pub fn set_variable<V>(
        &mut self,
        name: impl Into<String>,
        value: V,
    ) -> &mut Self
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

    fn install_standard_library(&mut self) -> Result<(), RuntimeError> {
        builtins::register(self)
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
                return Err(RuntimeError::wrong_arity(
                    &fname,
                    0,
                    ctx.args.len(),
                ));
            }
            let result = self();
            result.into_runtime_result()
        })
    }
}

macro_rules! impl_into_native_function {
    ($(($param:ident, $var:ident)),+ $(,)?) => {
        impl<F, R, $($param),+> IntoNativeFunction<($($param,)+), R> for F
        where
            F: Fn($($param),+) -> R + Send + Sync + 'static,
            R: FunctionOutput,
            $($param: TryFromValue,)+
        {
            fn into_native(self, name: String) -> NativeFunction {
                let fname = name.clone();
                Arc::new(move |ctx| {
                    const EXPECTED: usize = impl_into_native_function!(@count $(($param, $var)),+);
                    if ctx.args.len() != EXPECTED {
                        return Err(RuntimeError::wrong_arity(&fname, EXPECTED, ctx.args.len()));
                    }
                    impl_into_native_function!(@convert ctx, fname, self, [$(($param, $var)),+])
                })
            }
        }
    };

    (@count $(($param:ident, $var:ident)),+) => {
        impl_into_native_function!(@count_helper $($param),+)
    };
    (@count_helper $head:ident $(,$tail:ident)*) => {
        1usize + impl_into_native_function!(@count_helper $($tail),*)
    };
    (@count_helper) => {0usize};

    (@convert $ctx:ident, $fname:ident, $func:ident, [$(($param:ident, $var:ident)),+]) => {{
        let mut iter = $ctx.args.iter().enumerate();
        $(
            let $var = {
                let (idx, value) = iter.next().expect("arity validated");
                $param::try_from_value(value)
                    .map_err(|err| RuntimeError::argument(&$fname, idx, err))?
            };
        )+
        let result = $func($($var),+);
        result.into_runtime_result()
    }};
}

impl_into_native_function!((A0, arg0));
impl_into_native_function!((A0, arg0), (A1, arg1));
impl_into_native_function!((A0, arg0), (A1, arg1), (A2, arg2));
impl_into_native_function!((A0, arg0), (A1, arg1), (A2, arg2), (A3, arg3));
impl_into_native_function!(
    (A0, arg0),
    (A1, arg1),
    (A2, arg2),
    (A3, arg3),
    (A4, arg4)
);
impl_into_native_function!(
    (A0, arg0),
    (A1, arg1),
    (A2, arg2),
    (A3, arg3),
    (A4, arg4),
    (A5, arg5)
);

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_builtin_is_available() {
        let runtime = Runtime::builder().build();
        let value = runtime.eval("size([1, 2, 3])").expect("size to work");
        assert_eq!(value, Value::Int(3));
    }

    #[test]
    fn starts_with_builtin_supports_methods() {
        let runtime = Runtime::builder().build();
        let positive = runtime
            .eval("'foobar'.startsWith('foo')")
            .expect("startsWith to work");
        assert_eq!(positive, Value::Bool(true));

        let negative = runtime
            .eval("'foobar'.startsWith('bar')")
            .expect("startsWith to work");
        assert_eq!(negative, Value::Bool(false));
    }
}
