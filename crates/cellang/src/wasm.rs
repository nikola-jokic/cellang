use crate::error::RuntimeError;
use crate::runtime::{Runtime, RuntimeBuilder};
use crate::value::{ListValue, MapValue, Value};
use serde_json::Value as JsonValue;
use serde_wasm_bindgen::{
    from_value as from_js_value, to_value as to_js_value,
};
use wasm_bindgen::prelude::*;

/// Evaluates a CEL expression using a fresh runtime instantiated from the
/// provided JSON variables.
#[wasm_bindgen(js_name = "evaluateExpression")]
pub fn evaluate_expression(
    source: &str,
    env: JsValue,
) -> Result<JsValue, JsValue> {
    let runtime = build_runtime(env)?;
    eval_with_runtime(&runtime, source)
}

/// Re-usable runtime that can be shared across wasm callers.
#[wasm_bindgen]
pub struct WasmRuntime {
    inner: Runtime,
}

#[wasm_bindgen]
impl WasmRuntime {
    #[wasm_bindgen(constructor)]
    pub fn new(env: JsValue) -> Result<WasmRuntime, JsValue> {
        build_runtime(env).map(|runtime| WasmRuntime { inner: runtime })
    }

    /// Evaluates the provided CEL `source` against the stored runtime.
    #[wasm_bindgen(js_name = "evaluate")]
    pub fn evaluate(&self, source: &str) -> Result<JsValue, JsValue> {
        eval_with_runtime(&self.inner, source)
    }

    /// Returns a child runtime with additional variables merged in.
    #[wasm_bindgen(js_name = "withVariables")]
    pub fn with_variables(&self, env: JsValue) -> Result<WasmRuntime, JsValue> {
        let mut builder = self.inner.child_builder();
        if let Some(json) = decode_env(env)? {
            inject_variables(&mut builder, json).map_err(to_js_error)?;
        }
        Ok(WasmRuntime {
            inner: builder.build(),
        })
    }
}

fn build_runtime(env: JsValue) -> Result<Runtime, JsValue> {
    let mut builder = Runtime::builder();
    if let Some(json) = decode_env(env)? {
        inject_variables(&mut builder, json).map_err(to_js_error)?;
    }
    Ok(builder.build())
}

fn eval_with_runtime(
    runtime: &Runtime,
    source: &str,
) -> Result<JsValue, JsValue> {
    let value = runtime
        .eval(source)
        .map_err(|err| JsValue::from(err.to_string()))?;
    to_js_value(&value).map_err(|err| JsValue::from(err.to_string()))
}

fn decode_env(env: JsValue) -> Result<Option<JsonValue>, JsValue> {
    if env.is_undefined() || env.is_null() {
        return Ok(None);
    }
    from_js_value(env)
        .map(Some)
        .map_err(|err| JsValue::from(err.to_string()))
}

fn inject_variables(
    builder: &mut RuntimeBuilder,
    env: JsonValue,
) -> Result<(), RuntimeError> {
    match env {
        JsonValue::Null => Ok(()),
        JsonValue::Object(map) => {
            for (key, value) in map {
                builder.set_variable(key, json_to_value(value))?;
            }
            Ok(())
        }
        _ => Err(RuntimeError::new(
            "Environment must be a JSON object when targeting wasm",
        )),
    }
}

fn json_to_value(value: JsonValue) -> Value {
    match value {
        JsonValue::Null => Value::Null,
        JsonValue::Bool(flag) => Value::Bool(flag),
        JsonValue::Number(number) => number
            .as_i64()
            .map(Value::Int)
            .or_else(|| number.as_u64().map(Value::Uint))
            .or_else(|| number.as_f64().map(Value::Double))
            .unwrap_or(Value::Null),
        JsonValue::String(text) => Value::String(text),
        JsonValue::Array(items) => {
            let converted =
                items.into_iter().map(json_to_value).collect::<Vec<_>>();
            Value::List(ListValue::from(converted))
        }
        JsonValue::Object(map) => {
            let mut cel_map = MapValue::new();
            for (key, value) in map {
                cel_map.insert(key, json_to_value(value));
            }
            Value::Map(cel_map)
        }
    }
}

fn to_js_error<E: ToString>(err: E) -> JsValue {
    JsValue::from(err.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use wasm_bindgen::JsValue;
    use wasm_bindgen_test::wasm_bindgen_test;

    fn js_env(value: serde_json::Value) -> JsValue {
        serde_wasm_bindgen::to_value(&value)
            .expect("env serialization succeeds")
    }

    fn to_json(value: JsValue) -> serde_json::Value {
        serde_wasm_bindgen::from_value(value)
            .expect("js value converts to json")
    }

    #[wasm_bindgen_test]
    fn evaluates_expression_with_env() {
        let env = js_env(json!({
            "user": { "age": 34 }
        }));

        let result = evaluate_expression("user.age + 1", env)
            .expect("evaluation succeeds");
        assert_eq!(to_json(result), json!(35));
    }

    #[wasm_bindgen_test]
    fn child_runtime_merges_variables() {
        let runtime = WasmRuntime::new(js_env(json!({ "base": 10 })))
            .expect("runtime builds");
        let child = runtime
            .with_variables(js_env(json!({ "offset": 5 })))
            .expect("child runtime builds");

        let result = child
            .evaluate("base + offset")
            .expect("evaluation succeeds");
        assert_eq!(to_json(result), json!(15));
    }

    #[wasm_bindgen_test]
    fn rejects_non_object_environment() {
        let err = WasmRuntime::new(js_env(json!(5)))
            .expect_err("non-object env fails");
        let message = err.as_string().expect("error is string");
        assert!(message.contains("Environment must be a JSON object"));
    }
}
