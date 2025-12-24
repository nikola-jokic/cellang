use cellang::{CallContext, ListValue, Runtime, RuntimeError, Value};
use miette::Result;
use std::sync::Arc;

fn split(
    input: String,
    delimiter: String,
) -> Result<Vec<String>, RuntimeError> {
    if delimiter.chars().count() != 1 {
        return Err(RuntimeError::new(
            "split expects a single-character delimiter",
        ));
    }
    let needle = delimiter
        .chars()
        .next()
        .expect("delimiter has exactly one char");
    let parts = input
        .split(needle)
        .map(|segment| segment.to_string())
        .collect::<Vec<_>>();
    Ok(parts)
}

fn main() -> Result<()> {
    let mut builder = Runtime::builder();
    builder.register_function("split", split)?;
    builder.set_variable("feature_enabled", true);
    builder.register_native_function(
        "featureEnabled",
        Arc::new(|ctx: &CallContext<'_>| {
            // Access the runtime to read shared state when evaluating the function.
            Ok(ctx
                .runtime()
                .get_variable("feature_enabled")
                .cloned()
                .unwrap_or(Value::Bool(false)))
        }),
    )?;
    let runtime = builder.build();

    let expected = Value::List(ListValue::from(vec!["a", "b", "c"]));
    let value = runtime.eval("'a,b,c'.split(',')")?;
    assert_eq!(value, expected);

    let feature = runtime.eval("featureEnabled()")?;
    assert_eq!(feature, Value::Bool(true));

    let mut scoped = runtime.child_builder();
    scoped.set_variable("x", "a,b,c");
    let scoped = scoped.build();
    let via_variable = scoped.eval("x.split(',')")?;
    assert_eq!(via_variable, expected);

    Ok(())
}
