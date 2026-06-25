use cellang::types::{FunctionDecl, OverloadDecl, Type};
use cellang::{ListValue, Runtime, RuntimeError, Value};
use miette::Result;

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
    builder.add_function_decl(split_decl())?;
    builder.register_function("split", split)?;
    let runtime = builder.build();

    let expected = Value::List(ListValue::from(vec!["a", "b", "c"]));
    let value = runtime.eval("'a,b,c'.split(',')")?;
    assert_eq!(value, expected);

    let as_function = runtime.eval("split('red|green|blue', '|')")?;
    assert_eq!(
        as_function,
        Value::List(ListValue::from(vec!["red", "green", "blue"])),
    );

    let middle = runtime.eval("'red|green|blue'.split('|')[1]")?;
    assert_eq!(middle, Value::String("green".to_string()));

    let segment_count = runtime.eval("size('red|green|blue'.split('|'))")?;
    assert_eq!(segment_count, Value::Int(3));

    let mut scoped = runtime.child_builder();
    scoped.set_variable("x", "a,b,c")?;
    let scoped = scoped.build();
    let via_variable = scoped.eval("x.split(',')")?;
    assert_eq!(via_variable, expected);

    let err = scoped.eval("x.split('::')").expect_err("invalid delimiter");
    assert!(
        err.to_string().contains("single-character delimiter"),
        "unexpected error: {err}",
    );

    Ok(())
}

fn split_decl() -> FunctionDecl {
    let mut decl = FunctionDecl::new("split");
    let list_string = Type::list(Type::String);
    decl.add_overload(OverloadDecl::new(
        "string_split_function",
        vec![Type::String, Type::String],
        list_string.clone(),
    ))
    .expect("split function overload");
    decl.add_overload(
        OverloadDecl::new(
            "string_split_method",
            vec![Type::String],
            list_string,
        )
        .with_receiver(Type::String),
    )
    .expect("split method overload");
    decl
}
