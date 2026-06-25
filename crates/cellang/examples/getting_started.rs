use cellang::types::{FunctionDecl, OverloadDecl, Type};
use cellang::{Runtime, Value};
use miette::Result;

fn main() -> Result<()> {
    // Start with a builder, add the data CEL expressions can see, then build an
    // immutable runtime that can be reused for many evaluations.
    let mut builder = Runtime::builder();
    builder.set_variable("first_name", "Ada")?;
    builder.set_variable("last_name", "Lovelace")?;
    builder.set_variable("roles", vec!["admin", "analyst"])?;
    builder.set_variable("quota_used", 41_i64)?;
    builder.set_variable("quota_limit", 100_i64)?;

    // Native functions need a CEL declaration before they can be registered.
    // This gives the type checker enough information to validate calls.
    builder.add_function_decl(full_name_decl())?;
    builder.register_function("full_name", full_name)?;

    let runtime = builder.build();

    let display_name = runtime.eval("full_name(first_name, last_name)")?;
    assert_eq!(display_name, Value::String("Ada Lovelace".to_string()));

    let can_admin = runtime.eval(
        "'admin' in roles && quota_used < quota_limit && \
         full_name(first_name, last_name).startsWith('Ada')",
    )?;
    assert_eq!(can_admin, Value::Bool(true));

    // Child runtimes inherit the environment and values, then override only the
    // variables that are different for this request.
    let mut scoped = runtime.child_builder();
    scoped.set_variable("quota_used", 100_i64)?;
    let scoped = scoped.build();

    let exhausted = scoped.eval("quota_used >= quota_limit")?;
    assert_eq!(exhausted, Value::Bool(true));

    // Type and syntax errors are returned as normal Results.
    let err = scoped
        .eval("missing_variable == true")
        .expect_err("unknown identifiers should fail");
    assert!(
        err.to_string().contains("missing_variable"),
        "unexpected error: {err}",
    );

    Ok(())
}

fn full_name(first: String, last: String) -> String {
    format!("{first} {last}")
}

fn full_name_decl() -> FunctionDecl {
    let mut decl = FunctionDecl::new("full_name")
        .with_doc("Combines first and last name for display");
    decl.add_overload(OverloadDecl::new(
        "full_name_string_string",
        vec![Type::String, Type::String],
        Type::String,
    ))
    .expect("full_name overload");
    decl
}
