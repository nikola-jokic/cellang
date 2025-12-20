use cellang::{ListValue, MapValue, Runtime, RuntimeError, Value};
use miette::Result;

fn main() -> Result<()> {
    let mut builder = Runtime::builder();
    builder.set_variable("users", load_users());
    builder.register_function("has_role", has_role)?;

    builder.set_variable("role", "admin");
    let runtime = builder.build();
    let is_admin = runtime.eval("users[0].has_role(role)")?;
    assert_eq!(is_admin, Value::Bool(true));

    let mut scoped = runtime.child_builder();
    scoped.set_variable("role", "user");
    let scoped = scoped.build();
    let is_user = scoped.eval("users[1].has_role(role)")?;
    assert_eq!(is_user, Value::Bool(true));

    Ok(())
}

fn load_users() -> Value {
    let records = vec![
        build_user("Alice", &["admin"]),
        build_user("Bob", &["user"]),
        build_user("Charlie", &["admin", "user"]),
        build_user("David", &["user"]),
    ];
    Value::List(ListValue::from(records))
}

fn build_user(name: &str, roles: &[&str]) -> Value {
    let mut record = MapValue::new();
    record.insert("name", name);
    record.insert("roles", ListValue::from(roles.to_vec()));
    Value::Map(record)
}

fn has_role(user: MapValue, role: String) -> Result<bool, RuntimeError> {
    let roles = user
        .get_str("roles")
        .ok_or_else(|| RuntimeError::new("user.roles is missing"))?;
    let Value::List(list) = roles else {
        return Err(RuntimeError::new("user.roles must be a list"));
    };
    Ok(list
        .iter()
        .any(|value| matches!(value, Value::String(current) if current == &role)))
}
