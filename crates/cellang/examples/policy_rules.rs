use cellang::value::{IntoValue, ListValue, MapValue, Value};
use cellang::{Runtime, RuntimeError};
use miette::Result;

fn main() -> Result<()> {
    let mut builder = Runtime::builder();
    builder.set_variable("request", request("deploy", 42, &["engineering"]))?;
    builder.set_variable("resource", service("api", true))?;
    let runtime = builder.build();

    // CEL works well for small authorization and routing rules. Keep the data in
    // Rust, and let users or operators own the expression string.
    let allow_deploy = runtime.eval(
        "request.action in resource.allowed_actions && \
         request.risk_score < 70 && \
         (!resource.sensitive || 'security' in request.groups)",
    )?;
    assert_eq!(allow_deploy, Value::Bool(false));

    let mut security_request = runtime.child_builder();
    security_request.set_variable(
        "request",
        request("deploy", 42, &["engineering", "security"]),
    )?;
    let security_request = security_request.build();

    let allow_security_deploy = security_request.eval(
        "request.action in resource.allowed_actions && \
         request.risk_score < 70 && \
         (!resource.sensitive || 'security' in request.groups)",
    )?;
    assert_eq!(allow_security_deploy, Value::Bool(true));

    let blocked_delete = security_request.eval(
        "request.action == 'delete' ? \
         request.risk_score < 10 : \
         request.action in resource.allowed_actions",
    )?;
    assert_eq!(blocked_delete, Value::Bool(true));

    let mut delete_request = security_request.child_builder();
    delete_request.set_variable(
        "request",
        request("delete", 5, &["engineering", "security"]),
    )?;
    let delete_request = delete_request.build();

    let can_delete = delete_request.eval(
        "request.action == 'delete' ? \
         request.risk_score < 10 : \
         request.action in resource.allowed_actions",
    )?;
    assert_eq!(can_delete, Value::Bool(true));

    let invalid_policy = delete_request
        .eval("request.owner.department")
        .expect_err("missing nested fields should fail");
    assert_missing_field(invalid_policy, "owner");

    Ok(())
}

fn request(action: &str, risk_score: i64, groups: &[&str]) -> Value {
    let mut request = MapValue::new();
    request.insert("action", action);
    request.insert("risk_score", risk_score);
    request.insert(
        "groups",
        ListValue::from(groups.iter().copied().collect::<Vec<_>>()),
    );
    Value::Map(request)
}

fn service(name: &str, sensitive: bool) -> Value {
    let mut resource = MapValue::new();
    resource.insert("name", name);
    resource.insert("sensitive", sensitive);
    resource.insert(
        "allowed_actions",
        vec!["read", "deploy", "restart"].into_value(),
    );
    Value::Map(resource)
}

fn assert_missing_field(err: RuntimeError, field: &str) {
    assert!(
        err.to_string().contains(field),
        "expected missing field '{field}' in error, got {err}",
    );
}
