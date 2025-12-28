use cellang::types::{
    FieldDecl, FunctionDecl, IdentDecl, NamedType, OverloadDecl, StructType,
    Type,
};
use cellang::value::{ListValue, StructValue, Value};
use cellang::{Env, Runtime};
use miette::{IntoDiagnostic, Result};

fn main() -> Result<()> {
    let env_cache =
        serde_json::to_vec(&build_policy_env()).into_diagnostic()?;

    let scenarios =
        [("analytics", "write", true), ("security", "delete", false)];

    for (owner, desired_access, expected) in scenarios {
        let env: Env = serde_json::from_slice(&env_cache).into_diagnostic()?;
        let mut builder = Runtime::builder();
        builder.import_env_owned(env)?;
        builder.register_function("same_tenant", same_tenant)?;
        builder.set_variable("request", request_value())?;
        builder.set_variable("resource_owner", owner)?;
        builder.set_variable("desired_access", desired_access)?;
        let runtime = builder.build();

        let decision = runtime.eval(
            "same_tenant(request.subject, resource_owner) && \
             request.resource.accesses.exists(access, access == desired_access)",
        )?;
        assert_eq!(decision, Value::Bool(expected));
    }

    Ok(())
}

fn build_policy_env() -> Env {
    let mut builder = Env::builder();

    let mut resource = StructType::new("example.Resource")
        .with_doc("Resource being evaluated in a policy");
    resource
        .add_field("kind", FieldDecl::new(Type::String))
        .unwrap();
    resource
        .add_field(
            "accesses",
            FieldDecl::new(Type::list(Type::String))
                .with_doc("Allowed operations on the resource"),
        )
        .unwrap();

    let mut request = StructType::new("example.AccessRequest")
        .with_doc("Wrapper around the incoming access request");
    request
        .add_field("subject", FieldDecl::new(Type::String))
        .unwrap();
    request
        .add_field(
            "resource",
            FieldDecl::new(Type::struct_type(resource.name.clone()))
                .with_doc("Resource being accessed"),
        )
        .unwrap();

    builder.add_type(NamedType::Struct(resource)).unwrap();
    builder
        .add_type(NamedType::Struct(request.clone()))
        .unwrap();

    builder
        .add_ident(
            IdentDecl::new("request", Type::struct_type(request.name.clone()))
                .with_doc("Access request provided at evaluation time"),
        )
        .unwrap();
    builder
        .add_ident(
            IdentDecl::new("resource_owner", Type::String)
                .with_doc("Tenant that owns the resource"),
        )
        .unwrap();
    builder
        .add_ident(
            IdentDecl::new("desired_access", Type::String)
                .with_doc("Operation requested by the caller"),
        )
        .unwrap();

    builder.add_function(same_tenant_decl()).unwrap();

    builder.build()
}

fn same_tenant(requester: String, owner: String) -> bool {
    requester == owner
}

fn same_tenant_decl() -> FunctionDecl {
    let mut decl = FunctionDecl::new("same_tenant")
        .with_doc("Compares two tenant identifiers");
    decl.add_overload(OverloadDecl::new(
        "same_tenant_string_string",
        vec![Type::String, Type::String],
        Type::Bool,
    ))
    .unwrap();
    decl
}

fn request_value() -> Value {
    let mut resource = StructValue::new("example.Resource");
    resource.set_field("kind", "dashboard");
    resource.set_field("accesses", ListValue::from(vec!["read", "write"]));

    let mut request = StructValue::new("example.AccessRequest");
    request.set_field("subject", "analytics");
    request.set_field("resource", resource);

    Value::Struct(request)
}
