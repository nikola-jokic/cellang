use cellang::types::{FieldDecl, IdentDecl, NamedType, StructType, Type};
use cellang::value::{StructValue, Value};
use cellang::{Env, Runtime};
use miette::{IntoDiagnostic, Result};

const INVOICE_TYPE: &str = "example.Invoice";
const APPROVAL_RULE: &str = "invoice.total <= spending_limit && !invoice.paid && invoice.owner == actor";

fn main() -> Result<()> {
    let env = build_env()?;

    // Compile expressions up front when users save a rule. The typed AST can be
    // cached, inspected, serialized, or rejected before any request is evaluated.
    let typed = env.compile(APPROVAL_RULE)?;
    assert_eq!(typed.ty, Type::Bool);

    let serialized = serde_json::to_string(&typed).into_diagnostic()?;
    assert!(serialized.contains("less_equal"));
    assert!(serialized.contains("invoice"));

    let compile_error = env
        .compile("invoice.missing_field == actor")
        .expect_err("unknown struct fields should fail at compile time");
    assert!(
        compile_error.to_string().contains("missing_field"),
        "unexpected compile error: {compile_error}",
    );

    let mut builder = Runtime::builder();
    builder.import_env_owned(env)?;
    builder.set_variable("invoice", invoice("analytics", 125, false))?;
    builder.set_variable("actor", "analytics")?;
    builder.set_variable("spending_limit", 500_i64)?;
    let runtime = builder.build();

    let approved = runtime.eval(APPROVAL_RULE)?;
    assert_eq!(approved, Value::Bool(true));

    let mut scoped = runtime.child_builder();
    scoped.set_variable("spending_limit", 100_i64)?;
    let scoped = scoped.build();
    let blocked_by_limit = scoped.eval(APPROVAL_RULE)?;
    assert_eq!(blocked_by_limit, Value::Bool(false));

    Ok(())
}

fn build_env() -> Result<Env> {
    let mut invoice = StructType::new(INVOICE_TYPE)
        .with_doc("Invoice submitted for spending-policy approval");
    invoice.add_field(
        "owner",
        FieldDecl::new(Type::String).with_doc("Tenant that owns the invoice"),
    )?;
    invoice.add_field(
        "total",
        FieldDecl::new(Type::Int).with_doc("Total amount in whole cents"),
    )?;
    invoice.add_field(
        "paid",
        FieldDecl::new(Type::Bool)
            .with_doc("Whether this invoice was already paid"),
    )?;

    let mut builder = Env::builder();
    builder.add_type(NamedType::Struct(invoice))?;
    builder.add_ident(IdentDecl::new(
        "invoice",
        Type::struct_type(INVOICE_TYPE),
    ))?;
    builder.add_ident(IdentDecl::new("actor", Type::String))?;
    builder.add_ident(IdentDecl::new("spending_limit", Type::Int))?;
    Ok(builder.build())
}

fn invoice(owner: &str, total: i64, paid: bool) -> Value {
    let mut invoice = StructValue::new(INVOICE_TYPE);
    invoice.set_field("owner", owner);
    invoice.set_field("total", total);
    invoice.set_field("paid", paid);
    Value::Struct(invoice)
}
