//! Regression tests for canonical parser facade behavior.
//!
//! This test suite validates:
//! 1. Canonical parser facade functions compile and execute
//! 2. Parse/lower/eval behavior remains stable
//! 3. Edge case regression coverage (precedence, ternary, chaining, errors)

use cellang::Runtime;

// ============================================================================
// SECTION 1: Canonical Import Tests
// ============================================================================

#[test]
fn canonical_parse_compiles() {
    use cellang::parser::parse;

    let result = parse("1 + 2");
    assert!(result.is_ok(), "canonical parse failed: {:?}", result.err());
}

#[test]
fn canonical_lower_compiles() {
    use cellang::parser::{lower, parse};

    let cst = parse("1 + 2").expect("parse failed");
    let result = lower(cst);
    assert!(result.is_ok(), "canonical lower failed: {:?}", result.err());
}

#[test]
fn canonical_lower_source_compiles() {
    use cellang::parser::lower_source;

    let result = lower_source("1 + 2");
    assert!(
        result.is_ok(),
        "canonical lower_source failed: {:?}",
        result.err()
    );
}

#[test]
fn canonical_type_check_compiles() {
    use cellang::parser::{lower_source, type_check};

    let runtime = Runtime::builder().build();
    let hir = lower_source("1 + 2").expect("lower_source failed");
    let result = type_check(runtime.env(), &hir);
    assert!(
        result.is_ok(),
        "canonical type_check failed: {:?}",
        result.err()
    );
}

#[test]
fn canonical_eval_compiles() {
    use cellang::parser::eval;

    let runtime = Runtime::builder().build();
    let result = eval(&runtime, "1 + 2");
    assert!(result.is_ok(), "canonical eval failed: {:?}", result.err());
}

#[test]
fn canonical_eval_ast_compiles() {
    use cellang::parser::{eval_ast, lower_source};

    let runtime = Runtime::builder().build();
    let hir = lower_source("1 + 2").expect("lower_source failed");
    let result = eval_ast(&runtime, &hir);
    assert!(
        result.is_ok(),
        "canonical eval_ast failed: {:?}",
        result.err()
    );
}

// ============================================================================
// SECTION 2: Functional Behavior Tests
// ============================================================================

#[test]
fn parse_lower_eval_parity_simple() {
    use cellang::parser::eval;
    use cellang::Value;

    let runtime = Runtime::builder().build();

    let result = eval(&runtime, "1 + 2").expect("eval failed");
    assert_eq!(result, Value::Int(3));
}

#[test]
fn parse_lower_eval_parity_precedence() {
    use cellang::Value;
    use cellang::parser::eval;

    let runtime = Runtime::builder().build();

    let canonical_result = eval(&runtime, "1 + 2 * 3").expect("eval failed");

    // Verify precedence: 1 + (2 * 3) = 7, not (1 + 2) * 3 = 9
    assert_eq!(
        canonical_result,
        Value::Int(7),
        "precedence violation: expected 7"
    );
}

#[test]
fn parse_lower_eval_parity_ternary() {
    use cellang::Value;
    use cellang::parser::eval;

    let runtime = Runtime::builder().build();

    let canonical_result = eval(&runtime, "true ? 1 : 2").expect("eval failed");

    assert_eq!(
        canonical_result,
        Value::Int(1),
        "ternary: true branch should evaluate"
    );
}

#[test]
fn parse_lower_eval_parity_chaining() {
    use cellang::parser::eval;
    use cellang::{StructValue, Value};

    let mut alice = StructValue::new("User");
    alice.set_field("name", "Alice");

    let mut builder = Runtime::builder();
    builder
        .set_variable("users", vec![alice])
        .expect("set_variable failed");
    let runtime = builder.build();

    let canonical_result = eval(&runtime, "users[0].name").expect("eval failed");

    assert_eq!(
        canonical_result,
        Value::String("Alice".into()),
        "chaining: field after index"
    );
}

// ============================================================================
// SECTION 3: Regression Edge Cases
// ============================================================================

#[test]
fn regression_precedence_structure() {
    use cellang::parser::{Atom, BinaryOp, Expr, lower_source};

    let hir = lower_source("1 + 2 * 3").expect("lower_source failed");

    // Verify AST structure: Plus(1, Multiply(2, 3))
    let Expr::Binary {
        op: BinaryOp::Add,
        lhs,
        rhs,
    } = hir
    else {
        panic!("Expected Add operator at root, got {:?}", hir);
    };

    assert!(matches!(*lhs, Expr::Atom(Atom::Int(1))));

    let Expr::Binary {
        op: BinaryOp::Mul,
        lhs: mul_lhs,
        rhs: mul_rhs,
    } = *rhs
    else {
        panic!("Expected Multiply as rhs of Add");
    };

    assert!(matches!(*mul_lhs, Expr::Atom(Atom::Int(2))));
    assert!(matches!(*mul_rhs, Expr::Atom(Atom::Int(3))));
}

#[test]
fn regression_ternary_nested() {
    use cellang::Value;
    use cellang::parser::eval;

    let runtime = Runtime::builder().build();

    // Test nested ternary: true ? 1 : false ? 2 : 3
    let result =
        eval(&runtime, "true ? 1 : false ? 2 : 3").expect("eval failed");
    assert_eq!(
        result,
        Value::Int(1),
        "nested ternary: first branch should evaluate"
    );

    let result =
        eval(&runtime, "false ? 1 : true ? 2 : 3").expect("eval failed");
    assert_eq!(
        result,
        Value::Int(2),
        "nested ternary: second branch should evaluate"
    );

    let result =
        eval(&runtime, "false ? 1 : false ? 2 : 3").expect("eval failed");
    assert_eq!(
        result,
        Value::Int(3),
        "nested ternary: third branch should evaluate"
    );
}

#[test]
fn regression_chaining_field_index_call() {
    use cellang::parser::eval;
    use cellang::types::{FunctionDecl, OverloadDecl, Type};
    use cellang::{ListValue, StructValue, Value};

    let mut alice = StructValue::new("User");
    alice.set_field("name", "Alice");
    alice.set_field("roles", ListValue::from(vec!["admin", "user"]));

    let mut bob = StructValue::new("User");
    bob.set_field("name", "Bob");
    bob.set_field("roles", ListValue::from(vec!["user"]));

    let mut upper_decl = FunctionDecl::new("upper");
    upper_decl
        .add_overload(OverloadDecl::new(
            "upper_string",
            vec![Type::String],
            Type::String,
        ))
        .expect("add overload failed");

    let mut builder = Runtime::builder();
    builder
        .add_function_decl(upper_decl)
        .expect("add_function_decl failed");
    builder
        .register_function("upper", |s: String| s.to_uppercase())
        .expect("register_function failed");
    builder
        .set_variable("users", vec![alice, bob])
        .expect("set_variable failed");
    let runtime = builder.build();

    let result = eval(&runtime, "users[0].name").expect("eval failed");
    assert_eq!(result, Value::String("Alice".into()));

    let result = eval(&runtime, "users[0].roles[0]").expect("eval failed");
    assert_eq!(result, Value::String("admin".into()));

    let result = eval(&runtime, "upper(users[0].name)").expect("eval failed");
    assert_eq!(result, Value::String("ALICE".into()));
}

#[test]
fn regression_malformed_error_handling() {
    use cellang::parser::parse;

    // Unclosed delimiter
    let result = parse("foo(");
    assert!(result.is_err(), "expected error for unclosed delimiter");

    // Unexpected operator
    let result = parse("1 + * 2");
    assert!(result.is_err(), "expected error for unexpected operator");

    // Invalid character
    let result = parse("&");
    assert!(result.is_err(), "expected error for invalid character");
}

#[test]
fn regression_malformed_eval_errors() {
    use cellang::parser::eval;

    let runtime = Runtime::builder().build();

    // Undefined variable
    let result = eval(&runtime, "undefined_var");
    assert!(result.is_err(), "expected error for undefined variable");

    // Type mismatch
    let result = eval(&runtime, "1 + \"string\"");
    assert!(result.is_err(), "expected error for type mismatch");
}

// ============================================================================
// SECTION 4: Pipeline Equivalence (parse → lower → type_check → eval)
// ============================================================================

#[test]
fn pipeline_equivalence_full() {
    use cellang::parser::{eval_ast, lower, parse};

    let runtime = Runtime::builder().build();
    let input = "1 + 2 * 3";

    let cst = parse(input).expect("parse failed");
    let hir = lower(cst).expect("lower failed");
    let result = eval_ast(&runtime, &hir).expect("eval_ast failed");

    use cellang::parser::eval;
    let shortcut_result = eval(&runtime, input).expect("eval shortcut failed");

    assert_eq!(
        result, shortcut_result,
        "full pipeline diverged from eval shortcut"
    );
}
