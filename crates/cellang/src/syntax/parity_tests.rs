//! Parser fixture harness for the Rowan + HIR pipeline.

use crate::hir::{self, Atom, BinaryOp, Expr};
use crate::syntax::parser;

/// Golden fixtures: expressions that must parse successfully
const SUCCESS_FIXTURES: &[(&str, &str)] = &[
    // Precedence: multiplication before addition
    ("1 + 2 * 3", "precedence_mul_add"),
    // Associativity: left-associative subtraction
    ("a - b - c", "associativity_left_sub"),
    ("a / b / c", "associativity_left_div"),
    // Unary precedence
    ("-5", "unary_minus"),
    ("!x", "unary_not"),
    ("-a * b", "unary_minus_mul"),
    // Function calls
    ("foo(a, b)", "call_basic"),
    ("foo()", "call_empty"),
    ("foo([])", "call_empty_list"),
    ("foo({})", "call_empty_map"),
    // Method calls and chaining
    ("a.b(c)", "method_call"),
    ("a.b(c).d", "method_field_chain"),
    ("foo.bar().baz()", "method_chain"),
    ("foo.bar().baz().qux()", "long_method_chain"),
    ("foo.all(test, test.size() > 4)", "nested_method_call"),
    // Field access
    ("a.b.c", "field_chain"),
    ("foo.bar.baz", "field_chain_3"),
    // Indexing
    ("list[0]", "index_basic"),
    ("map[\"key\"]", "index_string_key"),
    ("a[b][c]", "index_chain"),
    ("foo[1][2]", "index_chain_numeric"),
    // Mixed field access and indexing
    ("foo.check[0].baz", "field_index_field"),
    (
        "foo.bar.filter(x, x > 10)[0].id",
        "nested_method_index_field",
    ),
    ("foo.bar(x, t[x] > 10)", "method_with_index_arg"),
    // Ternary
    ("a ? b : c", "ternary_basic"),
    ("x ? y ? z : w : v", "ternary_nested"),
    ("true ? 1 : false ? 2 : 3", "ternary_nested_else"),
    // Lists
    ("[1, 2, 3]", "list_basic"),
    ("[]", "list_empty"),
    ("[{foo: 1}, {bar: 2}]", "list_nested_maps"),
    // Maps
    ("{\"key\": value}", "map_string_key"),
    ("{foo: 1, bar: 2}", "map_ident_keys"),
    ("{}", "map_empty"),
    // Logical operators
    ("a && b || c", "logical_precedence"),
    ("1 < 2 && 3 >= 4 || 5 == 6 && 5 in 6", "relations_complex"),
    // Grouping
    ("(1 + 2) * 3 % 4", "grouping_precedence"),
    // Macros: has
    ("has(x.y)", "macro_has_field"),
    // Macros: comprehensions
    ("all(items, i, i > 0)", "macro_all"),
    ("exists(items, i, i == target)", "macro_exists"),
    ("exists_one(items, i, i > 0)", "macro_exists_one"),
    ("map(items, i, i * 2)", "macro_map_transform"),
    ("map(items, i, i > 0, i * 2)", "macro_map_filter_transform"),
    ("filter(items, i, i > 0)", "macro_filter"),
    // Additional atoms
    ("identifier", "atom_ident"),
    ("123", "atom_int"),
    ("123u", "atom_uint"),
    ("123.456", "atom_double"),
    ("true", "atom_true"),
    ("false", "atom_false"),
    ("\"string\"", "atom_string"),
    ("null", "atom_null"),
    // Inline function call in expression
    ("1 + size(2u)", "inline_function_call"),
    ("1 + dyn(2u)", "inline_dyn_call"),
    // Method with relation
    ("foo.bar() < 4", "method_relation"),
];

/// Failure fixtures: malformed expressions that must produce deterministic errors
const FAILURE_FIXTURES: &[(&str, &str, &str)] = &[
    // Unclosed delimiters (EOF inside expression context)
    ("foo(", "eof_unclosed_call", "continuing argument list"),
    ("[1, 2", "eof_unclosed_list", "continuing list"),
    ("{k: v", "eof_unclosed_map", "continuing map"),
    ("(1 + 2", "eof_unclosed_paren", "closing parenthesis"),
    // Unexpected tokens
    ("1 + * 2", "unexpected_operator", "Unexpected token"),
    // Invalid characters (lexer errors)
    ("&", "lexer_invalid_char", "Unexpected character"),
    // Macro validation errors (semantic-level but caught during parse)
    // Note: These may pass parsing but fail during macro detection
    // Including them here for completeness once macro integration is added to harness
];

/// Parse via the active pipeline: Rowan CST parse + HIR lowering.
fn parse_with_old(input: &str) -> Result<Expr, String> {
    let parsed = parser::parse(input).map_err(|err| err.message)?;
    hir::lower(parsed).map_err(|err| err.message)
}

/// Assert a fixture lowers successfully through the active pipeline.
fn assert_parity(input: &str, description: &str) {
    let old_result = parse_with_old(input);

    assert!(
        old_result.is_ok(),
        "Pipeline failed on fixture '{}' ({}): {:?}",
        description,
        input,
        old_result.unwrap_err()
    );
}

/// Assert that a fixture produces an expected error
fn assert_failure(
    input: &str,
    description: &str,
    expected_message_fragment: &str,
) {
    let old_result = parse_with_old(input);

    assert!(
        old_result.is_err(),
        "Pipeline succeeded on failure fixture '{}' ({}), expected error",
        description,
        input
    );

    let message = old_result.expect_err("checked is_err");
    assert!(
        message.contains(expected_message_fragment),
        "Error message mismatch for fixture '{}' ({})\nExpected fragment: '{}'\nActual message: '{}'",
        description,
        input,
        expected_message_fragment,
        message
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_success_fixtures() {
        for (input, description) in SUCCESS_FIXTURES {
            assert_parity(input, description);
        }
    }

    #[test]
    fn test_failure_fixtures() {
        for (input, description, expected_fragment) in FAILURE_FIXTURES {
            assert_failure(input, description, expected_fragment);
        }
    }

    #[test]
    fn test_precedence_structure() {
        // Validate that 1 + 2 * 3 parses as Plus(1, Multiply(2, 3))
        let tree = parse_with_old("1 + 2 * 3").expect("should parse");

        let Expr::Binary {
            op: BinaryOp::Add,
            lhs,
            rhs,
        } = tree
        else {
            panic!("Expected Add operator at root, got {:?}", tree);
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
    fn test_field_chain_structure() {
        // Validate that a.b.c parses as Field(Field(a, b), c)
        let tree = parse_with_old("a.b.c").expect("should parse");

        let Expr::Field {
            target: outer_target,
            field: outer_field,
        } = tree
        else {
            panic!("Expected Field node at root, got {:?}", tree);
        };

        let Expr::Field {
            target: inner_target,
            field: inner_field,
        } = *outer_target
        else {
            panic!("Expected nested Field node");
        };

        assert!(
            matches!(*inner_target, Expr::Atom(Atom::Ident(ref ident)) if ident == "a")
        );
        assert_eq!(inner_field, "b");
        assert_eq!(outer_field, "c");
    }

    #[test]
    fn test_method_call_structure() {
        // Validate that foo.bar(baz) parses as Call with is_method=true
        let tree = parse_with_old("foo.bar(baz)").expect("should parse");

        let Expr::Call {
            func,
            args,
            is_method,
        } = tree
        else {
            panic!("Expected Call node, got {:?}", tree);
        };

        assert!(is_method, "Expected method call");
        assert!(
            matches!(*func, Expr::Atom(Atom::Ident(ref ident)) if ident == "bar")
        );
        assert_eq!(args.len(), 2); // receiver + argument
        assert!(
            matches!(args[0], Expr::Atom(Atom::Ident(ref ident)) if ident == "foo")
        );
        assert!(
            matches!(args[1], Expr::Atom(Atom::Ident(ref ident)) if ident == "baz")
        );
    }

    #[test]
    fn test_ternary_structure() {
        // Validate that a ? b : c parses as IfTernary with 3 children
        let tree = parse_with_old("a ? b : c").expect("should parse");

        let Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } = tree
        else {
            panic!("Expected Ternary node, got {:?}", tree);
        };

        assert!(
            matches!(*cond, Expr::Atom(Atom::Ident(ref ident)) if ident == "a")
        );
        assert!(
            matches!(*then_expr, Expr::Atom(Atom::Ident(ref ident)) if ident == "b")
        );
        assert!(
            matches!(*else_expr, Expr::Atom(Atom::Ident(ref ident)) if ident == "c")
        );
    }

    #[test]
    fn test_list_structure() {
        let tree = parse_with_old("[1, 2, 3]").expect("should parse");

        let Expr::List(items) = tree else {
            panic!("Expected List node, got {:?}", tree);
        };

        assert_eq!(items.len(), 3);
        assert!(matches!(items[0], Expr::Atom(Atom::Int(1))));
        assert!(matches!(items[1], Expr::Atom(Atom::Int(2))));
        assert!(matches!(items[2], Expr::Atom(Atom::Int(3))));
    }

    #[test]
    fn test_map_structure() {
        let tree = parse_with_old("{foo: 1, bar: 2}").expect("should parse");

        let Expr::Map(entries) = tree else {
            panic!("Expected Map node, got {:?}", tree);
        };

        assert_eq!(entries.len(), 2);
        assert!(
            matches!(entries[0].0, Expr::Atom(Atom::Ident(ref ident)) if ident == "foo")
        );
        assert!(matches!(entries[0].1, Expr::Atom(Atom::Int(1))));
        assert!(
            matches!(entries[1].0, Expr::Atom(Atom::Ident(ref ident)) if ident == "bar")
        );
        assert!(matches!(entries[1].1, Expr::Atom(Atom::Int(2))));
    }

    #[test]
    fn test_index_structure() {
        let tree = parse_with_old("foo[1]").expect("should parse");

        let Expr::Index { target, index } = tree else {
            panic!("Expected Index node, got {:?}", tree);
        };

        assert!(
            matches!(*target, Expr::Atom(Atom::Ident(ref ident)) if ident == "foo")
        );
        assert!(matches!(*index, Expr::Atom(Atom::Int(1))));
    }

    #[test]
    fn test_lexer_error_propagation() {
        let err = parse_with_old("&").expect_err("should fail");
        assert!(err.contains("Unexpected character"));
    }
}
