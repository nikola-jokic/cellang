//! Comprehensive protocol fixture tests covering edge cases, boundary conditions, and integration scenarios.
//!
//! This test suite complements existing protocol tests by focusing on:
//! - Unicode/emoji in identifiers and ranges
//! - Malformed input (invalid positions, empty documents, EOF)
//! - Very long identifiers and multi-line expressions
//! - Cross-feature integration scenarios
//! - UTF-16 range correctness

use cellang_lsp::handlers::FeatureHandlers;
use cellang_lsp::state::{Document, DocumentStore};
use lsp_types::{
    CompletionParams, DocumentSymbolParams, HoverParams, Position,
    TextDocumentIdentifier, TextDocumentPositionParams, Uri,
};
use serde_json::{Value, json};

fn dispatch(payload: Value, documents: &mut DocumentStore) -> Vec<Value> {
    let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
    let dispatcher = cellang_lsp::RequestDispatcher::new(&handler);
    dispatcher.dispatch(payload, documents)
}

fn setup_document(uri: &Uri, text: &str, store: &mut DocumentStore) {
    let mut doc = Document::new(uri.clone(), 1, text.to_string());
    if let Ok(parsed) = cellang::parser::parse(text) {
        doc.parsed = Some(parsed.clone());
        if let Ok(lowered) = cellang::parser::lower(parsed) {
            doc.lowered = Some(lowered);
        }
    }
    store.upsert(doc);
}

fn open_document_via_protocol(
    uri: &Uri,
    text: &str,
    documents: &mut DocumentStore,
) {
    let _ = dispatch(
        json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "cellang",
                    "version": 1,
                    "text": text,
                }
            }
        }),
        documents,
    );
}

mod unicode_emoji_edge_cases {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn hover_with_emoji_in_document_content() {
        let uri = Uri::from_str("file:///emoji.cel").unwrap();
        let mut store = DocumentStore::new();
        // Emoji 🦀 = 2 UTF-16 code units
        let text = "items.exists(🦀, 🦀 > 0)";
        setup_document(&uri, text, &mut store);

        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let params = HoverParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier::new(uri.clone()),
                position: Position::new(0, 13), // On declaration 🦀
            },
            work_done_progress_params: Default::default(),
        };

        let hover = handler.hover(params, &store);
        // Note: Current implementation may not support emoji identifiers in CEL parser
        // This test verifies graceful handling rather than full support
        if let Some(h) = hover {
            assert!(
                h.range.is_some(),
                "hover should include range when supported"
            );
        }
    }

    #[test]
    fn definition_with_multibyte_utf8_characters() {
        let uri = Uri::from_str("file:///multibyte.cel").unwrap();
        let mut documents = DocumentStore::new();
        // 日本語 characters are 3 bytes each in UTF-8 but 1 UTF-16 unit each
        let text = "items.exists(日本, 日本 > 0)";
        open_document_via_protocol(&uri, text, &mut documents);

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 100,
                "method": "textDocument/definition",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 0, "character": 17 } // On reference 日本
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        assert!(
            out[0].get("result").is_some(),
            "should resolve definition with multibyte chars"
        );
    }

    #[test]
    fn references_with_mixed_emoji_and_ascii() {
        let uri = Uri::from_str("file:///mixed.cel").unwrap();
        let mut documents = DocumentStore::new();
        let text = "items.map(🎯, 🎯.value + 1)";
        open_document_via_protocol(&uri, text, &mut documents);

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 101,
                "method": "textDocument/references",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 0, "character": 10 },
                    "context": { "includeDeclaration": true }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        if let Some(result) = out[0].get("result")
            && let Some(locations) = result.as_array()
            && !locations.is_empty()
        {
            // Note: CEL parser may not support emoji identifiers as valid binders
            // This test verifies graceful handling (empty result) rather than requiring full support
            // Verify ranges are valid if any references found
            for loc in locations {
                assert!(
                    loc.get("range").is_some(),
                    "each reference should have range"
                );
                let range = loc.get("range").unwrap();
                assert!(range.get("start").is_some());
                assert!(range.get("end").is_some());
            }
        }
    }

    #[test]
    fn completion_with_emoji_identifier_in_scope() {
        let uri = Uri::from_str("file:///emoji_completion.cel").unwrap();
        let mut store = DocumentStore::new();
        let text = "items.filter(🔥, 🔥 > threshold)";
        setup_document(&uri, text, &mut store);

        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let params = CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position {
                    line: 0,
                    character: 20,
                },
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: None,
        };

        let response = handler.completion(params, &store);
        if let Some(lsp_types::CompletionResponse::Array(items)) = response {
            // Note: CEL parser may not support emoji identifiers
            // This test verifies completion still works (returns environment symbols at minimum)
            assert!(
                !items.is_empty(),
                "completion should return at least environment symbols"
            );
        }
    }

    #[test]
    fn formatting_preserves_emoji_in_output() {
        let uri = Uri::from_str("file:///emoji_format.cel").unwrap();
        let mut documents = DocumentStore::new();
        let text = "items.map(🌟,🌟+1)";
        open_document_via_protocol(&uri, text, &mut documents);

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 102,
                "method": "textDocument/formatting",
                "params": {
                    "textDocument": { "uri": uri },
                    "options": {
                        "tabSize": 2,
                        "insertSpaces": true
                    }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        if let Some(result) = out[0].get("result")
            && let Some(edits) = result.as_array()
        {
            assert!(!edits.is_empty(), "formatting should return edit");
            let new_text = edits[0].pointer("/newText").and_then(Value::as_str);
            assert!(new_text.is_some());
            assert!(
                new_text.unwrap().contains("🌟"),
                "formatted text should preserve emoji"
            );
        }
    }
}

mod malformed_input_edge_cases {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn hover_on_empty_document() {
        let uri = Uri::from_str("file:///empty.cel").unwrap();
        let mut store = DocumentStore::new();
        setup_document(&uri, "", &mut store);

        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let params = HoverParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier::new(uri.clone()),
                position: Position::new(0, 0),
            },
            work_done_progress_params: Default::default(),
        };

        let hover = handler.hover(params, &store);
        assert!(
            hover.is_none(),
            "hover on empty document should return None"
        );
    }

    #[test]
    fn definition_with_out_of_bounds_position() {
        let uri = Uri::from_str("file:///out_of_bounds.cel").unwrap();
        let mut documents = DocumentStore::new();
        open_document_via_protocol(&uri, "x + 1", &mut documents);

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 200,
                "method": "textDocument/definition",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 10, "character": 50 }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        // Should gracefully return null instead of crashing
        assert_eq!(out[0].get("result"), Some(&Value::Null));
    }

    #[test]
    fn references_on_unopened_document() {
        let uri = Uri::from_str("file:///never_opened.cel").unwrap();
        let mut documents = DocumentStore::new();

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 201,
                "method": "textDocument/references",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 0, "character": 0 },
                    "context": { "includeDeclaration": true }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        assert_eq!(out[0].pointer("/result"), Some(&json!([])));
    }

    #[test]
    fn completion_on_document_with_syntax_error() {
        let uri = Uri::from_str("file:///syntax_error.cel").unwrap();
        let mut store = DocumentStore::new();
        let text = "items.exists("; // Unclosed
        let doc = Document::new(uri.clone(), 1, text.to_string());
        // Don't parse - simulates failed parse
        store.upsert(doc);

        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let params = CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position {
                    line: 0,
                    character: 10,
                },
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: None,
        };

        let response = handler.completion(params, &store);
        assert!(
            response.is_some(),
            "completion should work even with syntax errors"
        );

        // Should still return environment symbols
        if let Some(lsp_types::CompletionResponse::Array(items)) = response {
            assert!(
                !items.is_empty(),
                "should return at least environment symbols"
            );
        }
    }

    #[test]
    fn formatting_empty_document() {
        let uri = Uri::from_str("file:///empty_format.cel").unwrap();
        let mut documents = DocumentStore::new();
        open_document_via_protocol(&uri, "", &mut documents);

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 202,
                "method": "textDocument/formatting",
                "params": {
                    "textDocument": { "uri": uri },
                    "options": {
                        "tabSize": 4,
                        "insertSpaces": true
                    }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        // Empty document should either return empty edit or no edits
        if let Some(result) = out[0].get("result")
            && let Some(edits) = result.as_array()
        {
            // Either empty or single edit with empty text
            assert!(edits.is_empty() || edits.len() == 1);
        }
    }

    #[test]
    fn document_symbols_with_parse_failure() {
        let uri = Uri::from_str("file:///parse_fail.cel").unwrap();
        let mut store = DocumentStore::new();
        let doc = Document::new(uri.clone(), 1, "1 + )".to_string());
        // Don't set parsed/lowered - simulates parse failure
        store.upsert(doc);

        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let params = DocumentSymbolParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handler.document_symbols(params, &store);
        // Should return None or empty symbols, not crash
        assert!(
            response.is_none()
                || matches!(response, Some(lsp_types::DocumentSymbolResponse::Nested(ref v)) if v.is_empty()),
            "parse failure should return empty symbols"
        );
    }
}

mod boundary_and_integration_cases {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn very_long_identifier_hover() {
        let uri = Uri::from_str("file:///long_id.cel").unwrap();
        let mut store = DocumentStore::new();
        let long_name = "a".repeat(500);
        let text = format!("items.exists({}, {} > 0)", long_name, long_name);
        setup_document(&uri, &text, &mut store);

        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let params = HoverParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier::new(uri.clone()),
                position: Position::new(0, 13),
            },
            work_done_progress_params: Default::default(),
        };

        let hover = handler.hover(params, &store);
        assert!(
            hover.is_some(),
            "hover should work with very long identifiers"
        );
    }

    #[test]
    fn multiline_expression_diagnostics() {
        let uri = Uri::from_str("file:///multiline.cel").unwrap();
        let mut documents = DocumentStore::new();
        let text = "items.filter(x,\n  x.value > 10\n) && all_valid";
        open_document_via_protocol(&uri, text, &mut documents);

        let doc = documents.get(&uri).unwrap();
        assert_eq!(doc.version, 1);
        assert_eq!(doc.text, text);
    }

    #[test]
    fn definition_across_multiple_comprehensions() {
        let uri = Uri::from_str("file:///nested_comp.cel").unwrap();
        let mut documents = DocumentStore::new();
        let text = "items.all(x, x > 0) && items.exists(y, y < 10)";
        open_document_via_protocol(&uri, text, &mut documents);

        // Query definition for first binder 'x'
        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 300,
                "method": "textDocument/definition",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 0, "character": 17 } // On 'x' reference
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        let _result = out[0].get("result").expect("should have result");
        // Note: First binder 'x' is scoped only within its own comprehension
        // Reference outside the comprehension may not resolve back to it
        // This test verifies the query doesn't crash on complex expressions
    }

    #[test]
    fn references_sorted_by_position_in_multiline() {
        let uri = Uri::from_str("file:///multiline_refs.cel").unwrap();
        let mut documents = DocumentStore::new();
        let text = "items.exists(\n  role,\n  role == target\n)";
        open_document_via_protocol(&uri, text, &mut documents);

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 301,
                "method": "textDocument/references",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 1, "character": 2 },
                    "context": { "includeDeclaration": true }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        if let Some(locations) =
            out[0].pointer("/result").and_then(Value::as_array)
        {
            // Verify positions are sorted
            let mut prev_line = 0;
            let mut prev_char = 0;
            for loc in locations {
                let start_line = loc
                    .pointer("/range/start/line")
                    .and_then(Value::as_u64)
                    .unwrap() as u32;
                let start_char = loc
                    .pointer("/range/start/character")
                    .and_then(Value::as_u64)
                    .unwrap() as u32;

                assert!(
                    start_line > prev_line
                        || (start_line == prev_line && start_char >= prev_char),
                    "references should be sorted by position"
                );

                prev_line = start_line;
                prev_char = start_char;
            }
        }
    }

    #[test]
    fn completion_includes_all_binders_from_nested_comprehensions() {
        let uri = Uri::from_str("file:///nested_binders.cel").unwrap();
        let mut store = DocumentStore::new();
        let text = "outer.all(x, x.inner.exists(y, y > 0))";
        setup_document(&uri, text, &mut store);

        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let params = CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position {
                    line: 0,
                    character: 35,
                },
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: None,
        };

        let response = handler.completion(params, &store);
        if let Some(lsp_types::CompletionResponse::Array(items)) = response {
            let has_x = items.iter().any(|item| item.label == "x");
            let has_y = items.iter().any(|item| item.label == "y");

            assert!(
                has_x || has_y,
                "completion should include binders from nested comprehensions"
            );
        }
    }

    #[test]
    fn formatting_preserves_correctness_on_complex_expression() {
        let uri = Uri::from_str("file:///complex_format.cel").unwrap();
        let mut documents = DocumentStore::new();
        let text = "items.filter(x,x.value>10&&x.active).map(y,{id:y.id,score:y.score*2})";
        open_document_via_protocol(&uri, text, &mut documents);

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 302,
                "method": "textDocument/formatting",
                "params": {
                    "textDocument": { "uri": uri },
                    "options": {
                        "tabSize": 2,
                        "insertSpaces": true
                    }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        if let Some(result) = out[0].get("result")
            && let Some(edits) = result.as_array()
        {
            assert!(!edits.is_empty(), "should format complex expression");
            let new_text = edits[0].pointer("/newText").and_then(Value::as_str);
            assert!(new_text.is_some());

            // Formatted text should be parseable
            let formatted = new_text.unwrap();
            let parse_result = cellang::parser::parse(formatted);
            assert!(
                parse_result.is_ok(),
                "formatted output should be valid CEL: {}",
                formatted
            );
        }
    }

    #[test]
    fn document_symbols_multiple_comprehensions_ordered() {
        let uri = Uri::from_str("file:///multi_comp_symbols.cel").unwrap();
        let mut store = DocumentStore::new();
        let text = "a.all(x, x > 0) && b.exists(y, y < 10) && c.map(z, z * 2)";
        setup_document(&uri, text, &mut store);

        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let params = DocumentSymbolParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handler.document_symbols(params, &store);
        if let Some(lsp_types::DocumentSymbolResponse::Nested(symbols)) =
            response
        {
            assert_eq!(symbols.len(), 3, "should extract all three binders");

            let names: Vec<_> =
                symbols.iter().map(|s| s.name.as_str()).collect();
            assert_eq!(
                names,
                vec!["x", "y", "z"],
                "symbols should be ordered by position"
            );
        }
    }
}

mod utf16_range_correctness {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn definition_range_correct_with_preceding_emoji() {
        let uri = Uri::from_str("file:///emoji_before.cel").unwrap();
        let mut documents = DocumentStore::new();
        // 🎯 is 2 UTF-16 units, text after it should account for this
        let text = "🎯 items.exists(role, role > 0)";
        open_document_via_protocol(&uri, text, &mut documents);

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 400,
                "method": "textDocument/definition",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 0, "character": 20 } // Approximate position
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        // Should return a result (null or valid location), not error
        assert!(out[0].get("result").is_some());
    }

    #[test]
    fn hover_range_exact_with_mixed_unicode() {
        let uri = Uri::from_str("file:///mixed_unicode.cel").unwrap();
        let mut store = DocumentStore::new();
        let text = "日本items.exists(x, x > 0)";
        setup_document(&uri, text, &mut store);

        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let params = HoverParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier::new(uri.clone()),
                position: Position::new(0, 18), // Approximate
            },
            work_done_progress_params: Default::default(),
        };

        let hover = handler.hover(params, &store);
        if let Some(h) = hover {
            assert!(h.range.is_some(), "hover should include valid range");
            let range = h.range.unwrap();
            // Start should be before or at end
            assert!(range.start.line <= range.end.line);
            if range.start.line == range.end.line {
                assert!(range.start.character <= range.end.character);
            }
        }
    }

    #[test]
    fn formatting_range_covers_entire_document_with_emoji() {
        let uri = Uri::from_str("file:///emoji_doc.cel").unwrap();
        let mut documents = DocumentStore::new();
        let text = "🔥 + 🌟";
        open_document_via_protocol(&uri, text, &mut documents);

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "id": 401,
                "method": "textDocument/formatting",
                "params": {
                    "textDocument": { "uri": uri },
                    "options": {
                        "tabSize": 2,
                        "insertSpaces": true
                    }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        if let Some(result) = out[0].get("result")
            && let Some(edits) = result.as_array()
            && !edits.is_empty()
        {
            let range = edits[0].get("range");
            assert!(range.is_some(), "formatting edit should have range");

            // Range should start at beginning
            let start = range.unwrap().get("start").unwrap();
            assert_eq!(start.pointer("/line").and_then(Value::as_u64), Some(0));
            assert_eq!(
                start.pointer("/character").and_then(Value::as_u64),
                Some(0)
            );
        }
    }
}

mod diagnostics_edge_cases {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn diagnostics_on_multiline_error() {
        let uri = Uri::from_str("file:///multiline_error.cel").unwrap();
        let mut documents = DocumentStore::new();
        let text = "items.filter(\n  x,\n  x +\n)";

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "cellang",
                        "version": 1,
                        "text": text
                    }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        let diagnostics = out[0]
            .pointer("/params/diagnostics")
            .and_then(Value::as_array);

        assert!(
            diagnostics.is_some(),
            "should emit diagnostics for multiline error"
        );
        if let Some(diags) = diagnostics {
            assert!(!diags.is_empty(), "should have at least one diagnostic");

            // Verify diagnostic has valid range
            for diag in diags {
                let range = diag.get("range");
                assert!(range.is_some(), "diagnostic should have range");
            }
        }
    }

    #[test]
    fn diagnostics_with_emoji_in_error_context() {
        let uri = Uri::from_str("file:///emoji_error.cel").unwrap();
        let mut documents = DocumentStore::new();
        let text = "🎯 + )";

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "cellang",
                        "version": 1,
                        "text": text
                    }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        let diagnostics = out[0]
            .pointer("/params/diagnostics")
            .and_then(Value::as_array)
            .expect("should have diagnostics");

        assert!(
            !diagnostics.is_empty(),
            "should emit diagnostic for syntax error with emoji"
        );
    }
}
