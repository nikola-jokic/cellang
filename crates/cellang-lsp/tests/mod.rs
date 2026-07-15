use cellang_lsp::handlers::FeatureHandlers;
use cellang_lsp::state::{Document, DocumentStore};
use lsp_types::{
    CompletionItemKind, CompletionParams, DocumentSymbolParams, Position,
    Range, SymbolKind, TextDocumentIdentifier, TextDocumentPositionParams, Uri,
};
use serde_json::{Value, json};

// Integration test placeholder module.

mod completion_symbols_protocol {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn completion_returns_environment_symbols() {
        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let mut store = DocumentStore::new();
        let uri = Uri::from_str("file:///test.cel").unwrap();

        store.upsert(Document::new(uri.clone(), 1, "x + 1".to_string()));

        let params = CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position {
                    line: 0,
                    character: 0,
                },
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: None,
        };

        let response = handler.completion(params, &store);
        assert!(response.is_some());

        if let Some(lsp_types::CompletionResponse::Array(items)) = response {
            assert!(
                !items.is_empty(),
                "should return at least builtin functions"
            );

            let has_size = items.iter().any(|item| item.label == "size");
            assert!(has_size, "should include 'size' builtin function");

            let has_contains =
                items.iter().any(|item| item.label == "contains");
            assert!(has_contains, "should include 'contains' builtin function");

            let function_items: Vec<_> = items
                .iter()
                .filter(|item| item.kind == Some(CompletionItemKind::FUNCTION))
                .collect();
            assert!(!function_items.is_empty(), "should have function items");
        } else {
            panic!("expected CompletionResponse::Array");
        }
    }

    #[test]
    fn completion_includes_local_symbols() {
        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let mut store = DocumentStore::new();
        let uri = Uri::from_str("file:///test.cel").unwrap();

        let text = "items.exists(item, item.value > 0)";
        store.upsert(Document::new(uri.clone(), 1, text.to_string()));

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
        assert!(response.is_some());

        if let Some(lsp_types::CompletionResponse::Array(items)) = response {
            let has_item = items.iter().any(|i| i.label == "item");
            let has_items = items.iter().any(|i| i.label == "items");

            assert!(
                has_item || has_items,
                "should include local identifiers from document"
            );
        }
    }

    #[test]
    fn completion_sorted_alphabetically() {
        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let mut store = DocumentStore::new();
        let uri = Uri::from_str("file:///test.cel").unwrap();

        store.upsert(Document::new(uri.clone(), 1, "1 + 1".to_string()));

        let params = CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position {
                    line: 0,
                    character: 0,
                },
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: None,
        };

        let response = handler.completion(params, &store);
        assert!(response.is_some());

        if let Some(lsp_types::CompletionResponse::Array(items)) = response {
            let labels: Vec<_> =
                items.iter().map(|i| i.label.as_str()).collect();
            let mut sorted_labels = labels.clone();
            sorted_labels.sort();

            assert_eq!(
                labels, sorted_labels,
                "completion items should be sorted alphabetically"
            );
        }
    }

    #[test]
    fn document_symbols_empty_for_simple_expressions() {
        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let mut store = DocumentStore::new();
        let uri = Uri::from_str("file:///test.cel").unwrap();

        store.upsert(Document::new(uri.clone(), 1, "1 + 1".to_string()));

        let params = DocumentSymbolParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handler.document_symbols(params, &store);

        assert!(
            response.is_none()
                || matches!(response, Some(lsp_types::DocumentSymbolResponse::Nested(ref v)) if v.is_empty()),
            "simple expressions should have no document symbols"
        );
    }

    #[test]
    fn document_symbols_includes_comprehension_binders() {
        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let mut store = DocumentStore::new();
        let uri = Uri::from_str("file:///test.cel").unwrap();

        let text = "items.exists(item, item > 0)";
        store.upsert(Document::new(uri.clone(), 1, text.to_string()));

        let params = DocumentSymbolParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handler.document_symbols(params, &store);

        if let Some(lsp_types::DocumentSymbolResponse::Nested(symbols)) =
            response
        {
            assert!(
                !symbols.is_empty(),
                "should have at least one symbol for comprehension binder"
            );

            let has_item_symbol = symbols
                .iter()
                .any(|s| s.name == "item" && s.kind == SymbolKind::VARIABLE);

            assert!(
                has_item_symbol,
                "should include 'item' comprehension binder as VARIABLE symbol"
            );
        } else {
            panic!("expected DocumentSymbolResponse::Nested with symbols");
        }
    }

    #[test]
    fn document_symbols_deterministic_ordering() {
        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let mut store = DocumentStore::new();
        let uri = Uri::from_str("file:///test.cel").unwrap();

        let text = "items.all(x, x > 0) && values.exists(y, y < 10)";
        store.upsert(Document::new(uri.clone(), 1, text.to_string()));

        let params = DocumentSymbolParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handler.document_symbols(params, &store);

        if let Some(lsp_types::DocumentSymbolResponse::Nested(symbols)) =
            response
        {
            let positions: Vec<_> = symbols
                .iter()
                .map(|s| {
                    (
                        s.selection_range.start.line,
                        s.selection_range.start.character,
                    )
                })
                .collect();

            let mut sorted_positions = positions.clone();
            sorted_positions.sort();

            assert_eq!(
                positions, sorted_positions,
                "symbols should be sorted by position"
            );
        }
    }
}

mod def_ref_protocol {
    use super::*;

    fn dispatch(payload: Value, documents: &mut DocumentStore) -> Vec<Value> {
        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let dispatcher = cellang_lsp::RequestDispatcher::new(&handler);
        dispatcher.dispatch(payload, documents)
    }

    fn open_document(uri: &Uri, text: &str, documents: &mut DocumentStore) {
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
            documents,
        );

        assert_eq!(out.len(), 1, "didOpen should publish diagnostics");
    }

    mod definition {
        use std::str::FromStr;

        use super::*;

        #[test]
        fn resolves_local_symbol_definition_with_exact_uri_and_range() {
            let uri = Uri::from_str("file:///workspace/def_ref.cel")
                .expect("valid uri");
            let text = "roles.exists(role, role == target && role != fallback)";
            let mut documents = DocumentStore::new();
            open_document(&uri, text, &mut documents);

            let out = dispatch(
                json!({
                    "jsonrpc": "2.0",
                    "id": 1,
                    "method": "textDocument/definition",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": { "line": 0, "character": 20 }
                    }
                }),
                &mut documents,
            );

            assert_eq!(out.len(), 1);
            assert_eq!(out[0].get("id").and_then(Value::as_i64), Some(1));
            assert_eq!(
                out[0].pointer("/result/uri").and_then(Value::as_str),
                Some(uri.as_str())
            );
            assert_eq!(
                out[0].pointer("/result/range"),
                Some(&json!(Range::new(
                    Position::new(0, 13),
                    Position::new(0, 17),
                )))
            );
        }

        #[test]
        fn missing_symbol_definition_returns_null() {
            let uri = Uri::from_str("file:///workspace/def_ref_missing.cel")
                .expect("valid uri");
            let text = "missing + 1";
            let mut documents = DocumentStore::new();
            open_document(&uri, text, &mut documents);

            let out = dispatch(
                json!({
                    "jsonrpc": "2.0",
                    "id": 2,
                    "method": "textDocument/definition",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": { "line": 0, "character": 0 }
                    }
                }),
                &mut documents,
            );

            assert_eq!(out.len(), 1);
            assert_eq!(out[0].get("id").and_then(Value::as_i64), Some(2));
            assert_eq!(out[0].get("result"), Some(&Value::Null));
        }
    }

    mod references {
        use std::str::FromStr;

        use super::*;

        #[test]
        fn resolves_local_symbol_references_with_exact_sorted_ranges() {
            let uri = Uri::from_str("file:///workspace/def_ref_refs.cel")
                .expect("valid uri");
            let text = "roles.exists(role, role == target && role != fallback)";
            let mut documents = DocumentStore::new();
            open_document(&uri, text, &mut documents);

            let out = dispatch(
                json!({
                    "jsonrpc": "2.0",
                    "id": 3,
                    "method": "textDocument/references",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": { "line": 0, "character": 20 },
                        "context": { "includeDeclaration": true }
                    }
                }),
                &mut documents,
            );

            assert_eq!(out.len(), 1);
            assert_eq!(out[0].get("id").and_then(Value::as_i64), Some(3));
            assert_eq!(
                out[0].pointer("/result"),
                Some(&json!([
                    {
                        "uri": uri,
                        "range": Range::new(Position::new(0, 13), Position::new(0, 17))
                    },
                    {
                        "uri": uri,
                        "range": Range::new(Position::new(0, 18), Position::new(0, 22))
                    },
                    {
                        "uri": uri,
                        "range": Range::new(Position::new(0, 31), Position::new(0, 35))
                    }
                ]))
            );
        }

        #[test]
        fn missing_symbol_references_returns_empty_result() {
            let uri =
                Uri::from_str("file:///workspace/def_ref_refs_missing.cel")
                    .expect("valid uri");
            let text = "missing + 1";
            let mut documents = DocumentStore::new();
            open_document(&uri, text, &mut documents);

            let out = dispatch(
                json!({
                    "jsonrpc": "2.0",
                    "id": 4,
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
            assert_eq!(out[0].get("id").and_then(Value::as_i64), Some(4));
            assert_eq!(out[0].pointer("/result"), Some(&json!([])));
        }
    }
}
