use cellang::Env;
use cellang::types::{FunctionDecl, IdentDecl, OverloadDecl, Type};
use cellang_lsp::FeatureHandlers;
use cellang_lsp::state::{Document, DocumentStore};
use lsp_types::{
    CompletionItemKind, CompletionParams, DocumentSymbolParams, Position,
    Range, SymbolKind, TextDocumentIdentifier, TextDocumentPositionParams, Uri,
};
use serde_json::{Value, json};

// Integration test placeholder module.

fn custom_policy_env() -> Env {
    let mut builder = Env::builder();
    builder
        .add_ident(
            IdentDecl::new("principal", Type::String)
                .with_doc("The authenticated principal"),
        )
        .expect("principal ident should register");

    let mut allowed = FunctionDecl::new("allowed")
        .with_doc("Checks whether the principal can access the resource");
    allowed
        .add_overload(OverloadDecl::new(
            "allowed_string_string",
            vec![Type::String, Type::String],
            Type::Bool,
        ))
        .expect("allowed overload should register");
    builder
        .add_function(allowed)
        .expect("allowed function should register");

    builder.build()
}

mod completion_symbols_protocol {
    use std::str::FromStr;

    use lsp_types::MarkupContent;

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
    fn completion_uses_supplied_environment_definitions() {
        let handler = cellang_lsp::EnvFeatureHandler::new(custom_policy_env());
        let mut store = DocumentStore::new();
        let uri = Uri::from_str("file:///custom-env-completion.cel").unwrap();

        store.upsert(Document::new(uri.clone(), 1, "prin".to_string()));

        let params = CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position {
                    line: 0,
                    character: 4,
                },
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: None,
        };

        let response = handler
            .completion(params, &store)
            .expect("custom env completion should produce items");

        let lsp_types::CompletionResponse::Array(items) = response else {
            panic!("expected CompletionResponse::Array");
        };

        let principal = items
            .iter()
            .find(|item| item.label == "principal")
            .expect("custom env ident should be offered");
        assert_eq!(principal.kind, Some(CompletionItemKind::VARIABLE));
        assert_eq!(
            principal.documentation,
            Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                kind: lsp_types::MarkupKind::Markdown,
                value: "The authenticated principal".to_string()
            }))
        );

        let allowed = items
            .iter()
            .find(|item| item.label == "allowed")
            .expect("custom env function should be offered");
        assert_eq!(allowed.kind, Some(CompletionItemKind::FUNCTION));
        assert_eq!(
            allowed.documentation,
            Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                kind: lsp_types::MarkupKind::Markdown,
                value: "Checks whether the principal can access the resource"
                    .to_string()
            }))
        );
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

mod custom_environment_protocol {
    use std::str::FromStr;

    use super::*;

    fn dispatch_with_custom_env(
        payload: Value,
        documents: &mut DocumentStore,
    ) -> Vec<Value> {
        let handler = cellang_lsp::EnvFeatureHandler::new(custom_policy_env());
        let dispatcher = cellang_lsp::RequestDispatcher::new(&handler);
        dispatcher.dispatch(payload, documents)
    }

    #[test]
    fn did_open_diagnostics_type_check_with_supplied_environment() {
        let uri = Uri::from_str("file:///workspace/custom-env.cel")
            .expect("valid uri");
        let mut documents = DocumentStore::new();

        let out = dispatch_with_custom_env(
            json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "cellang",
                        "version": 1,
                        "text": "allowed(principal, 'resource-1')"
                    }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1, "didOpen should publish diagnostics");
        assert_eq!(
            out[0].pointer("/method").and_then(Value::as_str),
            Some("textDocument/publishDiagnostics")
        );
        assert_eq!(
            out[0]
                .pointer("/params/diagnostics")
                .and_then(Value::as_array)
                .map(Vec::len),
            Some(0),
            "custom env idents/functions should type-check cleanly"
        );
    }

    #[test]
    fn default_environment_still_reports_unknown_custom_definitions() {
        let uri = Uri::from_str("file:///workspace/default-env.cel")
            .expect("valid uri");
        let mut documents = DocumentStore::new();
        let handler = cellang_lsp::handlers::MethodNotSupportedHandler;
        let dispatcher = cellang_lsp::RequestDispatcher::new(&handler);

        let out = dispatcher.dispatch(
            json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "cellang",
                        "version": 1,
                        "text": "allowed(principal, 'resource-1')"
                    }
                }
            }),
            &mut documents,
        );

        let diagnostics = out[0]
            .pointer("/params/diagnostics")
            .and_then(Value::as_array)
            .expect("default env should publish diagnostics");
        assert!(
            !diagnostics.is_empty(),
            "without custom env, custom definitions should remain unknown"
        );
    }

    #[test]
    fn references_resolve_supplied_environment_identifier() {
        let uri = Uri::from_str("file:///workspace/custom-env-refs.cel")
            .expect("valid uri");
        let mut documents = DocumentStore::new();

        dispatch_with_custom_env(
            json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "cellang",
                        "version": 1,
                        "text": "principal == 'alice' || principal == 'bob'"
                    }
                }
            }),
            &mut documents,
        );

        let out = dispatch_with_custom_env(
            json!({
                "jsonrpc": "2.0",
                "id": 51,
                "method": "textDocument/references",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 0, "character": 1 },
                    "context": { "includeDeclaration": true }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        assert_eq!(out[0].get("id").and_then(Value::as_i64), Some(51));
        assert_eq!(
            out[0].pointer("/result"),
            Some(&json!([
                {
                    "uri": uri,
                    "range": Range::new(Position::new(0, 0), Position::new(0, 9))
                },
                {
                    "uri": uri,
                    "range": Range::new(Position::new(0, 17), Position::new(0, 26))
                }
            ]))
        );
    }

    #[test]
    fn hover_describes_supplied_environment_identifier() {
        let uri = Uri::from_str("file:///workspace/custom-env-hover.cel")
            .expect("valid uri");
        let mut store = DocumentStore::new();
        let text = "principal == 'alice'";
        let mut document = Document::new(uri.clone(), 1, text.to_string());
        document.parsed = cellang::parser::parse(text).ok();
        store.upsert(document);

        let handler = cellang_lsp::EnvFeatureHandler::new(custom_policy_env());
        let hover = handler
            .hover(
                lsp_types::HoverParams {
                    text_document_position_params: TextDocumentPositionParams {
                        text_document: TextDocumentIdentifier { uri },
                        position: Position::new(0, 1),
                    },
                    work_done_progress_params: Default::default(),
                },
                &store,
            )
            .expect("custom env ident should produce hover");

        let lsp_types::HoverContents::Markup(markup) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(markup.value.contains("**principal**"));
        assert!(markup.value.contains("*Environment variable*"));
    }

    #[test]
    fn definition_for_environment_only_identifier_returns_null() {
        let uri = Uri::from_str("file:///workspace/custom-env-def.cel")
            .expect("valid uri");
        let mut documents = DocumentStore::new();

        dispatch_with_custom_env(
            json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "cellang",
                        "version": 1,
                        "text": "principal == 'alice'"
                    }
                }
            }),
            &mut documents,
        );

        let out = dispatch_with_custom_env(
            json!({
                "jsonrpc": "2.0",
                "id": 52,
                "method": "textDocument/definition",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 0, "character": 1 }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        assert_eq!(out[0].get("id").and_then(Value::as_i64), Some(52));
        assert_eq!(out[0].get("result"), Some(&Value::Null));
    }

    #[test]
    fn environment_function_is_not_a_navigable_symbol() {
        let uri = Uri::from_str("file:///workspace/custom-env-fn-nav.cel")
            .expect("valid uri");
        let mut documents = DocumentStore::new();

        dispatch_with_custom_env(
            json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "cellang",
                        "version": 1,
                        "text": "allowed(principal, 'resource-1')"
                    }
                }
            }),
            &mut documents,
        );

        let definition = dispatch_with_custom_env(
            json!({
                "jsonrpc": "2.0",
                "id": 53,
                "method": "textDocument/definition",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 0, "character": 1 }
                }
            }),
            &mut documents,
        );
        assert_eq!(definition[0].get("result"), Some(&Value::Null));

        let references = dispatch_with_custom_env(
            json!({
                "jsonrpc": "2.0",
                "id": 54,
                "method": "textDocument/references",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 0, "character": 1 },
                    "context": { "includeDeclaration": true }
                }
            }),
            &mut documents,
        );
        assert_eq!(references[0].pointer("/result"), Some(&json!([])));
    }

    #[test]
    fn embedded_service_diagnostics_map_to_host_yaml_range() {
        let host = "rule:\n  when: allowed(principal, @)";
        let expression = "allowed(principal, @)";
        let expression_start =
            host.find(expression).expect("expression in host");
        let embedded = cellang_lsp::HostExpression::new(
            host,
            expression,
            expression_start,
        );
        let service = cellang_lsp::EmbeddedService::new(custom_policy_env());

        let diagnostics = service.lsp_diagnostics(expression);
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].message.contains("Unexpected character: @"));

        let translated = embedded.translate_diagnostic(diagnostics[0].clone());
        assert_eq!(
            translated.range,
            Range::new(Position::new(1, 27), Position::new(1, 28))
        );
    }

    #[test]
    fn embedded_service_hover_maps_back_to_host_yaml_range() {
        let host = "rule:\n  when: principal == 'alice'";
        let expression = "principal == 'alice'";
        let expression_start =
            host.find(expression).expect("expression in host");
        let embedded = cellang_lsp::HostExpression::new(
            host,
            expression,
            expression_start,
        );
        let service = cellang_lsp::EmbeddedService::new(custom_policy_env());

        let local_hover = service
            .hover_at_offset(expression, 1)
            .expect("principal should hover");
        let host_hover = embedded.translate_hover(local_hover);

        assert_eq!(
            host_hover.range,
            Some(Range::new(Position::new(1, 8), Position::new(1, 17)))
        );
        let lsp_types::HoverContents::Markup(markup) = host_hover.contents
        else {
            panic!("expected markdown hover");
        };
        assert!(markup.value.contains("**principal**"));
    }

    #[test]
    fn embedded_service_references_map_back_to_host_yaml_ranges() {
        let host = "rule:\n  when: principal == 'alice' || principal == 'bob'";
        let expression = "principal == 'alice' || principal == 'bob'";
        let expression_start =
            host.find(expression).expect("expression in host");
        let embedded = cellang_lsp::HostExpression::new(
            host,
            expression,
            expression_start,
        );
        let service = cellang_lsp::EmbeddedService::new(custom_policy_env());

        let references =
            service.references_at_position(expression, Position::new(0, 1));
        let host_ranges = references
            .into_iter()
            .map(|range| embedded.translate_range(range))
            .collect::<Vec<_>>();

        assert_eq!(
            host_ranges,
            vec![
                Range::new(Position::new(1, 8), Position::new(1, 17)),
                Range::new(Position::new(1, 25), Position::new(1, 34)),
            ]
        );
    }

    #[test]
    fn embedded_service_maps_host_cursor_to_local_position() {
        let host = "rule:\n  when: 🦀 principal == 'alice'";
        let expression = "principal == 'alice'";
        let expression_start =
            host.find(expression).expect("expression in host");

        let local = cellang_lsp::local_position_from_host_position(
            host,
            expression_start,
            expression,
            Position::new(1, 12),
        );

        assert_eq!(local, Some(Position::new(0, 1)));
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
