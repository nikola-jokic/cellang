use std::str::FromStr;

use lsp_types::Uri;
use serde_json::{Value, json};

use cellang_lsp::handlers::MethodNotSupportedHandler;
use cellang_lsp::server::RequestDispatcher;
use cellang_lsp::state::DocumentStore;

fn dispatch(payload: Value, documents: &mut DocumentStore) -> Vec<Value> {
    let handler = MethodNotSupportedHandler;
    let dispatcher = RequestDispatcher::new(&handler);
    dispatcher.dispatch(payload, documents)
}

fn open_document(uri: &Uri, text: &str, documents: &mut DocumentStore) {
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

#[test]
fn formatting_protocol_returns_full_document_text_edit() {
    let uri =
        Uri::from_str("file:///workspace/formatting.cel").expect("valid uri");
    let mut documents = DocumentStore::new();
    open_document(&uri, "foo(1,2)+bar[0]", &mut documents);

    let out = dispatch(
        json!({
            "jsonrpc": "2.0",
            "id": 9,
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

    assert_eq!(out.len(), 1, "formatting should emit one response");
    println!("formatting response: {}", out[0]);

    let edits = out[0]
        .get("result")
        .and_then(Value::as_array)
        .expect("formatting result should be edit array");
    assert_eq!(edits.len(), 1, "formatter should return a single full edit");

    let edit = &edits[0];
    assert_eq!(
        edit.pointer("/newText").and_then(Value::as_str),
        Some("foo(1, 2) + bar[0]")
    );
    assert_eq!(
        edit.get("range"),
        Some(&json!({
            "start": { "line": 0, "character": 0 },
            "end": { "line": 0, "character": 15 }
        }))
    );
}

#[test]
fn formatting_protocol_is_deterministic_for_same_document() {
    let uri = Uri::from_str("file:///workspace/deterministic.cel")
        .expect("valid uri");
    let mut documents = DocumentStore::new();
    open_document(&uri, "{foo:[1,2],bar:3}", &mut documents);

    let request = json!({
        "jsonrpc": "2.0",
        "id": 11,
        "method": "textDocument/formatting",
        "params": {
            "textDocument": { "uri": uri },
            "options": {
                "tabSize": 2,
                "insertSpaces": true
            }
        }
    });

    let first = dispatch(request.clone(), &mut documents);
    let second = dispatch(request, &mut documents);

    let first_text = first[0]
        .pointer("/result/0/newText")
        .and_then(Value::as_str)
        .expect("first formatted text");
    let second_text = second[0]
        .pointer("/result/0/newText")
        .and_then(Value::as_str)
        .expect("second formatted text");

    assert_eq!(first_text, second_text);
    assert_eq!(first_text, "{foo: [1, 2], bar: 3}");
}

#[test]
fn formatting_protocol_returns_explicit_unsupported_error() {
    let uri =
        Uri::from_str("file:///workspace/unsupported.cel").expect("valid uri");
    let mut documents = DocumentStore::new();
    open_document(&uri, "a ? b : c", &mut documents);

    let out = dispatch(
        json!({
            "jsonrpc": "2.0",
            "id": 22,
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
    println!("unsupported formatting response: {}", out[0]);

    let error = out[0].get("error").expect("response should contain error");
    assert_eq!(error.pointer("/code").and_then(Value::as_i64), Some(-32803));
    assert_eq!(
        error.pointer("/message").and_then(Value::as_str),
        Some("Formatting failed")
    );
    assert_eq!(
        error.pointer("/data/kind").and_then(Value::as_str),
        Some("unsupported_construct")
    );
    assert_eq!(
        error.pointer("/data/message").and_then(Value::as_str),
        Some("Formatting unsupported construct: ternary expressions")
    );
}
