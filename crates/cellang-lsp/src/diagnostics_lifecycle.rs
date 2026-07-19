use lsp_types::{Position, Range, Uri};
use serde_json::{Value, json};

use crate::handlers::MethodNotSupportedHandler;
use crate::server::RequestDispatcher;
use crate::state::DocumentStore;

fn dispatch(payload: Value, documents: &mut DocumentStore) -> Vec<Value> {
    let handler = MethodNotSupportedHandler;
    let dispatcher = RequestDispatcher::new(&handler);
    dispatcher.dispatch(payload, documents)
}

mod emit {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn malformed_source_emits_exact_diagnostic_range_and_message() {
        let uri =
            Uri::from_str("file:///workspace/example.cel").expect("valid uri");
        let mut documents = DocumentStore::new();

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "cellang",
                        "version": 1,
                        "text": "1 + )"
                    }
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        println!("didOpen publish payload: {}", out[0]);

        let diagnostics = out[0]
            .pointer("/params/diagnostics")
            .and_then(Value::as_array)
            .expect("diagnostics array");
        assert_eq!(diagnostics.len(), 1, "should emit one parser diagnostic");

        let diagnostic = &diagnostics[0];
        assert_eq!(
            diagnostic.get("message").and_then(Value::as_str),
            Some("Unexpected token")
        );
        assert_eq!(
            diagnostic.get("range"),
            Some(&json!(Range::new(Position::new(0, 4), Position::new(0, 5))))
        );

        let document = documents.get(&uri).expect("document stored on open");
        assert_eq!(document.version, 1);
        assert_eq!(document.text, "1 + )");
        assert!(
            document.parsed.is_none() && document.lowered.is_none(),
            "failed parse should not cache parse/lower results"
        );
    }
}

mod clear {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn diagnostics_clear_after_fix_on_did_change() {
        let uri =
            Uri::from_str("file:///workspace/example.cel").expect("valid uri");
        let mut documents = DocumentStore::new();

        let _ = dispatch(
            json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "cellang",
                        "version": 1,
                        "text": "1 + )"
                    }
                }
            }),
            &mut documents,
        );

        let out = dispatch(
            json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didChange",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "version": 2
                    },
                    "contentChanges": [
                        {
                            "text": "1 + 1"
                        }
                    ]
                }
            }),
            &mut documents,
        );

        assert_eq!(out.len(), 1);
        println!("didChange publish payload: {}", out[0]);

        let diagnostics = out[0]
            .pointer("/params/diagnostics")
            .and_then(Value::as_array)
            .expect("diagnostics array");
        assert!(diagnostics.is_empty(), "diagnostics should clear after fix");

        let version = out[0]
            .pointer("/params/version")
            .and_then(Value::as_i64)
            .expect("version should be published");
        assert_eq!(version, 2);

        let document = documents.get(&uri).expect("document stored on change");
        assert_eq!(document.version, 2);
        assert_eq!(document.text, "1 + 1");
        assert!(
            document.parsed.is_some(),
            "successful parse should be cached"
        );
        assert!(
            document.lowered.is_some(),
            "successful lowering should be cached"
        );
    }
}
