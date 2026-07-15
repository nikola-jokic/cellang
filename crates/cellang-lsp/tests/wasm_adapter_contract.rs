use cellang_lsp::handlers::MethodNotSupportedHandler;
use cellang_lsp::server::ServerCore;
use serde_json::{Value, json};

fn dispatch(
    core: &mut ServerCore<MethodNotSupportedHandler>,
    message: Value,
) -> Vec<Value> {
    core.handle_payload(message)
}

#[test]
fn request_in_response_out_contract() {
    let mut core = ServerCore::new(MethodNotSupportedHandler);

    let open = json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": "file:///workspace/wasm-contract.cel",
                "languageId": "cellang",
                "version": 1,
                "text": "roles.exists(role, role == target)"
            }
        }
    });

    let notifications = dispatch(&mut core, open);
    assert_eq!(notifications.len(), 1, "didOpen should publish diagnostics");
    assert_eq!(
        notifications[0].pointer("/method").and_then(Value::as_str),
        Some("textDocument/publishDiagnostics")
    );

    let definition = json!({
        "jsonrpc": "2.0",
        "id": 41,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": "file:///workspace/wasm-contract.cel" },
            "position": { "line": 0, "character": 20 }
        }
    });

    let responses = dispatch(&mut core, definition);
    assert_eq!(
        responses.len(),
        1,
        "definition request should return one response"
    );
    assert_eq!(
        responses[0].pointer("/id").and_then(Value::as_i64),
        Some(41)
    );
    assert!(responses[0].get("result").is_some());
}

#[test]
fn malformed_json_payload_inbound_contract_shape() {
    let invalid = "{not valid json}";
    let parsed = serde_json::from_str::<Value>(invalid);
    assert!(
        parsed.is_err(),
        "adapter contract expects valid JSON text payload"
    );
}
