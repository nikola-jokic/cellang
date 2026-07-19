use std::str::FromStr;

use lsp_types::{
    CompletionParams, DocumentFormattingParams, DocumentSymbolParams,
    GotoDefinitionParams, HoverParams, ReferenceParams,
};
use serde_json::{Value, json};

use crate::adapter::{
    MessageChannel, MessageReader, MessageWriter, TransportError,
    TransportMessage,
};
use crate::handlers::{FeatureHandlers, SupportedRequest};
use crate::state::{Document, DocumentStore};

#[derive(Debug)]
pub struct ServerCore<H> {
    handlers: H,
    documents: DocumentStore,
}

impl<H> ServerCore<H>
where
    H: FeatureHandlers,
{
    #[must_use]
    pub fn new(handlers: H) -> Self {
        Self {
            handlers,
            documents: DocumentStore::new(),
        }
    }

    #[must_use]
    pub fn documents(&self) -> &DocumentStore {
        &self.documents
    }

    pub fn documents_mut(&mut self) -> &mut DocumentStore {
        &mut self.documents
    }

    #[must_use]
    pub fn dispatcher(&self) -> RequestDispatcher<'_, H> {
        RequestDispatcher::new(&self.handlers)
    }

    #[must_use]
    pub fn handle_payload(&mut self, payload: Value) -> Vec<Value> {
        let dispatcher = RequestDispatcher::new(&self.handlers);
        dispatcher.dispatch(payload, &mut self.documents)
    }

    pub async fn run_channel<C>(
        &mut self,
        channel: &mut C,
    ) -> Result<(), TransportError>
    where
        C: MessageChannel,
    {
        let dispatcher = RequestDispatcher::new(&self.handlers);
        while let Some(message) = channel.recv().await? {
            let outbounds =
                dispatcher.dispatch(message.payload, &mut self.documents);
            for outbound in outbounds {
                channel.send(TransportMessage::from_value(outbound)).await?;
            }
        }

        Ok(())
    }

    pub async fn run_split<R, W>(
        &mut self,
        reader: &mut R,
        writer: &mut W,
    ) -> Result<(), TransportError>
    where
        R: MessageReader,
        W: MessageWriter,
    {
        let dispatcher = RequestDispatcher::new(&self.handlers);
        while let Some(message) = reader.read().await? {
            let outbounds =
                dispatcher.dispatch(message.payload, &mut self.documents);
            for outbound in outbounds {
                writer.write(TransportMessage::from_value(outbound)).await?;
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct RequestDispatcher<'a, H> {
    handlers: &'a H,
}

impl<'a, H> RequestDispatcher<'a, H>
where
    H: FeatureHandlers,
{
    #[must_use]
    pub fn new(handlers: &'a H) -> Self {
        Self { handlers }
    }

    #[must_use]
    pub fn dispatch(
        &self,
        payload: Value,
        documents: &mut DocumentStore,
    ) -> Vec<Value> {
        let Some(method) = payload.get("method").and_then(Value::as_str) else {
            return Vec::new();
        };

        match method {
            "textDocument/didOpen" => {
                handle_did_open(&payload, documents);
                payload
                    .pointer("/params/textDocument/uri")
                    .and_then(Value::as_str)
                    .and_then(parse_uri)
                    .and_then(|uri| {
                        self.handlers.publish_diagnostics(&uri, documents)
                    })
                    .into_iter()
                    .collect()
            }
            "textDocument/didChange" => {
                handle_did_change(&payload, documents);
                payload
                    .pointer("/params/textDocument/uri")
                    .and_then(Value::as_str)
                    .and_then(parse_uri)
                    .and_then(|uri| {
                        self.handlers.publish_diagnostics(&uri, documents)
                    })
                    .into_iter()
                    .collect()
            }
            "textDocument/definition" => {
                let result = payload
                    .get("params")
                    .cloned()
                    .and_then(|params| {
                        serde_json::from_value::<GotoDefinitionParams>(params)
                            .ok()
                    })
                    .and_then(|params| {
                        self.handlers.definition(params, documents)
                    });

                vec![
                    json!({"jsonrpc": "2.0", "id": payload.get("id"), "result": result}),
                ]
            }
            "textDocument/references" => {
                let result = payload
                    .get("params")
                    .cloned()
                    .and_then(|params| {
                        serde_json::from_value::<ReferenceParams>(params).ok()
                    })
                    .map(|params| self.handlers.references(params, documents))
                    .unwrap_or_default();

                vec![
                    json!({"jsonrpc": "2.0", "id": payload.get("id"), "result": result}),
                ]
            }
            "textDocument/hover" => {
                let result = payload
                    .get("params")
                    .cloned()
                    .and_then(|params| {
                        serde_json::from_value::<HoverParams>(params).ok()
                    })
                    .and_then(|params| self.handlers.hover(params, documents));

                vec![
                    json!({"jsonrpc": "2.0", "id": payload.get("id"), "result": result}),
                ]
            }
            "textDocument/completion" => {
                let result = payload
                    .get("params")
                    .cloned()
                    .and_then(|params| {
                        serde_json::from_value::<CompletionParams>(params).ok()
                    })
                    .and_then(|params| {
                        self.handlers.completion(params, documents)
                    });

                vec![
                    json!({"jsonrpc": "2.0", "id": payload.get("id"), "result": result}),
                ]
            }
            "textDocument/documentSymbol" => {
                let result = payload
                    .get("params")
                    .cloned()
                    .and_then(|params| {
                        serde_json::from_value::<DocumentSymbolParams>(params)
                            .ok()
                    })
                    .and_then(|params| {
                        self.handlers.document_symbols(params, documents)
                    });

                vec![
                    json!({"jsonrpc": "2.0", "id": payload.get("id"), "result": result}),
                ]
            }
            "textDocument/formatting" => {
                let id = payload.get("id").cloned().unwrap_or(Value::Null);
                let Some(raw_params) = payload.get("params").cloned() else {
                    return vec![json!({
                        "jsonrpc": "2.0",
                        "id": id,
                        "error": {
                            "code": -32602,
                            "message": "Invalid params: missing formatting params"
                        }
                    })];
                };

                let params = match serde_json::from_value::<
                    DocumentFormattingParams,
                >(raw_params)
                {
                    Ok(params) => params,
                    Err(err) => {
                        return vec![json!({
                            "jsonrpc": "2.0",
                            "id": id,
                            "error": {
                                "code": -32602,
                                "message": "Invalid params: failed to decode formatting params",
                                "data": {
                                    "kind": "invalid_params",
                                    "message": err.to_string()
                                }
                            }
                        })];
                    }
                };

                match self.handlers.formatting(params, documents) {
                    Ok(edits) => vec![json!({
                        "jsonrpc": "2.0",
                        "id": id,
                        "result": edits
                    })],
                    Err(err) => vec![json!({
                        "jsonrpc": "2.0",
                        "id": id,
                        "error": {
                            "code": -32803,
                            "message": "Formatting failed",
                            "data": err.to_response_data()
                        }
                    })],
                }
            }
            _ if SupportedRequest::from_method(method).is_some() => {
                vec![
                    json!({"jsonrpc": "2.0", "id": payload.get("id"), "result": null}),
                ]
            }
            _ => {
                let _ = &self.handlers;
                Vec::new()
            }
        }
    }
}

fn parse_uri(raw: &str) -> Option<lsp_types::Uri> {
    lsp_types::Uri::from_str(raw).ok()
}

fn build_document(uri: lsp_types::Uri, version: i32, text: String) -> Document {
    let mut document = Document::new(uri, version, text);

    if let Ok(parsed) = cellang::parser::parse(&document.text) {
        document.parsed = Some(parsed.clone());
        if let Ok(lowered) = cellang::parser::lower(parsed) {
            document.lowered = Some(lowered);
        }
    }

    document
}

fn handle_did_open(payload: &Value, documents: &mut DocumentStore) {
    let Some(uri) = payload
        .pointer("/params/textDocument/uri")
        .and_then(Value::as_str)
        .and_then(parse_uri)
    else {
        return;
    };

    let Some(version) = payload
        .pointer("/params/textDocument/version")
        .and_then(Value::as_i64)
        .and_then(|value| i32::try_from(value).ok())
    else {
        return;
    };

    let Some(text) = payload
        .pointer("/params/textDocument/text")
        .and_then(Value::as_str)
    else {
        return;
    };

    documents.upsert(build_document(uri, version, text.to_owned()));
}

fn handle_did_change(payload: &Value, documents: &mut DocumentStore) {
    let Some(uri) = payload
        .pointer("/params/textDocument/uri")
        .and_then(Value::as_str)
        .and_then(parse_uri)
    else {
        return;
    };

    let Some(version) = payload
        .pointer("/params/textDocument/version")
        .and_then(Value::as_i64)
        .and_then(|value| i32::try_from(value).ok())
    else {
        return;
    };

    let next_text = payload
        .pointer("/params/contentChanges")
        .and_then(Value::as_array)
        .and_then(|changes| changes.last())
        .and_then(|change| change.get("text"))
        .and_then(Value::as_str)
        .map(str::to_owned)
        .or_else(|| documents.get(&uri).map(|document| document.text.clone()));

    let Some(next_text) = next_text else {
        return;
    };

    documents.upsert(build_document(uri, version, next_text));
}
