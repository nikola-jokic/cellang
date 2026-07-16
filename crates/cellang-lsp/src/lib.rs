//! Transport-agnostic Cellang LSP core scaffolding.

pub mod adapter;
pub mod capabilities;
pub mod diagnostics;
pub mod embedded;
pub mod formatter;
pub mod handlers;
pub mod position;
pub mod server;
pub mod state;
pub mod symbols;
#[cfg(all(feature = "wasm", target_arch = "wasm32"))]
pub mod wasm;

#[cfg(test)]
mod diagnostics_lifecycle;

#[cfg(test)]
mod hover_protocol;

pub use adapter::{
    MessageReader, MessageWriter, TransportError, TransportMessage,
};
pub use capabilities::mvp_server_capabilities;
pub use diagnostics::{NormalizedDiagnostic, NormalizedSeverity};
pub use embedded::{
    EmbeddedService, HostExpression, completions_for_text_with_env,
    diagnostics_for_text_with_env, document_symbols_for_text,
    hover_for_text_at_offset, hover_for_text_at_position,
    local_position_from_host_position, translate_local_range_by_start_position,
};
pub use handlers::{
    EnvFeatureHandler, FeatureHandlers, MethodNotSupportedHandler,
};
pub use position::{
    byte_offset_to_position, byte_range_to_lsp_range, lsp_range_to_byte_range,
    position_to_byte_offset, translate_local_range_by_host_start_offset,
    translate_local_range_by_host_start_position,
};
pub use server::{RequestDispatcher, ServerCore};
pub use state::{Document, DocumentStore};
pub use symbols::{
    SymbolIndex, SymbolRecord, definition_at, definition_at_with_env,
    references_at, references_at_with_env,
};
#[cfg(all(feature = "wasm", target_arch = "wasm32"))]
pub use wasm::WasmHostBridge;
