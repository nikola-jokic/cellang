//! Transport-agnostic Cellang LSP core scaffolding.

pub mod adapter;
pub mod capabilities;
pub mod diagnostics;
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
pub use handlers::{FeatureHandlers, MethodNotSupportedHandler};
pub use position::{
    byte_offset_to_position, byte_range_to_lsp_range, lsp_range_to_byte_range,
    position_to_byte_offset,
};
pub use server::{RequestDispatcher, ServerCore};
pub use state::{Document, DocumentStore};
pub use symbols::{
    SymbolIndex, SymbolRecord, definition_at, definition_at_with_env,
    references_at, references_at_with_env,
};
#[cfg(all(feature = "wasm", target_arch = "wasm32"))]
pub use wasm::WasmHostBridge;
