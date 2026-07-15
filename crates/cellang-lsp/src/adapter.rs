use std::future::Future;
use std::pin::Pin;

use serde::{Deserialize, Serialize};

type BoxFuture<'a, T> = Pin<Box<dyn Future<Output = T> + Send + 'a>>;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportMessage {
    pub payload: serde_json::Value,
}

impl TransportMessage {
    #[must_use]
    pub fn from_value(payload: serde_json::Value) -> Self {
        Self { payload }
    }
}

#[derive(Debug)]
pub enum TransportError {
    Disconnected,
    Serialization(String),
    Backend(String),
}

impl std::fmt::Display for TransportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Disconnected => f.write_str("transport disconnected"),
            Self::Serialization(error) => {
                write!(f, "transport serialization error: {error}")
            }
            Self::Backend(error) => {
                write!(f, "transport backend error: {error}")
            }
        }
    }
}

impl std::error::Error for TransportError {}

pub trait MessageReader {
    fn read<'a>(
        &'a mut self,
    ) -> BoxFuture<'a, Result<Option<TransportMessage>, TransportError>>;
}

pub trait MessageWriter {
    fn write<'a>(
        &'a mut self,
        message: TransportMessage,
    ) -> BoxFuture<'a, Result<(), TransportError>>;
}

pub trait MessageChannel {
    fn recv<'a>(
        &'a mut self,
    ) -> BoxFuture<'a, Result<Option<TransportMessage>, TransportError>>;

    fn send<'a>(
        &'a mut self,
        message: TransportMessage,
    ) -> BoxFuture<'a, Result<(), TransportError>>;
}
