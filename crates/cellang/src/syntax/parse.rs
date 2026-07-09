use rowan::GreenNode;

/// ParseResult wraps a Rowan GreenNode, representing the root of a successfully parsed CEL expression.
/// This type will eventually hold the complete syntax tree and associated metadata (source spans, etc.).
pub type ParseResult = GreenNode;
