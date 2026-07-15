use lsp_types::Uri;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub struct Document {
    pub uri: Uri,
    pub version: i32,
    pub text: String,
    pub parsed: Option<cellang::parser::ParseResult>,
    pub lowered: Option<cellang::parser::Expr>,
}

impl Document {
    #[must_use]
    pub fn new(uri: Uri, version: i32, text: String) -> Self {
        Self {
            uri,
            version,
            text,
            parsed: None,
            lowered: None,
        }
    }
}

#[derive(Debug, Default)]
pub struct DocumentStore {
    documents: HashMap<Uri, Document>,
}

impl DocumentStore {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn upsert(&mut self, document: Document) {
        self.documents.insert(document.uri.clone(), document);
    }

    #[must_use]
    pub fn get(&self, uri: &Uri) -> Option<&Document> {
        self.documents.get(uri)
    }

    pub fn remove(&mut self, uri: &Uri) {
        self.documents.remove(uri);
    }
}
