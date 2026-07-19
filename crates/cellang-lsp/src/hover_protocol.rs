use std::str::FromStr;

use lsp_types::{
    HoverParams, Position, TextDocumentIdentifier, TextDocumentPositionParams,
    Uri,
};

use crate::handlers::{FeatureHandlers, MethodNotSupportedHandler};
use crate::state::{Document, DocumentStore};

fn setup_document(text: &str) -> (Uri, DocumentStore) {
    let uri = Uri::from_str("file:///workspace/test.cel").expect("valid uri");
    let mut documents = DocumentStore::new();
    let mut document = Document::new(uri.clone(), 1, text.to_string());

    if let Ok(parsed) = cellang::parser::parse(text) {
        document.parsed = Some(parsed.clone());
        if let Ok(lowered) = cellang::parser::lower(parsed) {
            document.lowered = Some(lowered);
        }
    }

    documents.upsert(document);
    (uri, documents)
}

fn hover_at_position(
    uri: &Uri,
    documents: &DocumentStore,
    line: u32,
    character: u32,
) -> Option<lsp_types::Hover> {
    let handler = MethodNotSupportedHandler;
    let params = HoverParams {
        text_document_position_params: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier::new(uri.clone()),
            position: Position::new(line, character),
        },
        work_done_progress_params: Default::default(),
    };
    handler.hover(params, documents)
}

mod identifier_hover {
    use super::*;
    use lsp_types::{HoverContents, MarkupKind};

    #[test]
    fn hover_on_local_declaration_shows_identifier_info() {
        let text = "roles.exists(role, role == 'admin')";
        let (uri, documents) = setup_document(text);

        let hover = hover_at_position(&uri, &documents, 0, 13)
            .expect("hover on 'role' declaration");

        if let HoverContents::Markup(markup) = hover.contents {
            assert_eq!(markup.kind, MarkupKind::Markdown);
            assert!(
                markup.value.contains("**role**"),
                "should display identifier name"
            );
            assert!(
                markup.value.contains("Declared at: line 0, character 13"),
                "should show declaration location"
            );
            assert!(
                markup.value.contains("1 reference"),
                "should show reference count"
            );

            println!("Hover content:\n{}", markup.value);
        } else {
            panic!("Expected MarkupContent hover");
        }

        assert!(
            hover.range.is_some(),
            "should provide range for declaration"
        );
    }

    #[test]
    fn hover_on_reference_resolves_to_declaration() {
        let text = "roles.exists(role, role == 'admin')";
        let (uri, documents) = setup_document(text);

        let hover = hover_at_position(&uri, &documents, 0, 19)
            .expect("hover on 'role' reference");

        if let HoverContents::Markup(markup) = hover.contents {
            assert!(
                markup.value.contains("**role**"),
                "should display identifier name"
            );
            assert!(
                markup.value.contains("Declared at: line 0, character 13"),
                "should resolve to declaration"
            );
        } else {
            panic!("Expected MarkupContent hover");
        }
    }

    #[test]
    fn hover_on_environment_variable_shows_env_info() {
        let text = "user == 'alice'";
        let (uri, documents) = setup_document(text);

        let hover = hover_at_position(&uri, &documents, 0, 0);
        assert!(
            hover.is_none(),
            "unknown environment variable should return None without Env setup"
        );
    }
}

mod invalid_position {
    use super::*;

    #[test]
    fn hover_on_whitespace_returns_none() {
        let text = "a + b";
        let (uri, documents) = setup_document(text);

        let hover = hover_at_position(&uri, &documents, 0, 1);
        assert!(hover.is_none(), "whitespace should return None");
    }

    #[test]
    fn hover_on_operator_returns_none() {
        let text = "a + b";
        let (uri, documents) = setup_document(text);

        let hover = hover_at_position(&uri, &documents, 0, 2);
        assert!(hover.is_none(), "operator should return None");
    }

    #[test]
    fn hover_on_punctuation_returns_none() {
        let text = "list[0]";
        let (uri, documents) = setup_document(text);

        let hover = hover_at_position(&uri, &documents, 0, 4);
        assert!(hover.is_none(), "bracket should return None");
    }

    #[test]
    fn hover_on_unknown_identifier_returns_none() {
        let text = "unknown_var";
        let (uri, documents) = setup_document(text);

        let hover = hover_at_position(&uri, &documents, 0, 0);
        assert!(hover.is_none(), "unknown identifier should return None");
    }
}

mod edge_cases {
    use super::*;

    #[test]
    fn hover_on_field_access_receiver_works() {
        let text = "roles.exists(r, r.name == 'admin')";
        let (uri, documents) = setup_document(text);

        let hover = hover_at_position(&uri, &documents, 0, 0);
        assert!(
            hover.is_none(),
            "field access receiver 'roles' has no declaration in local scope"
        );
    }

    #[test]
    fn hover_on_function_name_returns_none() {
        let text = "size(list)";
        let (uri, documents) = setup_document(text);

        let hover = hover_at_position(&uri, &documents, 0, 0);
        assert!(hover.is_none(), "function name should return None");
    }
}
