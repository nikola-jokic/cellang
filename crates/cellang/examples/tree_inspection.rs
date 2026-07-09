//! Demonstrates syntax tree inspection for IDE/LSP tooling and analysis.
//!
//! This example shows how to parse CEL expressions and inspect the resulting
//! concrete syntax tree (CST) using rowan traversal and the inspection API.
//!
//! Run with: cargo run --example tree_inspection

use cellang::{
    SyntaxKind,
    inspection::{node_at_offset, text_range},
    parser::{CelNode, parse},
};
use rowan::TextSize;

fn main() -> Result<(), cellang::Error> {
    println!("=== CEL Syntax Tree Inspection Examples ===\n");

    // Use Case 1: Basic Tree Traversal
    basic_tree_traversal()?;

    // Use Case 2: LSP Hover Simulation
    lsp_hover_simulation()?;

    // Use Case 3: Extract All Identifiers
    extract_identifiers()?;

    // Use Case 4: Analyze Binary Operations
    analyze_binary_operations()?;

    // Use Case 5: Error-Tolerant Parsing
    error_tolerant_parsing()?;

    Ok(())
}

/// Use Case 1: Parse an expression and walk the entire syntax tree
fn basic_tree_traversal() -> Result<(), cellang::Error> {
    println!("--- Use Case 1: Basic Tree Traversal ---");

    let source = "users.filter(u, u.age > 18).map(u, u.name)";
    println!("Source: {}\n", source);

    let green = parse(source)?;
    let root = CelNode::new_root(green);

    println!("Tree structure (depth-first):");
    for (depth, node) in walk_tree(&root, 0) {
        let indent = "  ".repeat(depth);
        let text = node.text().to_string().replace('\n', "\\n");
        let text_display = if text.len() > 30 {
            format!("{}...", &text[..27])
        } else {
            text
        };
        println!("{}{:?} '{}'", indent, node.kind(), text_display);
    }

    println!();
    Ok(())
}

/// Helper to walk tree with depth tracking
fn walk_tree(node: &CelNode, depth: usize) -> Vec<(usize, CelNode)> {
    let mut result = vec![(depth, node.clone())];
    for child in node.children() {
        result.extend(walk_tree(&child, depth + 1));
    }
    result
}

/// Use Case 2: Simulate LSP hover - find node at cursor position
fn lsp_hover_simulation() -> Result<(), cellang::Error> {
    println!("--- Use Case 2: LSP Hover Simulation ---");

    let source = "users[0].name.startsWith('A')";
    println!("Source: {}", source);
    println!("        ^------- (simulating cursor at offset 8: 'name')");

    let green = parse(source)?;
    let root = CelNode::new_root(green);

    let offset = TextSize::from(8); // cursor on 'name'
    if let Some(node) = node_at_offset(&root, offset) {
        let range = text_range(&node);
        let text = node.text().to_string();
        println!("\nHover info:");
        println!("  Kind: {:?}", node.kind());
        println!("  Text: '{}'", text);
        println!("  Range: {:?}", range);

        // Show parent context
        if let Some(parent) = node.parent() {
            println!("  Parent: {:?} '{}'", parent.kind(), parent.text());
        }
    }

    println!();
    Ok(())
}

/// Use Case 3: Extract all identifiers from an expression
fn extract_identifiers() -> Result<(), cellang::Error> {
    println!("--- Use Case 3: Extract All Identifiers ---");

    let source = "user.name == 'Alice' && user.age >= 18 && user.role in roles";
    println!("Source: {}\n", source);

    let green = parse(source)?;
    let root = CelNode::new_root(green);

    let mut identifiers = Vec::new();
    for node in root.descendants() {
        if node.kind() == SyntaxKind::Ident {
            identifiers.push(node.text().to_string());
        }
    }

    println!("Identifiers found: {:?}", identifiers);
    println!("Total: {} unique identifiers", identifiers.len());

    println!();
    Ok(())
}

/// Use Case 4: Analyze binary operations and their structure
fn analyze_binary_operations() -> Result<(), cellang::Error> {
    println!("--- Use Case 4: Analyze Binary Operations ---");

    let source = "(a + b) * c - d / e";
    println!("Source: {}\n", source);

    let green = parse(source)?;
    let root = CelNode::new_root(green);

    println!("Binary operations (in evaluation order):");
    let mut ops = Vec::new();
    for node in root.descendants() {
        if node.kind() == SyntaxKind::BinaryOp {
            // Find the operator token
            let operator = node
                .children_with_tokens()
                .find_map(|child| {
                    child.as_token().and_then(|t| match t.kind() {
                        SyntaxKind::Plus => Some("+"),
                        SyntaxKind::Minus => Some("-"),
                        SyntaxKind::Star => Some("*"),
                        SyntaxKind::Slash => Some("/"),
                        _ => None,
                    })
                })
                .unwrap_or("?");

            let text = node.text().to_string();
            ops.push(format!("  {} in: '{}'", operator, text));
        }
    }

    for op in ops {
        println!("{}", op);
    }

    println!();
    Ok(())
}

/// Use Case 5: Demonstrate error-tolerant parsing
fn error_tolerant_parsing() -> Result<(), cellang::Error> {
    println!("--- Use Case 5: Error-Tolerant Parsing ---");

    let source = "foo(bar,"; // intentionally malformed (unclosed paren)
    println!("Source: {} (malformed - unclosed paren)\n", source);

    // Rowan's error recovery means we still get a tree
    let green = parse(source)?;
    let root = CelNode::new_root(green);

    println!("Tree built successfully despite errors:");
    let mut error_count = 0;
    let mut node_count = 0;

    for node in root.descendants_with_tokens() {
        node_count += 1;
        if let Some(token) = node.as_token() {
            if token.kind() == SyntaxKind::Error {
                error_count += 1;
                println!(
                    "  Error token at offset {:?}: '{}'",
                    token.text_range().start(),
                    token.text()
                );
            }
        }
    }

    println!("\nStatistics:");
    println!("  Total nodes: {}", node_count);
    println!("  Error tokens: {}", error_count);
    println!("  Tree is still traversable and queryable!");

    // Even with errors, we can still extract what we parsed successfully
    println!("\nIdentifiers found despite errors:");
    for node in root.descendants() {
        if node.kind() == SyntaxKind::Ident {
            println!("  - {}", node.text());
        }
    }

    println!();
    Ok(())
}
