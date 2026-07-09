# Cellang

Cellang is an implementation of the [CEL](https://cel.dev/) language interpreter in Rust.

## Motivation

Motivation behind this project is to provide a way to evaluate CEL expressions in Rust, while allowing
easier way to provide custom functions. This project is built for [BountyHub](https://bountyhub.org) project,
but is open-source and can be used by anyone.

There is a great rust project called [CEL Interpreter](https://crates.io/crates/cel-interpreter) which I initially used.

However, I found that the project is not flexible enough for my needs. I needed to be able to:
- Inspect the syntax tree during parsing for IDE/LSP support
- Add slightly more complex functions on types
- Robust error recovery for incomplete expressions

Therefore, the library exposes lower-level primitives that would allow you to do that.

## Parser Architecture

Cellang uses a **Rowan-based parser** with a clean semantic boundary:

1. **Lexer** (`lexer`) - Tokenizes source text into a stream of tokens
2. **Rowan Parser** (`parser::parse`) - Builds a lossless concrete syntax tree (CST)
   - Preserves whitespace, comments, error tokens
   - Supports error recovery for IDE/LSP workflows
3. **HIR Lowering** (`parser::lower`) - Converts CST to high-level intermediate representation
   - Strips away syntax noise (grouping parens, etc.)
   - Owned data structure suitable for semantic analysis
4. **Type Checking** (`parser::type_check`) - Validates types and builds typed expression graph
5. **Interpreter** (`parser::eval`) - Evaluates expressions against a runtime

**Note**: Existing code using nested module paths (`cellang::syntax::parser`, `cellang::hir::lower`, etc.) continues to work. Both canonical and compatibility paths coexist for additive migration.

The separation between CST (syntax layer) and HIR (semantic layer) provides:
- **CST**: Perfect for IDE tooling (preserves all source details, supports incremental parsing)
- **HIR**: Perfect for semantic analysis (clean structure, no parser lifetimes)

## Getting started

This library aims to be ergonomic without hiding the lower-level building blocks that make CEL powerful. The typical workflow is:

1. Build a `Runtime` with variables, declared types, and native functions.
2. Evaluate expressions against that runtime (or child runtimes that inherit the same environment).

```rust
use cellang::types::{FunctionDecl, OverloadDecl, Type};
use cellang::{Runtime, Value};

fn main() -> miette::Result<()> {
    let mut builder = Runtime::builder();
    builder.set_variable("first_name", "Ada")?;
    builder.set_variable("last_name", "Lovelace")?;
    builder.set_variable("roles", vec!["admin", "analyst"])?;

    let mut decl = FunctionDecl::new("full_name");
    decl.add_overload(OverloadDecl::new(
        "full_name_string_string",
        vec![Type::String, Type::String],
        Type::String,
    ))?;
    builder.add_function_decl(decl)?;
    builder.register_function("full_name", |first: String, last: String| {
        format!("{first} {last}")
    })?;

    let runtime = builder.build();
    let value = runtime.eval("full_name(first_name, last_name)")?;
    assert_eq!(value, Value::String("Ada Lovelace".into()));

    let is_admin = runtime.eval("'admin' in roles")?;
    assert_eq!(is_admin, Value::Bool(true));
    Ok(())
}
```

## Runnable Examples

The examples in [examples](examples) are written as user documentation and are also executed by `cargo test`, so they stay in sync with the public API.

Run all default-feature examples with:

```bash
cargo test -p cellang --examples
```

Run the derive-backed example with:

```bash
cargo test -p cellang --features derive --example user_role_derive
```

Good starting points:

- [examples/getting_started.rs](examples/getting_started.rs) shows variables, scoped child runtimes, function declarations, native function registration, and error handling.
- [examples/policy_rules.rs](examples/policy_rules.rs) shows map-backed request/resource data and policy expressions that can be owned outside Rust code.
- [examples/typed_environment.rs](examples/typed_environment.rs) shows typed environment metadata, compile-time validation, typed AST serialization, and runtime evaluation.
- [examples/create_function.rs](examples/create_function.rs) focuses on registering custom functions as both functions and receiver-style methods.
- [examples/env_snapshot.rs](examples/env_snapshot.rs) shows serializing an `Env` so rule metadata can be cached and reused.
- [examples/user_role_derive.rs](examples/user_role_derive.rs) shows the optional `derive` feature for structured data.

### Advanced Examples

For larger flows, prefer the checked examples over copying README snippets. [examples/typed_environment.rs](examples/typed_environment.rs) demonstrates explicit type metadata and compile-time rule validation, while [examples/user_role_derive.rs](examples/user_role_derive.rs) demonstrates the optional `derive` feature for strongly typed Rust structs.

## WebAssembly

Cellang can be compiled to `wasm32-unknown-unknown` behind the optional `wasm` feature. The bindings in [src/wasm.rs](crates/cellang/src/wasm.rs) expose an `evaluateExpression` helper and a reusable `WasmRuntime` class. Build the WebAssembly artifact with:

```bash
cargo build -p cellang --features wasm --target wasm32-unknown-unknown
```

For projects that expect JavaScript glue code, run `wasm-pack build crates/cellang --features wasm --target web` to generate the `.wasm` binary plus the corresponding JS module. JavaScript callers can then evaluate expressions provided that the environment is a JSON-serializable object:

```javascript
import { evaluateExpression, WasmRuntime } from "cellang";

const result = await evaluateExpression("users.exists(u, u == name)", {
    users: ["alice", "bob"],
    name: "alice",
});

const runtime = new WasmRuntime({ greeting: "hello" });
const jsValue = runtime.evaluate("greeting.upperAscii() == 'HELLO'");
```

Both exports accept any value that `serde_wasm_bindgen` can convert (objects, arrays, scalars). Additional per-evaluation variables can be merged via `runtime.withVariables({...})`, which builds a scoped child runtime without mutating the original instance.