# CEL language interpreter for Rust

This is a rust implementation of the [CEL](https://cel.dev/) language.

This project is built for [BountyHub](https://bountyhub.org) platform, but is open-source and can be used by anyone.

If you find any issues, please report them.

## Getting started

```bash
git clone https://github.com/nikola-jokic/cellang.git
cd cellang
cargo build
```

### Running the test suite

The workspace is fully covered by automated checks. Locally you can mirror CI with:

```bash
cargo test --locked --all-features --all-targets
cargo test --locked --all-features --doc
```

Examples under `crates/cellang/examples` can be exercised from the workspace root via:

```bash
for example in crates/cellang/examples/*.rs; do \
 name=$(basename "${example%.rs}"); \
 cargo run --locked --all-features -p cellang --example "$name"; \
done
```

or run directly with `cargo run -p cellang --example <name>` for interactive experimentation.

### Example overview

| Example | Highlights |
| --- | --- |
| [`simple`](./crates/cellang/examples/simple.rs) | Basic expression evaluation, child runtimes, and scalar values. |
| [`create_function`](./crates/cellang/examples/create_function.rs) | Registering function declarations plus native Rust implementations. |
| [`concurrency`](./crates/cellang/examples/concurrency.rs) | Sharing a runtime builder across threads for parallel evaluation. |
| [`user_role_derive`](./crates/cellang/examples/user_role_derive.rs) | Using the `derive` feature to expose Rust structs and methods to CEL. |
| [`comprehensions`](./crates/cellang/examples/comprehensions.rs) | Practical use of CEL macros like `exists`, `filter`, `map`, and `all`. |
| [`env_snapshot`](./crates/cellang/examples/env_snapshot.rs) | Building, serializing, and rehydrating a reusable environment snapshot. |
| [`tree_inspection`](./crates/cellang/examples/tree_inspection.rs) | Inspecting parsed syntax trees for IDE/LSP tooling, linters, and code analysis. |

## CLI

The `cellang-cli` crate exposes a developer-friendly command line interface for inspecting CEL programs.

```bash
cargo run -p cellang-cli -- lex expr --format json "a + size(b)"
cargo run -p cellang-cli -- parse expr --format debug "a.b.c"
cargo run -p cellang-cli -- eval expr --expr "users[0].has_role(role)" --env-path ./env.json
```

Subcommands:

- `lex` – emit tokens for a file or inline expression (formatted as pretty JSON or debug output).
- `parse` – dump the syntax tree from parsed expressions.
  - Rowan-based concrete syntax tree with full source fidelity (default)
- `eval` – evaluate an expression within a runtime populated from a JSON environment file.

## Parser Architecture

Cellang uses a Rowan-based parser for robust syntax tree construction with error recovery:

1. **Lexer** (`lexer.rs`) - Tokenizes source text
2. **Rowan Parser** (`parser::parse`) - Builds lossless concrete syntax tree (CST)
3. **HIR Lowering** (`parser::lower`) - Converts CST to high-level intermediate representation
4. **Type Checking** (`parser::type_check`) - Validates types and builds typed expression graph
5. **Interpreter** (`parser::eval`) - Evaluates typed expressions

Use only the canonical parser facade paths (`cellang::parser::*`) for parse/lower/type-check/eval pipeline access.

The Rowan CST preserves all source information (whitespace, comments, error tokens) making it ideal for IDE/LSP tooling. The HIR provides a clean semantic boundary for runtime evaluation.

## Repository structure

This repository is a rust workspace, with the following crates:

- `cellang`: The main library crate located at [lib](./crates/cellang)
- `cellang-cli`: A CLI tool to evaluate CEL expressions located at [cli](./crates/cellang-cli)

## License

This project is licensed under the [MIT license](./LICENSE).

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this project by you, as defined in the MIT license, shall be licensed as above, without any additional terms or conditions.

## Special thanks

Special thanks to [Jon Gjengset](https://github.com/jonhoo) for his amazing [video](https://youtu.be/mNOLaw-_Buc) which helped me get started with this project.
