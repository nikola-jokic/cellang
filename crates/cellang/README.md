# Cellang

Cellang is an implementation of the [CEL](https://cel.dev/) language interpreter in Rust.

## Motivation

Motivation behind this project is to provide a way to evaluate CEL expressions in Rust, while allowing
easier way to provide custom functions. This project is built for [BountyHub](https://bountyhub.org) project,
but is open-source and can be used by anyone.

There is a great rust project called [CEL Interpreter](https://crates.io/crates/cel-interpreter) which I initially used.

However, I found that the project is not flexible enough for my needs. I needed to be able to:
- Inspect the AST of the program during validations
- Add slightly more complex functions on types.

Therefore, the library exposes lower-level primitives that would allow you to do that.

## Getting started

This library aims to be ergonomic without hiding the lower-level building blocks that make CEL powerful. The typical workflow is:

1. Build a `Runtime` with variables, declared types, and native functions.
2. Evaluate expressions against that runtime (or child runtimes that inherit the same environment).

```rust
use cellang::{Runtime, Value};

fn main() -> miette::Result<()> {
    let mut builder = Runtime::builder();
    builder.set_variable("greeting", "Hello");
    builder.set_variable("name", "World");

    builder.register_function("shout", |text: String| text.to_uppercase())?;

    let runtime = builder.build();
    let value = runtime.eval("shout(greeting + ", " + name)")?;
    assert_eq!(value, Value::String("HELLO, WORLD".into()));
    Ok(())
}
```

### Advanced example

The [user_role](./examples/user_role.rs) example demonstrates how to register structured data, declare CEL metadata, and surface strongly typed native functions:

```rust
use cellang::runtime::RuntimeBuilder;
use cellang::Runtime;
use cellang::types::{FieldDecl, FunctionDecl, IdentDecl, NamedType, OverloadDecl, StructType, Type};
use cellang::value::{IntoValue, StructValue, TryFromValue, Value, ValueError};

const USER_TYPE: &str = "example.User";
const EXPRESSION: &str = "users[0].has_role(role)";

fn main() -> miette::Result<()> {
    let runtime = build_runtime()?;

    let mut scoped = runtime.child_builder();
    scoped.set_variable("role", "admin");
    let scoped = scoped.build();

    let result = scoped.eval(EXPRESSION)?;
    assert_eq!(result, Value::Bool(true));
    println!("{} => {}", EXPRESSION, result);
    Ok(())
}

fn install_user_schema(builder: &mut RuntimeBuilder) -> miette::Result<()> {
    let mut user = StructType::new(USER_TYPE);
    user.add_field("name", FieldDecl::new(Type::String))?;
    user.add_field("roles", FieldDecl::new(Type::list(Type::String)))?;
    builder.add_type(NamedType::Struct(user))?;
    builder.add_ident(IdentDecl::new("users", Type::list(Type::struct_type(USER_TYPE))))?;

    let mut decl = FunctionDecl::new("has_role");
    decl.add_overload(
        OverloadDecl::new(
            "user_has_role_string",
            vec![Type::struct_type(USER_TYPE), Type::String],
            Type::Bool,
        )
        .with_receiver(Type::struct_type(USER_TYPE)),
    )?;
    builder.add_function_decl(decl)?;
    Ok(())
}

#[derive(Clone)]
struct User {
    name: String,
    roles: Vec<String>,
}

impl IntoValue for User {
    fn into_value(self) -> Value {
        let mut value = StructValue::new(USER_TYPE);
        value.set_field("name", self.name);
        value.set_field("roles", self.roles);
        Value::Struct(value)
    }
}

impl TryFromValue for User {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        let Value::Struct(strct) = value else {
            return Err(ValueError::Message("expected struct".into()));
        };
        Ok(Self {
            name: String::try_from_value(strct.get("name").unwrap())?,
            roles: Vec::<String>::try_from_value(strct.get("roles").unwrap())?,
        })
    }
}

fn has_role(user: User, role: String) -> bool {
    user.roles.iter().any(|current| current == &role)
}

fn build_runtime() -> miette::Result<cellang::Runtime> {
    let mut builder = Runtime::builder();
    install_user_schema(&mut builder)?;
    builder.register_function("has_role", has_role)?;
    builder.set_variable("users", vec![
        User {
            name: "Alice".into(),
            roles: vec!["admin".into()],
        },
        User {
            name: "Bob".into(),
            roles: vec!["user".into()],
        },
    ]);
    Ok(builder.build())
}
```

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