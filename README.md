# CEL language interpreter for Rust

This is a rust implementation of the [CEL](https://cel.dev/) language.

NOTE: While this project is still in development, it is already being used in production for [BountyHub](https://bountyhub.org).
If you find any issues, please report them.

## Motivation

Motivation behind this project is to provide a way to evaluate CEL expressions in Rust, while allowing
easier way to provide custom functions. This project is built for [BountyHub](https://bountyhub.org) project,
but is open-source and can be used by anyone.

There is a great rust project called [CEL Interpreter](https://crates.io/crates/cel-interpreter) which I initially used.

However, while the project is great, it does not provide an easy way to add custom functions to the interpreter (in my opinion).
It has a great API to provide a simple functions, but as soon as I needed to check the AST, it proved to be difficult to do so.

I also needed to inspect the AST of the CEL expressions in order to validate the expression. Most of the fields were private, so
the references field was the only one that was accessible.

With that in mind, I decided to create this project, and expose the all components of the interpreter, so that it can be used
in a more flexible way. Therefore, you have `eval` that will evaluate the program, `eval_ast` that will evaluate the AST which can
be a subset of the program, etc.

## Repository structure

This repository is a rust workspace, with the following crates:

- `cellang`: The main library crate located at [lib](./crates/lib)
- `cellang-cli`: A CLI tool to evaluate CEL expressions located at [cli](./crates/cli)
