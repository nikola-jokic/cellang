# CEL language interpreter for Rust

This is a rust implementation of the [CEL](https://cel.dev/) language.

This project is built for [BountyHub](https://bountyhub.org) platform, but is open-source and can be used by anyone.

If you find any issues, please report them.

## Repository structure

This repository is a rust workspace, with the following crates:

- `cellang`: The main library crate located at [lib](./crates/lib)
- `cellang-cli`: A CLI tool to evaluate CEL expressions located at [cli](./crates/cli)

## License

This project is licensed under the [MIT license](./LICENSE).

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this project by you, as defined in the MIT license, shall be licensed as above, without any additional terms or conditions.

## Special thanks

Special thanks to [Jon Gjengset](https://github.com/jonhoo) for his amazing [video](https://youtu.be/mNOLaw-_Buc) which helped me get started with this project.
