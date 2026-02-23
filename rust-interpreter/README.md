# EYG Rust Interpreter

A Rust port of the EYG interpreter (`packages/gleam_interpreter`). Reads EYG programs serialised as dag-json, executes them using a continuation-passing-style (CPS) evaluator, and prints the result.

## Build

```sh
cargo build --release
```

## Usage

```sh
# Run a program
eyg-run program.json

# Run with effect handlers
eyg-run program.json --effects handlers.json
```

The input file is an EYG IR tree encoded as [dag-json](https://ipld.io/specs/codecs/dag-json/). On success the result value is printed to stdout; on error the break reason goes to stderr with exit code 1.

## Development

```sh
make check   # cargo test + clippy
make test    # cargo test
make lint    # cargo clippy -- -D warnings
```

Tests run the shared spec suites from `spec/evaluation/` (core, builtins, effects) and `spec/ir_suite.json`.
