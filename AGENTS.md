# EYG Lang — Agent Context

## Project Structure
- `packages/gleam_*` — Authoritative Gleam implementations (parser, analysis, interpreter)
- `rust-interpreter/` — Rust port as Cargo workspace
  - `crates/eyg-ir` — Shared IR types (Node, Expr, dag-json)
  - Root crate — CLI binary (`eyg-run`) + interpreter lib

## Build & Test
```sh
cd rust-interpreter
make check   # runs: cargo test --workspace && cargo clippy --workspace -- -D warnings
make test    # cargo test --workspace
make lint    # cargo clippy --workspace -- -D warnings
```

## Key Notes
- Rust edition is **2024** — `gen` is a reserved keyword, use `generalize` instead
- 29 tests total across 4 test crates (builtin_tests, cli_tests, evaluation_suite, ir_suite)
- CPS interpreter with persistent environments (im::Vector)
- Shared spec suites live in `spec/evaluation/` and `spec/ir_suite.json`
