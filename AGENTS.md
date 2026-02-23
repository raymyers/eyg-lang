# EYG Lang — Agent Context

## Project Structure
- `packages/gleam_*` — Authoritative Gleam implementations (parser, analysis, interpreter)
- `rust-interpreter/` — Rust port as Cargo workspace
  - `crates/eyg-ir` — Shared IR types (Node, Expr, dag-json)
  - `crates/eyg-parser` — Lexer + recursive-descent parser
  - `crates/eyg-analysis` — Type checker (in progress, Milestones 1-4 done)
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
- Plan docs live in `rust-interpreter/plan/03-analysis/` (current phase)
- Progress tracked in `rust-interpreter/plan/03-analysis/progress/CRATE_SETUP.md`
- 142 tests total as of Milestone 4 completion
- Type checker uses Algorithm J with levels (Oleg Kiselyov) + effect opening/closing
