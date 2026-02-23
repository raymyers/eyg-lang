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
- Progress tracked in `rust-interpreter/plan/03-analysis/progress/`
- 171 tests total as of Milestones 6-8 completion
- Type checker uses Algorithm J with levels (Oleg Kiselyov) + effect opening/closing
- **Critical**: In unify, `occurs_and_levels` must use the variable's own level (from `Binding::Unbound`), NOT the unification level parameter. The Gleam code achieves this via pattern-match shadowing.
- Rust parser doesn't support `.field` after record/empty literals — use `let` bindings in tests
