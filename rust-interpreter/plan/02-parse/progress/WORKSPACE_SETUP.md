# Milestone 1: Workspace & Crate Setup

## Status: COMPLETE

## What was done
- Created `crates/eyg-ir` with `ast.rs` and `dag_json.rs` extracted from `src/ir/`
- Created `crates/eyg-parser` skeleton (empty lib.rs, depends on eyg-ir)
- Root `Cargo.toml` now has `[workspace]` with both crates as members and path deps
- `src/ir/mod.rs` re-exports from `eyg_ir` — existing `crate::ir::ast::*` paths still work
- Old `src/ir/ast.rs` and `src/ir/dag_json.rs` removed (now in eyg-ir crate)
- All 26 tests pass, clippy clean
