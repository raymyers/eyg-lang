# Milestones 6-8: Inference Engine (All Forms + Builtins)

## Status: Complete

## Scope
Ported full `do_infer` from `contextual.gleam` for ALL IR forms + builtin type table.
Covers Milestones 6, 7, and 8 in a single implementation pass.

## Key Design Decisions
- `Vec<NodeInfo>` instead of annotated tree (pre-order DFS, self then children)
- `Context` struct with `pure()`/`unpure()` constructors
- `Env` as `Vec<(String, Poly)>` (clone on extension for immutability)
- `infer()` convenience function for tests (matches Gleam's `j.infer`)

## Bug Fix: Unify Level Handling
**Critical fix in `unify.rs`**: The `occurs_and_levels` function must use the
**variable's own level** (from `Binding::Unbound(var_level)`), not the unification
level parameter. The Gleam code achieves this via pattern match shadowing:
```gleam
t.Var(i), Ok(binding.Unbound(level)), other, _  // <-- shadows `level` param
```
Without this fix, type variable levels don't propagate correctly through
unification, causing wrong effect annotations in Apply nodes.

## Parser Limitation
The Rust parser doesn't support `.field` after record/empty literals (e.g.
`{name: 5}.name`). Tests use `let` bindings to work around this.

## Test Coverage
- 73 tests in eyg-analysis (up from 42), 171 total workspace
- Tests mirror `contextual_test.gleam`: variable, literal, function, let,
  polymorphism, list, record, select, tag, builtin, perform, effects

## Completed Steps
- [x] Implement infer.rs: Context, NodeInfo, Analysis, check, type_of, do_infer
- [x] Implement helpers: open_effect, open, close, close_eff, eff_tail, ftv, prim, q
- [x] All 21 IR forms: Variable, Lambda, Apply, Let, Vacant, Integer, Binary, String,
      Tail, Cons, Empty, Extend, Overwrite, Select, Tag, Case, NoCases,
      Perform, Handle, Builtin, Reference, Release
- [x] builtins.rs: full builtin type table (equal, fix, never, int_*, string_*, binary_*, list_*)
- [x] Fix unify var_level bug
- [x] 15 inference tests + all existing tests pass
- [x] `make check` clean (tests + clippy)
