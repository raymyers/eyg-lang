# Milestone 10: End-to-End & Regression Tests

## Status: Complete

## What was done

### Data-driven test fixture
- Created `testdata/type_check_cases.json` with 35 test cases
- Format: `{ name, source (or source_ir), expected_type, expected_errors }`
- Supports both EYG source (parsed via `eyg_parser::from_string`) and IR JSON (deserialized via `serde_json`)
- `expected_type: null` means "don't check type" (used when type contains implementation-dependent variable numbers)
- `expected_errors` uses substring matching against `debug::render_reason` output

### Test runner
- Created `tests/type_check_suite.rs` — reads JSON, parses, runs `infer::check`, validates type and errors
- Reports all failures at once (not just first)

### Cases ported from contextual_test.gleam (35 total)
- Variables: missing variable, missing variable in select
- Literals: integer, string
- Functions: identity, applied identity, multi-arg (x selected), multi-arg (z selected)
- Let: basic, shadowing, polymorphism
- Lists: empty, singleton, polymorphism
- Records: empty, single field, two fields, nested, destructure function
- Select: field access, missing variable, missing row
- Tags: constructor, applied, match with two branches
- Builtins: int_add, int_add applied, missing, int_to_string, equal, list_fold
- Effects: only_unknown_effect
- Edge cases: vacant/todo (via IR JSON), deep let polymorphism (4 uses of id), recursive occurs check
- Composition: pure function composition

### Variable numbering note
Some expected types contain implementation-specific variable IDs (e.g., `List(15)` for deep_let_polymorphism, `3` for select_missing_row). These are deterministic given fresh bindings from `Context::pure()` but would change if internals change. Cases where the exact number matters use the verified value; others use `null`.

### Test counts
- 179 tests total (73 eyg-analysis + 62 parser + 7 builtins + 22 CLI + 3 evaluation + 8 IR + 1 lex + 2 parse + 1 type_check_suite)
- The type_check_suite test runs 35 cases internally
- `make check` passes (all tests + clippy clean)
