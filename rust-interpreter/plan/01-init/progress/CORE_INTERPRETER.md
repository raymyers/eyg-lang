# Core Interpreter Implementation Progress

**Milestone**: 3 - Core Interpreter
**Status**: Complete ✅
**Started**: 2026-02-22
**Completed**: 2026-02-22

## Goal

Port `state.gleam` — the stepper, `eval`, and `apply` functions — as the heart of the interpreter. Mirror the CPS structure exactly so the mapping to the Gleam source stays obvious.

## Tasks

### 1. Define `src/interpreter/value.rs` ✅
- [x] Define `Scope` type
- [x] Define `Value` enum with all variants
- [x] Define `Switch` enum with all variants
- [x] Add helper functions (unit, true, false, ok, error, etc.)

### 2. Define `src/interpreter/break_reason.rs` ✅
- [x] Define `BreakReason` enum with all error variants
- [x] Box large Value variants to reduce enum size

### 3. Define `src/interpreter/cast.rs` ✅
- [x] Implement `as_integer` helper
- [x] Implement `as_string` helper
- [x] Implement `as_binary` helper
- [x] Implement `as_list` helper
- [x] Implement `as_record` helper
- [x] Implement `as_tagged` helper

### 4. Define `src/interpreter/state.rs` ✅
- [x] Define `Control` enum
- [x] Define `Kontinue` enum
- [x] Define `Stack` enum
- [x] Define `Next` enum (with boxed Stack to reduce size)
- [x] Define `Env` struct
- [x] Define `Builtin` enum with type aliases
- [x] Define `StepReturn` type alias
- [x] Implement `step` function
- [x] Implement `eval` function (handles all IR node types)
- [x] Implement `apply` function
- [x] Implement `call` function (handles closures, partials, effects)
- [x] Implement `call_builtin` helper
- [x] Implement `perform` and `do_perform` functions
- [x] Implement `deep` function for effect handlers
- [x] Implement `move_frames` helper

### 5. Define `src/interpreter/expression.rs` ✅
- [x] Implement `execute` function
- [x] Implement `call` function
- [x] Implement `resume` function
- [x] Implement `new_env` function
- [x] Implement `eval_loop` function

## Implementation Notes

- Using `Rc<Value>` for shared ownership of values
- Using `Vec<(String, Rc<Value>)>` for Scope (can optimize to `im::Vector` later)
- Metadata type `m` is fixed to `()` for initial port
- CID stored as `String` (base32 multibase encoding)
- No async/Promise support (JavaScript-specific)
- Boxed large types to satisfy clippy warnings:
  - `Value` in `BreakReason` variants
  - `Debug` tuple for error information
  - `Stack` in `Next::Loop` variant
- Created type aliases for builtin function signatures to reduce complexity

## Verification

- ✅ `cargo check` passes
- ✅ `cargo clippy -- -D warnings` passes with no warnings
- ✅ `cargo test` passes (8 IR tests)
- ✅ `make check` passes

## Next Steps

Milestone 4 (Environment & Scope) is already partially implemented in state.rs.
Milestone 5 (Built-in Functions) needs to populate the builtins map.
Milestone 6 (Testing) needs evaluation test suite implementation.

