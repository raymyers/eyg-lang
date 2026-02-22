# Builtin Functions - Accept References

## Goal

Refactor builtin functions to accept `&Rc<Value>` instead of `Rc<Value>` to avoid
unnecessary reference count increments/decrements.

## Tasks

- [x] Update `BuiltinFn1..4` type aliases in `builtin.rs` to take `&Rc<Value>`
- [x] Update all builtin function signatures in `builtin.rs`
- [x] Update `call_builtin` in `state.rs` to pass references
- [x] Run `cargo test` to verify all tests pass
- [x] Run `cargo clippy` to verify warnings are resolved

## Completed

Changed `state.rs` type aliases from:
```rust
pub type BuiltinFn1 = fn(Rc<Value>, (), Env, Stack) -> StepReturn;
pub type BuiltinFn2 = fn(Rc<Value>, Rc<Value>, (), Env, Stack) -> StepReturn;
// ...
```

To:
```rust
pub type BuiltinFn1 = fn(&Rc<Value>, (), Env, Stack) -> StepReturn;
pub type BuiltinFn2 = fn(&Rc<Value>, &Rc<Value>, (), Env, Stack) -> StepReturn;
// ...
```

Updated `call_builtin` to pass references instead of cloned values.

Updated all 40+ builtin functions in `builtin.rs` to accept `&Rc<Value>` parameters.
Where cloning was necessary (e.g., passing to `state::call`), added explicit `.clone()`.

All 26 tests pass, clippy clean.

