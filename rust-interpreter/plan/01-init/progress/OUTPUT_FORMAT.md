# Output Format Compatibility

## Goal
Match Go (mulch) CLI `Debug()` output format for all value types.

## Reference: Go Debug() formats

| Value Type | Go format | Rust (before) |
|------------|-----------|---------------|
| String | `"hello"` | `"hello"` ✅ |
| Integer | `42` | `42` ✅ |
| Tagged | `Ok(42)` | `Ok(42)` ✅ |
| List | `[1, 2, 3]` | `[1, 2, 3]` ✅ |
| Record | `{name: "Alice"}` | `{name: "Alice"}` ✅ |
| Closure | `(x) -> { ... }` | `<closure x>` ❌ |
| Binary | `<<72, 101>>` (signed i8) | `Binary(N bytes)` ❌ |
| Partial Select | `.label` | `<partial ...>` ❌ |
| Partial Overwrite | `:=label` | `<partial ...>` ❌ |
| Partial Tag | `label` or `label(arg)` | `<partial ...>` ❌ |
| Partial Case | `case label` | `<partial ...>` ❌ |
| Partial NoCases | `nocases` | `<partial ...>` ❌ |
| Partial Perform | `^label` | `<partial ...>` ❌ |
| Partial Handle | `deep label` / `deep label(handler)` | `<partial ...>` ❌ |
| Partial Resume | `resume` | `<partial ...>` ❌ |
| Partial Builtin | `Defunc name (arg1, ..)` | `<partial ...>` ❌ |
| Partial Cons | partial cons display | `<partial ...>` ❌ |

## Status
- [x] Studied Go reference formats
- [x] Update Rust Display impl
- [x] Tests pass (26 tests, clippy clean)
