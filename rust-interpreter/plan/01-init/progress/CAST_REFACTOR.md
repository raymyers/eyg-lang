# Cast Functions Refactor - Return References

## Goal
Refactor cast functions to return references instead of cloning data, eliminating unnecessary allocations.

## Current State
Cast functions clone inner data:
- `as_string` returns `Result<String, BreakReason>` (clones String)
- `as_binary` returns `Result<Vec<u8>, BreakReason>` (clones Vec)
- `as_list` returns `Result<Vec<Rc<Value>>, BreakReason>` (clones Vec)
- `as_record` returns `Result<im::HashMap<String, Rc<Value>>, BreakReason>` (clones HashMap)
- `as_tagged` returns `Result<(String, Rc<Value>), BreakReason>` (clones String)

## Target State
Cast functions return references:
- `as_string` returns `Result<&str, BreakReason>`
- `as_binary` returns `Result<&[u8], BreakReason>`
- `as_list` returns `Result<&Vec<Rc<Value>>, BreakReason>`
- `as_record` returns `Result<&im::HashMap<String, Rc<Value>>, BreakReason>`
- `as_tagged` returns `Result<(&str, &Rc<Value>), BreakReason>`

## Impact Analysis

### Files to modify:
1. `src/interpreter/cast.rs` - Change return types
2. `src/interpreter/builtin.rs` - Update ~30 call sites
3. `src/interpreter/state.rs` - Update ~5 call sites

### Usage patterns in builtin.rs:
Most usages need the data for operations that require owned values:
- String operations: `s.to_uppercase()`, `s.replace()`, `format!("{}{}", left, right)`
- Binary operations: `String::from_utf8(bytes)`, iterating over bytes
- List operations: slicing `elements[1..]`, iterating

Some usages can benefit from references:
- Read-only checks: `s.starts_with()`, `s.ends_with()`, `s.is_empty()`
- Length operations: `s.graphemes(true).count()`
- Field lookups: `fields.get(label)`

### Usage patterns in state.rs:
Most need to mutate or extend the data:
- `Cons`: extends list with `new_list.extend(elements)`
- `Extend/Overwrite`: mutates record with `fields.insert()`
- `Select`: reads field with `fields.get()` (can use reference)
- `Match`: extracts label and inner value

## Implementation Strategy

1. Update cast.rs return types
2. Update builtin.rs call sites - add `.to_owned()` or `.to_string()` where needed
3. Update state.rs call sites - clone where mutation is needed
4. Run tests to verify correctness
5. Run clippy to check for any issues

## Progress

- [x] Update cast.rs function signatures
- [x] Update builtin.rs call sites
- [x] Update state.rs call sites
- [x] Run `cargo test` - verify all tests pass (26 tests)
- [x] Run `cargo clippy` - verify no new warnings
- [x] Update PLAN.md to mark task complete

## Implementation Details

### Changes to cast.rs
All cast functions now return references instead of cloning:
- `as_string`: `Result<&str, BreakReason>` (was `Result<String, BreakReason>`)
- `as_binary`: `Result<&[u8], BreakReason>` (was `Result<Vec<u8>, BreakReason>`)
- `as_list`: `Result<&Vec<Rc<Value>>, BreakReason>` (was `Result<Vec<Rc<Value>>, BreakReason>`)
- `as_record`: `Result<&im::HashMap<String, Rc<Value>>, BreakReason>` (was `Result<im::HashMap<String, Rc<Value>>, BreakReason>`)
- `as_tagged`: `Result<(&str, &Rc<Value>), BreakReason>` (was `Result<(String, Rc<Value>), BreakReason>`)

### Changes to builtin.rs
Updated call sites to work with references:
- String operations: Most already work with `&str` (e.g., `parse()`, `starts_with()`, `ends_with()`)
- `string_to_binary`: Changed from `s.into_bytes()` to `s.as_bytes().to_vec()`
- `string_from_binary`: Changed from `String::from_utf8(bytes)` to `String::from_utf8(bytes.to_vec())`
- `binary_fold`: Changed from `byte as i64` to `i64::from(byte)` for lossless cast
- List/record operations: Already worked with references via iteration

### Changes to state.rs
Updated to clone only when mutation is needed:
- `Cons`: Changed `new_list.extend(elements)` to `new_list.extend(elements.iter().cloned())`
- `Extend`: Clone fields before inserting: `let mut new_fields = fields.clone()`
- `Overwrite`: Clone fields before inserting: `let mut new_fields = fields.clone()`
- `Select`: No changes needed (read-only access)
- `Match`: Changed `&l == label` to `l == label` and `inner` to `inner.clone()`

## Impact
This refactor eliminates unnecessary deep clones of strings, byte arrays, lists, and records on every type check. The performance improvement is most significant for:
- Large strings in string operations
- Large binary data in binary operations
- Large lists and records in structural operations

All 26 tests pass with no clippy warnings.

