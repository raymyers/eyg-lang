# Milestone 9: CLI Integration Progress

## Completed

### Args refactoring
- Replaced `--parse-ir <FILE>` / `--parse-exec <FILE>` with unified design:
  - Positional `<FILE>` (required)
  - `--in ir|eyg` (default: `ir`)
  - `--dump-ir` flag (replaces `--parse-ir`)
  - `--type-check` flag (new)
  - `--effects` stays unchanged
- Uses `clap::ValueEnum` for `InputFormat` enum

### Type-check integration
- `--type-check` runs `eyg_analysis::infer::check()` with `Context::unpure()`
- On success: prints rendered type to stdout, exit 0
- On errors: prints each `Type error: ...` to stderr, still prints type to stdout, exit 1
- Parse errors abort before type-checking

### Tests (7 new type-check tests, 22 CLI tests total)
- `test_type_check_well_typed_eyg` — `5` → `Integer`
- `test_type_check_well_typed_json` — dag-json integer → `Integer`
- `test_type_check_string` — `"hello"` → `String`
- `test_type_check_function` — identity fn has `->` in output
- `test_type_check_ill_typed` — missing variable → error
- `test_type_check_parse_error` — parse error propagates
- `test_type_check_vacant` — vacant → `code incomplete` error

### README updated with new CLI docs

## Total: 178 tests, clippy clean
