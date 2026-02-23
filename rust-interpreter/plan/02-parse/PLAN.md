# Rust Parser Implementation Plan

## Overview

Port `packages/gleam_parser` to Rust as a separate crate within a Cargo
workspace, sharing IR types with the existing interpreter.  The parser is a
hand-written recursive-descent parser fed by a byte-level lexer, producing the
same IR node types already defined in `src/ir/ast.rs`.

The CLI (`eyg-run`) gains two new flags:
- `--parse-ir <file.eyg>` — parse source to IR, emit dag-json to stdout
- `--parse-exec <file.eyg>` — parse source, then execute (same as current JSON path)

Additionally, a built-in `Log` effect handler is wired as a default extrinsic
so that `perform Log` programs work out of the box (prints the lifted value to
stderr, resumes with unit `{}`).

Reference sources:

| Gleam source | Role |
|---|---|
| `packages/gleam_parser/src/eyg/parser.gleam` | Public API (`from_string`, `all_from_string`, `block_from_string`) |
| `packages/gleam_parser/src/eyg/parser/token.gleam` | 27 token variants + whitespace/comment filtering |
| `packages/gleam_parser/src/eyg/parser/lexer.gleam` | Hand-written byte-level scanner (313 lines) |
| `packages/gleam_parser/src/eyg/parser/parser.gleam` | Recursive-descent parser (543 lines, 17 functions) |
| `packages/gleam_parser/test/eyg/parser/lexer_test.gleam` | 8 lexer test functions |
| `packages/gleam_parser/test/eyg/parser_test.gleam` | 16 parser test functions (735 lines) |

### Key Design Constraints

- **Auto-currying**: Multi-param lambdas `(x, y) -> { body }` desugar to
  nested `Lambda("x", Lambda("y", body))`.  Multi-arg calls `f(x, y)` desugar
  to nested `Apply(Apply(f, x), y)`.
- **Synthetic `$` variable**: Destructuring patterns (`let {x: a} = r`) use a
  hidden `$` binding with `Select` projections.
- **No infix operators**: Grammar is unambiguous without precedence rules.
- **Byte-offset spans**: Every IR node carries `Span = (start, end)` byte
  offsets for source mapping.  The Rust parser uses `()` metadata (matching the
  interpreter) but may optionally preserve spans.
- **Postfix chaining**: `f(x).y(z)` is parsed via a loop in `after_expression`.
- **Block mode**: `block_from_string` allows `let` without a continuation body
  (yields `Vacant`), used for editor/REPL integration.

---

## Milestone 1: Workspace & Crate Setup ✅

Progress: [progress/WORKSPACE_SETUP.md](progress/WORKSPACE_SETUP.md)

* [x] Convert `rust-interpreter/` to a Cargo workspace with members:
  - `crates/eyg-ir` — shared IR types (extracted from current `src/ir/`)
  - `crates/eyg-parser` — new parser crate
  - root crate — CLI binary (`eyg-run`) + interpreter lib
* [x] Move `src/ir/ast.rs`, `src/ir/dag_json.rs`, `src/ir/mod.rs` into
      `crates/eyg-ir/src/` and update `pub use` paths
* [x] Root `Cargo.toml` gains `[workspace]` section and `eyg-ir` + `eyg-parser`
      as path dependencies
* [x] `crates/eyg-parser/Cargo.toml` depends on `eyg-ir`
* [x] Root crate depends on `eyg-ir` (for `Node`, `Expr`) and `eyg-parser`
* [x] Verify `make check` still passes — all 26 existing tests green, clippy clean
* [x] Update import paths in `src/main.rs`, `src/interpreter/`, and `tests/`

---

## Milestone 2: Token Types ✅

Port `packages/gleam_parser/src/eyg/parser/token.gleam` (27 variants).

* [x] Create `crates/eyg-parser/src/token.rs` with a `Token` enum
      (follows Gleam source: `Whitespace(String)`, `Integer(String)`, `Minus`, `Deep`, `Bar`, etc.)
* [x] Implement `drop_whitespace` — filter `Whitespace` tokens
* [x] Implement `drop_comments` — filter `Comment` tokens
* [x] Implement `Display` for `Token` (for error messages)
* [x] Unit tests for `drop_whitespace`, `drop_comments`, and `Display`
* [x] Updated Makefile to use `--workspace` for test and clippy

---

## Milestone 3: Lexer ✅

* [x] `crates/eyg-parser/src/lexer.rs` — `pub fn lex(source: &str) -> Vec<(Token, usize)>`
* [x] All single/two-char tokens, comments, whitespace, strings (with escapes), integers
* [x] Identifiers: lowercase→`Name` (with keyword boundary guard), uppercase→`Uppername`
* [x] `UnexpectedGrapheme` for unrecognized bytes
* [x] 13 unit tests mirroring all 8 Gleam lexer tests + extras

---

## Milestones 4-6: Parser, Compound Expressions & Public API ✅

All implemented together in `crates/eyg-parser/src/parser.rs` + `lib.rs`.

* [x] `ParseError::{UnexpectedEnd, UnexpectedToken}`, helpers `pop`/`fail`
* [x] Atoms: integers (incl. negative), strings, variables, tags, builtins, perform, handle, references
* [x] Lambdas: single, multi-param (auto-currying), destructuring
* [x] Application: single, multi-arg, chained, nested; `after_expression` loop
* [x] Let bindings: simple, nested, destructuring (with shorthand), block mode
* [x] Records: empty, fields, shorthand, spread (overwrite), identity spread
* [x] Lists: empty, elements, spread
* [x] Match: empty, with subject, multi-branch, open match (pipe fallback)
* [x] Field access: `a.foo`, `b(x).foo`, `a.foo(2)`
* [x] Public API: `from_string`, `block_from_string`
* [x] 46 unit tests covering all expression forms, block mode, and errors

---

## Milestone 7: CLI Integration ✅

Progress: [progress/CLI_INTEGRATION.md](progress/CLI_INTEGRATION.md)

* [x] Add `--parse-ir <file>` flag to `src/main.rs`:
  - Read source file as UTF-8 string
  - Call `eyg_parser::from_string(source)`
  - Serialize resulting `Node` as dag-json to stdout
  - On parse error: print error with byte offset to stderr, exit 1
* [x] Add `--parse-exec <file>` flag:
  - Parse source → `Node`
  - Execute `Node` through the interpreter (same path as JSON execution)
  - On parse error: stderr + exit 1
* [x] Add built-in `Log` extrinsic effect handler:
  - When an `UnhandledEffect("Log", value)` bubbles to the stack base,
    print the lifted value to stderr (matching convention: Log goes to stderr)
  - Resume with unit (`Value::Record(empty)`)
  - Wired in the CLI `run()` function as a loop after explicit handlers
* [x] Verify `eyg-run --parse-exec hello.eyg` with a file containing
      `perform Log("Hello, World!")` prints to stderr and exits 0
* [x] Verify `eyg-run --parse-ir hello.eyg` outputs the expected dag-json
* [x] Added dag-json `serialize_with` for Binary, Reference, Release fields
* [x] 7 new CLI integration tests (15 total CLI tests, 95 total)

---

## Milestone 8: End-to-End & Regression Tests

* [ ] CLI integration tests for `--parse-ir`:
  - Parse a simple expression, assert stdout is valid dag-json
  - Parse error input, assert exit 1 with error on stderr
* [ ] CLI integration tests for `--parse-exec`:
  - Execute a parsed program, assert correct stdout
  - Test with effect-producing programs (Log)
* [ ] CLI integration tests for default Log handler:
  - `perform Log("hi")` prints `"hi"` to stderr, exits 0
  - Chained: `let x = perform Log("a") perform Log("b")` logs both
* [ ] Verify existing 26 interpreter tests still pass unchanged
* [ ] Port representative parser tests from `packages/gleam_parser/test/`:
  - All 16 parser test cases as data-driven fixtures
  - All 8 lexer test cases
* [ ] Edge cases: empty input, only whitespace, only comments,
      deeply nested expressions, large integers