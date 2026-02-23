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

## Milestone 3: Lexer

Port `packages/gleam_parser/src/eyg/parser/lexer.gleam` (313 lines,
hand-written byte-level scanner).

* [ ] Create `crates/eyg-parser/src/lexer.rs` with `pub fn lex(source: &str) -> Vec<(Token, usize)>`
      where `usize` is the byte offset
* [ ] Scan single-char tokens: `(`, `)`, `{`, `}`, `[`, `]`, `=`, `,`, `:`,
      `.`, `|`, `!`, `#`, `@`
* [ ] Scan two-char tokens: `->` (RightArrow), `..` (DotDot)
* [ ] Scan line comments: `//` through end-of-line → `Comment(String)`
* [ ] Scan whitespace: spaces → `Space`, `\n`/`\r\n` → `NewLine`
* [ ] Scan integers: digit sequences, optionally preceded by `-`
      (negative integer as single token, matching Gleam lexer)
* [ ] Scan strings: `"..."` with escape sequences (`\"`, `\\`, `\n`),
      produce `UnterminatedString` on EOF
* [ ] Scan identifiers: lowercase-start → `Name` or keyword lookup
      (`let` → `Let`, `match` → `Match`, `perform` → `Perform`,
       `handle` → `Handle`)
* [ ] Scan upper identifiers: uppercase-start → `UpperName` (tags)
* [ ] Produce `UnexpectedGrapheme(ch)` for unrecognized bytes
* [ ] Data-driven lexer tests in `testdata/lexer_cases.json`:
  - Empty input
  - Single integer, negative integer
  - String with escapes
  - Identifiers and keywords
  - Mixed token sequences
  - Comment handling
  - Error tokens (unexpected grapheme, unterminated string)

---

## Milestone 4: Parser — Atoms & Simple Expressions

Port the atomic expression parsing from `parser.gleam` — the `expression`
function entry point and simple forms that don't recurse.

* [ ] Create `crates/eyg-parser/src/parser.rs` with error types:
  - `ParseError::UnexpectedEnd`
  - `ParseError::UnexpectedToken(Token, usize)`
* [ ] Implement token-stream helpers: `pop` (take next token), `peek`,
      `expect` (assert and consume a specific token)
* [ ] Parse integer literals: `Integer(i64)` token → `Expr::Integer`
* [ ] Parse string literals: `String(s)` token → `Expr::String`
* [ ] Parse variables: `Name(s)` token → `Expr::Variable`
* [ ] Parse tags: `UpperName(s)` token → `Expr::Tag`
* [ ] Parse builtins: `Bang` + `Name(s)` → `Expr::Builtin`
* [ ] Parse perform: `Perform` + `UpperName(s)` → `Expr::Perform`
* [ ] Parse handle: `Handle` + `UpperName(s)` → `Expr::Handle`
* [ ] Parse CID references: `Hash` + `Name(cid)` → `Expr::Reference`
* [ ] Parse named references: `At` + `Name(pkg)` → `Expr::Release`
      (with release=0 and a vacant CID, matching Gleam parser)
* [ ] Tests for each atom type (integers, strings, variables, tags,
      builtins, perform, handle, references)

---

## Milestone 5: Parser — Compound Expressions

Port the compound expression forms: lambdas, application, let, records,
lists, match.

### 5a: Lambdas & Application

* [ ] Parse single-param lambda: `(x) -> { body }` → `Expr::Lambda`
* [ ] Parse multi-param lambda: `(x, y) -> { body }` → nested
      `Lambda("x", Lambda("y", body))` (auto-currying)
* [ ] Parse destructuring lambda: `({x: a}) -> { body }` → desugar to
      `Lambda("$", Let("a", Apply(Select("x"), Var("$")), body))`
* [ ] Parse function application: `f(x)` → `Expr::Apply`
* [ ] Parse multi-arg application: `f(x, y)` → `Apply(Apply(f, x), y)`
* [ ] Parse chained application: `f(x)(y)` → `Apply(Apply(f, x), y)`
* [ ] Parse field access: `a.foo` → `Apply(Select("foo"), a)`
* [ ] Implement `after_expression` loop for postfix `.field` and `(args)` chaining
* [ ] Tests: single lambda, multi-param, destructuring, application,
      multi-arg, chaining, field access

### 5b: Let Bindings

* [ ] Parse simple let: `let x = v body` → `Expr::Let`
* [ ] Parse destructuring let: `let {x: a, y} = r body` → desugar to
      nested `Let("$", r, Let("a", Select("x")($), Let("y", Select("y")($), body)))`
* [ ] Parse let-in-block mode: `let x = v` without body → body is `Vacant`
* [ ] Tests: simple let, shadowing, destructuring, block mode

### 5c: Records

* [ ] Parse empty record: `{}` → `Expr::Empty`
* [ ] Parse record with fields: `{a: 5, b: 6}` → nested
      `Apply(Apply(Extend("a"), 5), Apply(Apply(Extend("b"), 6), Empty))`
* [ ] Parse record shorthand: `{a, b}` → same as `{a: a, b: b}`
* [ ] Parse record spread: `{a: 5, ..x}` → nested with `Overwrite` instead of `Extend`
* [ ] Parse identity spread: `{..x}` → just `x`
* [ ] Tests: empty, fields, shorthand, spread, identity spread, mixed

### 5d: Lists

* [ ] Parse empty list: `[]` → `Expr::Tail`
* [ ] Parse list with elements: `[1, 2]` → nested `Apply(Apply(Cons, 1), Apply(Apply(Cons, 2), Tail))`
* [ ] Parse list spread: `[1, ..rest]` → `Apply(Apply(Cons, 1), rest)`
* [ ] Tests: empty, elements, spread

### 5e: Match

* [ ] Parse match without subject: `match { Ok fn1 Error fn2 }` →
      `Apply(Apply(Case("Ok"), fn1), Apply(Apply(Case("Error"), fn2), NoCases))`
* [ ] Parse match with subject: `match e { Ok fn1 }` →
      `Apply(Apply(Apply(Case("Ok"), fn1), NoCases), e)`
* [ ] Parse open match (pipe fallback): `| (x) -> { fallback }` replaces
      `NoCases` with the fallback function
* [ ] Tests: simple match, multi-branch, with subject, open match

---

## Milestone 6: Public API & IR Serialization

Wire the parser into a clean public API and verify IR output.

* [ ] Create `crates/eyg-parser/src/lib.rs` with public functions:
  - `pub fn from_string(source: &str) -> Result<Node, ParseError>`
    (parse one expression)
  - `pub fn block_from_string(source: &str) -> Result<Node, ParseError>`
    (parse let-sequence, body defaults to `Vacant`)
* [ ] Verify `Node` serializes to correct dag-json via `serde_json::to_string`
      (the existing `Serialize` impl on `Expr`/`Node` handles this)
* [ ] Create round-trip tests: parse source → IR `Node` → serialize to JSON →
      deserialize back → assert structural equality
* [ ] Create golden-file tests in `testdata/parse_cases.json`:
  each case has `{ "name": "...", "source": "...", "expected_ir": <dag-json> }`
* [ ] Test error cases: unexpected token, unexpected end, unterminated string

---

## Milestone 7: CLI Integration

Add `--parse-ir` and `--parse-exec` flags to `eyg-run`, plus default Log handler.

* [ ] Add `--parse-ir <file>` subcommand/flag to `src/main.rs`:
  - Read source file as UTF-8 string
  - Call `eyg_parser::from_string(source)`
  - Serialize resulting `Node` as dag-json to stdout
  - On parse error: print error with byte offset to stderr, exit 1
* [ ] Add `--parse-exec <file>` subcommand/flag:
  - Parse source → `Node`
  - Execute `Node` through the interpreter (same path as JSON execution)
  - On parse error: stderr + exit 1
* [ ] Add built-in `Log` extrinsic effect handler:
  - When an `UnhandledEffect("Log", value)` bubbles to the stack base,
    print the lifted value to stderr (matching convention: Log goes to stderr)
  - Resume with unit (`Value::Record(empty)`)
  - Wire as a default extrinsic in `expression::execute` or in the CLI main loop
* [ ] Verify `eyg-run --parse-exec hello.eyg` with a file containing
      `perform Log("Hello, World!")` prints to stderr and exits 0
* [ ] Verify `eyg-run --parse-ir hello.eyg` outputs the expected dag-json

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