# Rust Interpreter Implementation Plan

## Overview

Port `packages/gleam_interpreter` to Rust, producing a standalone binary that
reads EYG programs serialised as dag-json (IR.json) from disk, executes them,
and prints the result.  The implementation should faithfully reproduce the
continuation-passing-style (CPS) evaluation model found in the Gleam source,
covering all IR node types, built-in functions, effects/handlers, and the full
test matrix from `spec/evaluation/`.

Reference sources:

| Gleam source | Role |
|---|---|
| `packages/gleam_ir/src/eyg/ir/tree.gleam` | IR AST type definitions |
| `packages/gleam_ir/src/eyg/ir/dag_json.gleam` | dag-json encode / decode |
| `packages/gleam_interpreter/src/eyg/interpreter/value.gleam` | Runtime value types |
| `packages/gleam_interpreter/src/eyg/interpreter/state.gleam` | Stepper / eval / apply |
| `packages/gleam_interpreter/src/eyg/interpreter/expression.gleam` | Public entry-points (`execute`, `call`, `resume`) |
| `packages/gleam_interpreter/src/eyg/interpreter/builtin.gleam` | All built-in functions |
| `packages/gleam_interpreter/src/eyg/interpreter/break.gleam` | Error / break reasons |
| `packages/gleam_interpreter/src/eyg/interpreter/cast.gleam` | Value casting helpers |
| `packages/gleam_interpreter/test/eyg/interpreter_test.gleam` | Evaluation test suite driver |
| `spec/evaluation/core_suite.json` | Core evaluation test fixtures |
| `spec/evaluation/builtins_suite.json` | Built-in function test fixtures |
| `spec/evaluation/effects_suite.json` | Effect / handler test fixtures |

---

## Key Implementation Notes

- **Input format** – Programs arrive as dag-json objects (compact single-char
  field keys: `"0"` = node type, `"l"` = label, etc.).  Parse with
  `serde_json`; convert immediately to well-typed `Expr` / `Node` Rust enums.
- **Type safety** – Deserialise once into a typed AST; never pass raw
  `serde_json::Value` into the evaluator.
- **Immutability & sharing** – Gleam's lists/dicts are persistent.  Use
  `im::Vector` / `im::HashMap` from the `im` crate (structural sharing) or
  `Rc<...>` + clone-on-write where that is simpler.  Closures capture
  `Scope = Vec<(String, Rc<Value>)>` (or `im::Vector`).
- **Pattern matching** – Every Gleam `case` in `state.gleam` maps 1-to-1 to a
  Rust `match`.  The stepper loop `loop(next)` maps to a Rust `loop { match
  next { ... } }`.
- **Error handling** – Use `Result<T, BreakReason>` throughout; no panics in
  normal execution paths.
- **CID / Reference nodes** – The `Reference` and `Release` IR nodes require a
  CID type.  For the initial milestone store CIDs as raw `String` (base32
  multibase encoding); add proper multiformat parsing later if needed.
- **No async** – The Gleam `await` / `Promise` path is JavaScript-specific.
  Omit it from the Rust port; the `Promise` value variant can be left as a
  stub or removed.

---

## Milestone 1: Project Setup ✅

**Progress**: `progress/PROJECT_SETUP.md`

- [x] Run `cargo new --lib rust-interpreter` inside `rust-interpreter/`; rename
      the default binary to `src/main.rs` (`cargo new --bin` or add
      `[[bin]]` to `Cargo.toml`).
- [x] Add dependencies via `cargo add`:
  - `serde = { features = ["derive"] }`
  - `serde_json`
  - `im` (persistent/immutable collections)
  - `base64` (dag-json binary decoding uses base64url)
  - `clap` (CLI argument parsing, Milestone 6)
- [x] Define workspace layout:
  ```
  rust-interpreter/
    Cargo.toml
    src/
      main.rs          # CLI entry-point
      ir/
        mod.rs         # re-exports
        ast.rs         # Expr / Node types
        dag_json.rs    # serde Deserialize impls
      interpreter/
        mod.rs
        value.rs       # Value / Switch enums
        break_reason.rs
        cast.rs
        env.rs         # Env struct
        state.rs       # Control / Stack / stepper
        builtin.rs     # all built-in functions
        expression.rs  # execute / call / resume
    tests/
      evaluation_suite.rs   # reads spec/evaluation/*.json
  ```
- [x] Confirm `cargo check` passes on the empty project skeleton before
      proceeding.
- [x] Setup Makefile in rust-interpreter, with `make check` running cargo test and clippy.

---

## Milestone 2: IR Data Structures ✅

**Progress**: `progress/IR_DATA_STRUCTURES.md`

Map every Gleam `Expression(m)` variant from `tree.gleam` to a Rust enum.
The metadata type parameter `m` is fixed to `()` for the initial port
(all nodes carry `()` as their annotation, matching `Node(Nil)` in tests).

- [x] Define `src/ir/ast.rs`:
  ```rust
  pub type Node = (Expr, ());   // or Box<Expr> for tree nodes

  pub enum Expr {
      Variable(String),
      Lambda { param: String, body: Box<Node> },
      Apply  { func: Box<Node>, arg: Box<Node> },
      Let    { label: String, def: Box<Node>, body: Box<Node> },
      Binary(Vec<u8>),
      Integer(i64),
      Str(String),
      Tail, Cons, Vacant,
      Empty,
      Extend(String), Select(String), Overwrite(String),
      Tag(String), Case(String), NoCases,
      Perform(String), Handle(String),
      Builtin(String),
      Reference(String),   // CID as base-32 string for now
      Release { package: String, release: i64, cid: String },
  }
  ```
- [x] Implement `serde::Deserialize` for `Expr` / `Node` in
      `src/ir/dag_json.rs`, mirroring the field-key table from `dag_json.gleam`:

  | JSON `"0"` value | Rust variant |
  |---|---|
  | `"v"` | `Variable` (field `"l"`) |
  | `"f"` | `Lambda` (fields `"l"`, `"b"`) |
  | `"a"` | `Apply` (fields `"f"`, `"a"`) |
  | `"l"` | `Let` (fields `"l"`, `"v"`, `"t"`) |
  | `"x"` | `Binary` (field `"v"` = dag-json bytes object `{"/":{bytes":…}}`) |
  | `"i"` | `Integer` (field `"v"`) |
  | `"s"` | `Str` (field `"v"`) |
  | `"ta"` | `Tail` |
  | `"c"` | `Cons` |
  | `"z"` | `Vacant` |
  | `"u"` | `Empty` |
  | `"e"` | `Extend` |
  | `"g"` | `Select` |
  | `"o"` | `Overwrite` |
  | `"t"` | `Tag` |
  | `"m"` | `Case` |
  | `"n"` | `NoCases` |
  | `"p"` | `Perform` |
  | `"h"` | `Handle` |
  | `"b"` | `Builtin` |
  | `"#"` | `Reference` (field `"l"` = CID link) |
  | `"@"` | `Release` (fields `"p"`, `"r"`, `"l"`) |

- [x] Handle the dag-json binary encoding: `{"/":{bytes":"<base64url>"}}`;
      decode the inner base64url string to `Vec<u8>`.
- [x] Handle the dag-json CID link encoding: `{"/":"<multibase-cid-string>"}`;
      store as `String`.
- [x] Write unit tests that round-trip each fixture in `spec/ir_suite.json`
      through `serde_json::from_str::<Node>`.

---

## Milestone 3: Core Interpreter ✅

**Progress**: `progress/CORE_INTERPRETER.md`

Port `state.gleam` — the stepper, `eval`, and `apply` functions — as the heart
of the interpreter.  Mirror the CPS structure exactly so the mapping to the
Gleam source stays obvious.

- [x] Define `src/interpreter/value.rs` — mirror `value.gleam`:
  ```rust
  pub type Scope = Vec<(String, Rc<Value>)>;

  pub enum Value {
      Binary(Vec<u8>),
      Integer(i64),
      Str(String),
      LinkedList(Vec<Rc<Value>>),
      Record(HashMap<String, Rc<Value>>),
      Tagged { label: String, value: Rc<Value> },
      Closure { param: String, body: Box<Node>, env: Scope },
      Partial(Switch, Vec<Rc<Value>>),
  }

  pub enum Switch {
      Cons,
      Extend(String), Overwrite(String), Select(String),
      Tag(String), Match(String),
      NoCases,
      Perform(String), Handle(String),
      Resume(ResumeCont),  // captured delimited continuation
      Builtin(String),
  }
  ```
- [x] Define `src/interpreter/break_reason.rs` — mirror `break.gleam`:
  ```rust
  pub enum BreakReason {
      NotAFunction(Box<Value>),
      UndefinedVariable(String),
      UndefinedBuiltin(String),
      UndefinedReference(String),
      UndefinedRelease { package: String, release: i64, cid: String },
      Vacant,
      NoMatch(Box<Value>),
      UnhandledEffect(String, Box<Value>),
      IncorrectTerm { expected: String, got: Box<Value> },
      MissingField(String),
  }
  ```
- [x] Define `src/interpreter/state.rs`:
  - `Control` enum: `Expr(Node)` | `Val(Rc<Value>)`
  - `Kontinue` enum: `Arg(Node, Env)` | `Apply(Rc<Value>, Env)` |
    `Assign(String, Node, Env)` | `CallWith(Rc<Value>, Env)` |
    `Delimit { label: String, handler: Rc<Value>, env: Env, shallow: bool }`
  - `Stack` enum: `Frame(Kontinue, (), Box<Stack>)` | `Empty(Handlers)`
    where `Handlers = HashMap<String, Extrinsic>`
  - `Next` enum: `Loop(Control, Env, Box<Stack>)` | `Break(EvalResult)`
  - Implement `fn step(c: Control, env: Env, k: Box<Stack>) -> Next`
  - Implement `fn eval(node: &Node, env: Env, k: Stack) -> StepReturn`
    mapping every `Expr` variant to a `Control`/`Stack` transition.
  - Implement `fn apply(value: Rc<Value>, env: Env, k: Kontinue, meta: (),
    rest: Stack) -> StepReturn` mapping every `Kontinue` variant.
  - Implement `fn call(f: Rc<Value>, arg: Rc<Value>, meta: (), env: Env, k: Stack)
    -> StepReturn` covering `Closure`, `Partial`, and error cases.
  - Implement `fn perform(label, arg, env, k)` and `fn deep(label, handler,
    exec, meta, env, k)` mirroring the effect dispatch in `state.gleam`.
- [x] Implement `src/interpreter/expression.rs`:
  - `pub fn execute(node: Node, scope: Scope) -> EvalResult`
  - `pub fn call(f: Rc<Value>, args: Vec<(Rc<Value>, ())>) -> EvalResult`
  - `pub fn resume(value: Rc<Value>, env: Env, k: Stack) -> EvalResult`
  - `fn new_env(scope: Scope) -> Env` — builds an `Env` with an empty
    references map and the full builtins table.

---

## Milestone 4: Environment & Scope ✅

**Progress**: `progress/ENV_AND_SCOPE.md`

- [x] Define `src/interpreter/env.rs`:
  ```rust
  pub struct Env {
      pub scope:      Scope,                          // lexical bindings
      pub references: HashMap<String, Rc<Value>>,     // CID → value cache
      pub builtins:   HashMap<String, Builtin>,
  }

  pub enum Builtin {
      Arity1(fn(Rc<Value>, Env, Stack) -> StepReturn),
      Arity2(fn(Rc<Value>, Rc<Value>, Env, Stack) -> StepReturn),
      Arity3(fn(Rc<Value>, Rc<Value>, Rc<Value>, Env, Stack) -> StepReturn),
      Arity4(fn(Rc<Value>, Rc<Value>, Rc<Value>, Rc<Value>, Env, Stack) -> StepReturn),
  }
  ```
- [x] Because `Env` is passed by value through the CPS stepper (cloned at each
      scope extension), wrap `scope` in `im::Vector<(String, Rc<Value>)>` so
      that clone is O(1).  Alternatively use `Rc<Vec<...>>` with prepend-on-copy.
      (Note: Using Vec for now, can optimize later if needed)
- [x] `scope` lookup: linear scan from head (most-recently-bound wins), matching
      Gleam's `list.key_find`.
- [x] Implement `fn extend_scope(env: &Env, label: String, value: Rc<Value>)
      -> Env` — returns a new `Env` with the binding prepended.
      (Implemented as `Env::extend()` method)
- [x] Populate the builtins map in `expression::new_env` with the same 27 keys
      listed in `expression.gleam`'s `builtins()` function.
- [x] Create stub implementations for all 27 builtin functions in `builtin.rs`
      (actual implementations will be added in Milestone 5).

---

## Milestone 5: Built-in Functions ✅

**Progress**: `progress/BUILTIN_FUNCTIONS.md`

Port every function from `builtin.gleam`.  Each built-in receives its fully-
applied argument list plus `(env, k)` and returns `StepReturn`.

- [x] **Equality / control flow**
  - `equal` (Arity2): structural equality → `Tagged("True"|"False", unit)`
  - `fix` (Arity1): fixed-point combinator — calls builder with
    `Partial(Builtin("fixed"), [builder])`
  - `fixed` (Arity2): one step of the fixed-point unrolling
  - `never` (Arity1): always returns `IncorrectTerm("Never", …)`
- [x] **Integer operations** (`int_compare`, `int_add`, `int_subtract`,
      `int_multiply`, `int_divide`, `int_absolute`, `int_parse`,
      `int_to_string`)
  - `int_compare` → `Tagged("Lt"|"Eq"|"Gt", unit)`
  - `int_divide` → `Tagged("Ok"|"Error", …)` (divide-by-zero returns `Error`)
  - `int_parse` → `Tagged("Ok"|"Error", …)`
- [x] **String operations** (`string_append`, `string_split`,
      `string_split_once`, `string_replace`, `string_uppercase`,
      `string_lowercase`, `string_starts_with`, `string_ends_with`,
      `string_length`, `string_to_binary`, `string_from_binary`)
  - `string_split` → `Record { head: Str, tail: LinkedList<Str> }`
  - `string_split_once` → `Tagged("Ok", Record { pre, post }) | Tagged("Error", unit)`
  - `string_from_binary` → `Tagged("Ok", Str) | Tagged("Error", unit)`
- [x] **Binary operations** (`binary_from_integers`, `binary_fold`)
  - `binary_from_integers`: list of `Integer` → `Binary`
  - `binary_fold` (Arity3): mirrors `list_fold` but over bytes
- [x] **List operations** (`list_pop`, `list_fold`)
  - `list_pop` → `Tagged("Ok", Record { head, tail }) | Tagged("Error", unit)`
  - `list_fold` (Arity3): recursive CPS fold; push continuation frames onto
    the stack rather than recursing, matching the Gleam implementation.
- [x] Implement `src/interpreter/cast.rs` with helpers: `as_integer`,
      `as_string`, `as_binary`, `as_list`, `as_record`, `as_tagged`.

---

## Milestone 6: Testing ✅

**Progress**: `progress/TESTING.md`

Drive the same JSON test fixtures used by the Gleam test suite.

- [x] Create `tests/evaluation_suite.rs` with a `#[test]` that:
  1. Reads `spec/evaluation/core_suite.json`,
    `spec/evaluation/builtins_suite.json`,
    `spec/evaluation/effects_suite.json` relative to the workspace root.
  2. Deserialises each fixture:
     ```json
     { "name": "…", "source": <IR node>,
       "effects": [{"label","lift","reply"}],
       "value": <expected Value> | "break": <BreakReason> }
     ```
  3. Calls `expression::execute(source, vec![])`.
  4. For each listed effect, asserts `UnhandledEffect(label, lift)` was
     raised, then calls `expression::resume(reply, env, k)`.
  5. Compares final result to expected value or break reason.
- [x] All fixtures in all three suites must pass (`cargo test`).
- [x] Add unit tests for the dag-json decoder covering every node type using
      fixtures from `spec/ir_suite.json`.

---

## Milestone 7: CLI ✅

**Progress**: `progress/CLI_IMPLEMENTATION.md`, `progress/EFFECTS_FLAG.md`

- [x] In `src/main.rs`, use `clap` to define:
  ```
  eyg-run <file.json>
  ```
  - Reads the file, deserialises as a `Node`, calls `execute(node, vec![])`.
  - On `Ok(value)`: pretty-print the value to stdout.
  - On `Err(reason)`: print the break reason to stderr and exit with code 1.
- [x] Add a `--effects` flag (or stdin protocol) so callers can supply effect
      handlers for effects that would otherwise be `UnhandledEffect`.
  - Implemented `--effects <file>` flag to read effect handlers from JSON
  - Handlers specify label and reply value for each effect
  - Programs with unhandled effects print error and exit with code 1
- [x] Implement a `Display` (or simple `fn to_string`) for `Value` and
      `BreakReason` suitable for human-readable CLI output.
- [x] Verify the CLI works end-to-end with a simple program from
      `spec/evaluation/core_suite.json` (e.g., `"integer primitive"` → `42`).

---

## Milestone 8: Performance Optimizations (In Progress)

**Progress**: `progress/PERSISTENT_DATA_STRUCTURES.md`

Code review identified several opportunities to improve memory efficiency and
reduce unnecessary allocations. The current implementation prioritizes
correctness over performance, which is appropriate for a first port, but these
optimizations should be addressed for production use.

### 8.1 Use Persistent Data Structures ✅

**Progress**: `progress/PERSISTENT_DATA_STRUCTURES.md`

The `im` crate is already a dependency but was never used. Environment cloning
happens on every `let` binding and closure call, making this a hot path.

- [x] Change `Scope` from `Vec<(String, Rc<Value>)>` to `im::Vector<(String, Rc<Value>)>`
- [x] Change `Env.references` from `HashMap<String, Rc<Value>>` to `im::HashMap<String, Rc<Value>>`
- [x] Change `Env.builtins` from `HashMap<String, Builtin>` to `im::HashMap<String, Builtin>`
- [x] Update `Env::extend()` to use `im::Vector::push_front()` for O(log n) instead of O(n)
- [x] Update all usage sites in interpreter modules
- [x] Update all test files
- [x] Verify all tests pass (26 tests)

**Impact**: `Env::extend()` goes from O(n) full clone to O(log n) structural sharing.

### 8.2 Refactor Cast Functions to Return References (High Priority)

Current cast functions clone inner data unnecessarily:
```rust
// Current - clones entire HashMap
pub fn as_record(value: &Value) -> Result<HashMap<String, Rc<Value>>, BreakReason>

// Better - returns reference to existing data
pub fn as_record(value: &Value) -> Result<&HashMap<String, Rc<Value>>, BreakReason>
```

- [ ] Change `as_string` to return `Result<&str, BreakReason>`
- [ ] Change `as_binary` to return `Result<&[u8], BreakReason>`
- [ ] Change `as_list` to return `Result<&Vec<Rc<Value>>, BreakReason>`
- [ ] Change `as_record` to return `Result<&HashMap<String, Rc<Value>>, BreakReason>`
- [ ] Update all call sites in `builtin.rs` and `state.rs` accordingly

**Impact**: Eliminates deep clones of strings, byte arrays, lists, and records on every type check.

### 8.3 Accept References in Builtin Functions (Medium Priority)

Clippy warns that many builtin functions receive `Rc<Value>` by value but only
borrow the contents:
```rust
// Current - takes ownership unnecessarily
pub fn int_add(left: Rc<Value>, right: Rc<Value>, ...) -> StepReturn

// Better - borrows without incrementing refcount
pub fn int_add(left: &Rc<Value>, right: &Rc<Value>, ...) -> StepReturn
```

- [ ] Update `BuiltinFn1..4` type aliases to take `&Rc<Value>` instead of `Rc<Value>`
- [ ] Update all builtin function signatures in `builtin.rs`
- [ ] Update `call_builtin` in `state.rs` to pass references

**Impact**: Avoids unnecessary reference count increments/decrements in builtin calls.

### 8.4 Address Clippy Pedantic Warnings (Low Priority)

Running `cargo clippy -- -W clippy::pedantic -W clippy::nursery` produces ~215
warnings. Most are style suggestions that improve code quality:

- [ ] Use `Self` instead of type name in impl blocks
- [ ] Add `#[must_use]` attributes to pure functions
- [ ] Use inline format args (`format!("{x}")` instead of `format!("{}", x)`)
- [ ] Add `# Errors` sections to doc comments for functions returning `Result`
- [ ] Use `i64::from(byte)` instead of `byte as i64` for lossless casts

### 8.5 Consider Additional Optimizations (Future)

These are lower priority but worth considering for heavily-used interpreters:

- [ ] **Intern strings**: Use a string interner for labels/identifiers to reduce
      allocations and enable cheap equality checks
- [ ] **Arena allocation**: Consider using an arena allocator for AST nodes and
      Values to improve cache locality
- [ ] **Tail call optimization**: Detect and optimize tail calls to avoid stack
      growth in recursive programs
- [ ] **Bytecode compilation**: For frequently-executed code, compile to a more
      efficient bytecode representation
