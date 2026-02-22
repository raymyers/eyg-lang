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

## Milestone 1: Project Setup

- [ ] Run `cargo new --lib rust-interpreter` inside `rust-interpreter/`; rename
      the default binary to `src/main.rs` (`cargo new --bin` or add
      `[[bin]]` to `Cargo.toml`).
- [ ] Add dependencies via `cargo add`:
  - `serde = { features = ["derive"] }`
  - `serde_json`
  - `im` (persistent/immutable collections)
  - `base64` (dag-json binary decoding uses base64url)
  - `clap` (CLI argument parsing, Milestone 6)
- [ ] Define workspace layout:
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
- [ ] Confirm `cargo check` passes on the empty project skeleton before
      proceeding.
- [ ] Setup Makefile in rust-interpreter, with `make check` running cargo test and clippy.

---

## Milestone 2: IR Data Structures

Map every Gleam `Expression(m)` variant from `tree.gleam` to a Rust enum.
The metadata type parameter `m` is fixed to `()` for the initial port
(all nodes carry `()` as their annotation, matching `Node(Nil)` in tests).

- [ ] Define `src/ir/ast.rs`:
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
- [ ] Implement `serde::Deserialize` for `Expr` / `Node` in
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

- [ ] Handle the dag-json binary encoding: `{"/":{bytes":"<base64url>"}}`;
      decode the inner base64url string to `Vec<u8>`.
- [ ] Handle the dag-json CID link encoding: `{"/":"<multibase-cid-string>"}`;
      store as `String`.
- [ ] Write unit tests that round-trip each fixture in `spec/ir_suite.json`
      through `serde_json::from_str::<Node>`.

---

## Milestone 3: Core Interpreter

Port `state.gleam` — the stepper, `eval`, and `apply` functions — as the heart
of the interpreter.  Mirror the CPS structure exactly so the mapping to the
Gleam source stays obvious.

- [ ] Define `src/interpreter/value.rs` — mirror `value.gleam`:
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
- [ ] Define `src/interpreter/break_reason.rs` — mirror `break.gleam`:
  ```rust
  pub enum BreakReason {
      NotAFunction(Value),
      UndefinedVariable(String),
      UndefinedBuiltin(String),
      UndefinedReference(String),
      UndefinedRelease { package: String, release: i64, cid: String },
      Vacant,
      NoMatch(Value),
      UnhandledEffect(String, Value),
      IncorrectTerm { expected: String, got: Value },
      MissingField(String),
  }
  ```
- [ ] Define `src/interpreter/state.rs`:
  - `Control` enum: `Expr(Node)` | `Val(Rc<Value>)`
  - `Kontinue` enum: `Arg(Node, Env)` | `Apply(Rc<Value>, Env)` |
    `Assign(String, Node, Env)` | `CallWith(Rc<Value>, Env)` |
    `Delimit { label: String, handler: Rc<Value>, env: Env, shallow: bool }`
  - `Stack` enum: `Frame(Kontinue, (), Box<Stack>)` | `Empty(Handlers)`
    where `Handlers = HashMap<String, Box<dyn Fn(Rc<Value>) -> StepResult>>`
  - `Next` enum: `Loop(Control, Env, Stack)` | `Break(EvalResult)`
  - Implement `fn step(c: Control, env: Env, k: Stack) -> Next`
  - Implement `fn eval(node: &Node, env: &Env, k: Stack) -> StepReturn`
    mapping every `Expr` variant to a `Control`/`Stack` transition.
  - Implement `fn apply(value: Rc<Value>, env: &Env, k: Kontinue, meta: (),
    rest: Stack) -> StepReturn` mapping every `Kontinue` variant.
  - Implement `fn call(f: Rc<Value>, arg: Rc<Value>, env: Env, k: Stack)
    -> StepReturn` covering `Closure`, `Partial`, and error cases.
  - Implement `fn perform(label, arg, env, k)` and `fn deep(label, handler,
    exec, env, k)` mirroring the effect dispatch in `state.gleam`.
- [ ] Implement `src/interpreter/expression.rs`:
  - `pub fn execute(node: Node, scope: Scope) -> EvalResult`
  - `pub fn call_fn(f: Rc<Value>, args: Vec<Rc<Value>>) -> EvalResult`
  - `pub fn resume(value: Rc<Value>, env: Env, k: Stack) -> EvalResult`
  - `fn new_env(scope: Scope) -> Env` — builds an `Env` with an empty
    references map and the full builtins table.

---

## Milestone 4: Environment & Scope

- [ ] Define `src/interpreter/env.rs`:
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
- [ ] Because `Env` is passed by value through the CPS stepper (cloned at each
      scope extension), wrap `scope` in `im::Vector<(String, Rc<Value>)>` so
      that clone is O(1).  Alternatively use `Rc<Vec<...>>` with prepend-on-copy.
- [ ] `scope` lookup: linear scan from head (most-recently-bound wins), matching
      Gleam's `list.key_find`.
- [ ] Implement `fn extend_scope(env: &Env, label: String, value: Rc<Value>)
      -> Env` — returns a new `Env` with the binding prepended.
- [ ] Populate the builtins map in `expression::new_env` with the same 27 keys
      listed in `expression.gleam`'s `builtins()` function.

---

## Milestone 5: Built-in Functions

Port every function from `builtin.gleam`.  Each built-in receives its fully-
applied argument list plus `(env, k)` and returns `StepReturn`.

- [ ] **Equality / control flow**
  - `equal` (Arity2): structural equality → `Tagged("True"|"False", unit)`
  - `fix` (Arity1): fixed-point combinator — calls builder with
    `Partial(Builtin("fixed"), [builder])`
  - `fixed` (Arity2): one step of the fixed-point unrolling
  - `never` (Arity1): always returns `IncorrectTerm("Never", …)`
- [ ] **Integer operations** (`int_compare`, `int_add`, `int_subtract`,
      `int_multiply`, `int_divide`, `int_absolute`, `int_parse`,
      `int_to_string`)
  - `int_compare` → `Tagged("Lt"|"Eq"|"Gt", unit)`
  - `int_divide` → `Tagged("Ok"|"Error", …)` (divide-by-zero returns `Error`)
  - `int_parse` → `Tagged("Ok"|"Error", …)`
- [ ] **String operations** (`string_append`, `string_split`,
      `string_split_once`, `string_replace`, `string_uppercase`,
      `string_lowercase`, `string_starts_with`, `string_ends_with`,
      `string_length`, `string_to_binary`, `string_from_binary`)
  - `string_split` → `Record { head: Str, tail: LinkedList<Str> }`
  - `string_split_once` → `Tagged("Ok", Record { pre, post }) | Tagged("Error", unit)`
  - `string_from_binary` → `Tagged("Ok", Str) | Tagged("Error", unit)`
- [ ] **Binary operations** (`binary_from_integers`, `binary_fold`)
  - `binary_from_integers`: list of `Integer` → `Binary`
  - `binary_fold` (Arity3): mirrors `list_fold` but over bytes
- [ ] **List operations** (`list_pop`, `list_fold`)
  - `list_pop` → `Tagged("Ok", Record { head, tail }) | Tagged("Error", unit)`
  - `list_fold` (Arity3): recursive CPS fold; push continuation frames onto
    the stack rather than recursing, matching the Gleam implementation.
- [ ] Implement `src/interpreter/cast.rs` with helpers: `as_integer`,
      `as_string`, `as_binary`, `as_list`, `as_record`, `as_tagged`.

---

## Milestone 6: Testing

Drive the same JSON test fixtures used by the Gleam test suite.

- [ ] Create `tests/evaluation_suite.rs` with a `#[test]` that:
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
- [ ] All fixtures in all three suites must pass (`cargo test`).
- [ ] Add unit tests for the dag-json decoder covering every node type using
      fixtures from `spec/ir_suite.json`.

---

## Milestone 7: CLI

- [ ] In `src/main.rs`, use `clap` to define:
  ```
  eyg-run <file.json>
  ```
  - Reads the file, deserialises as a `Node`, calls `execute(node, vec![])`.
  - On `Ok(value)`: pretty-print the value to stdout.
  - On `Err(reason)`: print the break reason to stderr and exit with code 1.
- [ ] Add a `--effects` flag (or stdin protocol) so callers can supply effect
      handlers for effects that would otherwise be `UnhandledEffect`.
  - Initial approach: handle no effects (programs that require effects will
    print the unhandled effect info and exit).
- [ ] Implement a `Display` (or simple `fn to_string`) for `Value` and
      `BreakReason` suitable for human-readable CLI output.
- [ ] Verify the CLI works end-to-end with a simple program from
      `spec/evaluation/core_suite.json` (e.g., `"integer primitive"` → `42`).
