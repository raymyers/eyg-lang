# Rust Type-Checker Implementation Plan

## Overview

Port `packages/gleam_analysis` to Rust as a new `eyg-analysis` crate within
the existing Cargo workspace, sharing IR types with the interpreter and parser.
The type-checker implements Algorithm J with levels (Oleg Kiselyov) combined
with effect opening/closing from algebraic effects literature.

The CLI (`eyg-run`) gains a `--type-check` flag that works in both parse mode
(`.eyg` source) and IR mode (dag-json).  On success it prints the inferred
top-level type; on failure it prints all type errors and exits with code 1.

All work is **test-first**: write tests before implementation, using the Gleam
test suite as the specification.

Reference sources:

| Gleam source | Role |
|---|---|
| `packages/gleam_analysis/src/eyg/analysis/type_/isomorphic.gleam` | Core `Type(var)` enum — 13 variants |
| `packages/gleam_analysis/src/eyg/analysis/type_/binding.gleam` | Binding store, `resolve`, `gen`, `instantiate` |
| `packages/gleam_analysis/src/eyg/analysis/type_/binding/unify.gleam` | Worklist-based Robinson unification with row/effect rewriting |
| `packages/gleam_analysis/src/eyg/analysis/type_/binding/error.gleam` | 9 error variants |
| `packages/gleam_analysis/src/eyg/analysis/type_/binding/debug.gleam` | Pretty-printing types, effects, errors |
| `packages/gleam_analysis/src/eyg/analysis/inference/levels_j/contextual.gleam` | Main inference engine (613 lines, all 21 IR forms) |
| `packages/gleam_analysis/test/eyg/analysis/type_/binding/unify_test.gleam` | Unification edge-case tests |
| `packages/gleam_analysis/test/eyg/analysis/type_/binding/debug_test.gleam` | Pretty-print tests |
| `packages/gleam_analysis/test/eyg/analysis/inference/levels_j/contextual_test.gleam` | Full inference test suite |

### Key Design Decisions

- **Functions carry effects**: `Fun(arg, effect, return)` — every arrow has an
  effect slot.
- **Row polymorphism everywhere**: Records, unions, AND effects use extensible
  row types (`RowExtend`/`EffectExtend` chains ending in `Empty` or a variable).
- **Levels replace env scanning**: Type variable levels allow O(1)
  generalization decisions instead of scanning the entire environment for free
  variables.
- **Poly vs Mono types**: `Mono = Type<usize>` (variable is an index).
  `Poly = Type<(bool, usize)>` where the bool indicates "is quantified".
- **Bindings as `Vec<Binding>`**: Variables get sequential IDs from
  `bindings.len()` — maps directly to a `Vec` in Rust (the Gleam code uses
  `Dict(Int, Binding)` with `dict.size()` for new IDs).
- **Open/close effects**: Effect tails are opened (replaced with fresh vars) at
  `Variable`/`Builtin` lookup and closed (excess tails removed) at `Let`
  generalization. Only `Apply` nodes can produce effects.
- **Error recovery**: On type error, a fresh type variable is assigned so
  inference continues through the rest of the program.

### Mapping from Gleam to Rust

| Gleam | Rust |
|---|---|
| `Type(var)` — generic over var | `Type<V>` — generic enum, `Mono = Type<usize>`, `Poly = Type<(bool, usize)>` |
| `Dict(Int, Binding)` | `Vec<Binding>` (index = variable ID) |
| `#(result, type, effect, env)` per node | `NodeInfo { result, typ, eff, scope }` collected in a `Vec` |
| `do_infer` returns annotated tree | `infer` walks `&Node` and appends to `Vec<NodeInfo>` |
| `v1.Cid` | `String` (same as eyg-ir's Reference identifier) |

---

## Milestone 1: Crate Setup

* [ ] Create `crates/eyg-analysis/Cargo.toml` with `eyg-ir` as a dependency
      and edition 2024
* [ ] Create `crates/eyg-analysis/src/lib.rs` with module declarations:
      `pub mod types;` `pub mod binding;` `pub mod unify;` `pub mod error;`
      `pub mod debug;` `pub mod infer;` `pub mod builtins;`
* [ ] Add `"crates/eyg-analysis"` to workspace members in root `Cargo.toml`
* [ ] Add `eyg-analysis = { path = "crates/eyg-analysis" }` to root `[dependencies]`
* [ ] Add `eyg-parser` as a `[dev-dependencies]` of `eyg-analysis`
      (needed by inference tests that parse `.eyg` source)
* [ ] Verify `make check` still passes (all existing ~98 tests green, clippy clean)

---

## Milestone 2: Type Representation & Error Types

Port `type_/isomorphic.gleam` and `type_/binding/error.gleam`.

* [ ] `crates/eyg-analysis/src/types.rs` — `Type<V>` enum with 13 variants:
      `Var(V)`, `Fun(Box<Type<V>>, Box<Type<V>>, Box<Type<V>>)`,
      `Binary`, `Integer`, `String`, `List(Box<Type<V>>)`,
      `Record(Box<Type<V>>)`, `Union(Box<Type<V>>)`, `Empty`,
      `RowExtend(String, Box<Type<V>>, Box<Type<V>>)`,
      `EffectExtend(String, (Box<Type<V>>, Box<Type<V>>), Box<Type<V>>)`,
      `Never`, `Promise(Box<Type<V>>)`
* [ ] Type aliases: `pub type Mono = Type<usize>;`
      `pub type Poly = Type<(bool, usize)>;`
* [ ] Convenience constructors: `Type::unit()` → `Record(Empty)`,
      `Type::boolean()` → `Union(RowExtend("True", unit, RowExtend("False", unit, Empty)))`,
      `Type::result(value, reason)`, `Type::rows(pairs)`, `Type::record(pairs)`,
      `Type::union(pairs)`
* [ ] `crates/eyg-analysis/src/error.rs` — `Reason` enum with 9 variants:
      `Todo`, `MissingVariable(String)`, `MissingBuiltin(String)`,
      `MissingReference(String)`, `UndefinedRelease { package, release, identifier }`,
      `TypeMismatch(Mono, Mono)`, `MissingRow(String)`, `Recursive`, `SameTail(Mono, Mono)`
* [ ] Derive `Debug`, `Clone`, `PartialEq` on both enums
* [ ] Unit tests: construct each `Type` variant, verify `PartialEq`; construct
      each `Reason` variant

---

## Milestone 3: Binding Operations

Port `type_/binding.gleam` — the type variable store and poly/mono operations.

* [ ] `crates/eyg-analysis/src/binding.rs` — `Binding` enum:
      `Bound(Mono)` | `Unbound(usize)` (level)
* [ ] `Bindings` newtype wrapping `Vec<Binding>` with methods:
  - `new() -> Self`
  - `fresh_mono(level) -> (Mono, &mut Self)` — push `Unbound(level)`, return `Var(id)`
  - `fresh_poly(level) -> (Poly, &mut Self)` — push `Unbound(level)`, return `Var((false, id))`
  - `bind(id, Mono)` — set `bindings[id] = Bound(mono)`
  - `get(id) -> &Binding`
* [ ] `resolve(type_: &Mono, bindings: &Bindings) -> Mono` — chase `Bound`
      links to ground type, recursing through all `Type` variants
* [ ] `gen(type_: &Mono, level: usize, bindings: &Bindings) -> Poly` —
      generalize: `Unbound(l)` with `l > level` becomes `Var((true, id))`,
      otherwise `Var((false, id))`; recurse through structure
* [ ] `instantiate(poly: &Poly, level: usize, bindings: &mut Bindings) -> Mono`
      — replace each quantified `Var((true, id))` with a fresh mono var,
      using a local `HashMap<usize, Mono>` for sharing
* [ ] Unit tests:
  - `fresh_mono` returns sequential IDs
  - `resolve` chases one-step and multi-step bindings
  - `gen` marks variables above level as quantified
  - `instantiate` replaces quantified vars with fresh, preserves free vars

---

## Milestone 4: Unification

Port `type_/binding/unify.gleam` — worklist-based unification with row
rewriting.

* [ ] `crates/eyg-analysis/src/unify.rs` —
      `pub fn unify(t1: &Mono, t2: &Mono, level: usize, bindings: &mut Bindings) -> Result<(), Reason>`
* [ ] Worklist-based `do_unify` (iterative loop over pairs to unify):
  - Same `Var(i) == Var(j)` → skip
  - Either side `Bound(t)` → substitute and retry
  - One side `Var(i)` with `Unbound` → occurs check + level adjustment, then bind
  - Structural: `Fun/Fun`, `Integer/Integer`, `Binary/Binary`, `String/String`,
    `List/List`, `Empty/Empty`, `Record/Record`, `Union/Union`,
    `Never/Never`, `Promise/Promise` — push sub-constraints
  - `RowExtend` vs anything → `rewrite_row`
  - `EffectExtend` vs anything → `rewrite_effect`
  - Otherwise → `TypeMismatch`
* [ ] `occurs_and_levels(i, level, types, bindings)` — recursive occurs
      check that also adjusts unbound variable levels via `min(l, level)`
* [ ] `rewrite_row(label, type_, level, bindings, check)` — find matching
      label in row, rewrite tail; handle same-tail guard (`SameTail` error);
      handle unbound var tail (create fresh row extension)
* [ ] `rewrite_effect(label, type_, level, bindings, check)` — same logic
      for `EffectExtend` chains with `(lift, reply)` pairs
* [ ] Tests mirroring `unify_test.gleam`:
  - `binding_types_in_tail_position_get_resolved` — unify open record vs
    closed record, expect `MissingRow("init")`
  - `rows_with_the_same_common_tail_dont_unify` — two `RowExtend` sharing
    a tail var, expect error (no infinite loop)
  - `effects_with_the_same_common_tail_dont_unify` — two `EffectExtend`
    sharing a tail var, expect error
* [ ] Additional unit tests: unify identical types, unify `Var` with concrete,
      occurs-check failure (`Recursive` error), row rewriting with multiple labels

---

## Milestone 5: Debug / Display

Port `type_/binding/debug.gleam` — human-readable rendering of types, effects,
and errors.

* [ ] `crates/eyg-analysis/src/debug.rs` with:
  - `pub fn render_mono(type_: &Mono) -> String`
  - `pub fn render_effects(eff: &Mono) -> String`
  - `pub fn render_reason(reason: &Reason) -> String`
* [ ] Function rendering: multi-arg functions collapse
      `Fun(a, e1, Fun(b, e2, ret))` → `(a, b) -> ret`, with `<effect>` after
      each arg if effect is non-Empty
* [ ] Row rendering: `RowExtend("x", T, tail)` → `x: T, ...` with `..N` for
      open tails
* [ ] Effect rendering: `EffectExtend("Log", (String, Unit), tail)` →
      `Log(↑String ↓{})`, comma-separated, `..N` for open tails
* [ ] Tests mirroring `debug_test.gleam`:
  - `pure_function` → `"(Integer) -> String"`
  - `multiple_argument_function` → `"(Integer, Integer) -> String"`
  - `open_function` → `"(Integer <..1>) -> String"`
  - `closed_effectful_function` → `"(Integer <Abort(↑String ↓{}), Count(↑{} ↓Integer)>) -> String"`
  - `open_effectful_function` → `"(Integer <Abort(↑String ↓{}), ..2>) -> String"`
  - `polymorphic_effect` → `"((String <..0>) -> String, Integer <..0>) -> String"`
* [ ] Implement `Display` for `Reason` via `render_reason`

---

## Milestone 6: Inference Engine — Core Forms

Port the core of `contextual.gleam`'s `do_infer` for: `Variable`, `Lambda`,
`Apply`, `Let`, `Vacant`, `Integer`, `Binary`, `String`.

* [ ] `crates/eyg-analysis/src/infer.rs` with:
  - `Context` struct: `env: Vec<(String, Poly)>`, `eff: Mono`,
    `refs: HashMap<String, Poly>`, `level: usize`, `bindings: Bindings`
  - `Context::pure()` → effect = `Empty`
  - `Context::unpure()` → effect = fresh var
  - `NodeInfo` struct: `result: Result<(), Reason>`, `typ: Mono`, `eff: Mono`
  - `Analysis` struct: `bindings: Bindings`, `annotations: Vec<NodeInfo>`
  - `pub fn check(context: &mut Context, source: &Node) -> Analysis`
  - `pub fn type_of(analysis: &Analysis) -> Mono` — resolved top-level type
* [ ] Internal `do_infer(node, env, eff, refs, level, bindings) -> (Mono, Mono)`
      that pushes `NodeInfo` to an accumulator during DFS traversal matching
      `get_annotation` order (self, then children left-to-right)
* [ ] `open_effect` / `open` — replace closed effect tails with fresh vars
* [ ] `close` / `close_eff` — remove effect tail vars that would generalize
      and aren't free in arg/ret (using `ftv` free-type-variables helper)
* [ ] `prim` helper — instantiate a poly scheme, open, record annotation
* [ ] Handle each core IR form:
  - `Variable` — env lookup, instantiate + open; or error `MissingVariable`
  - `Lambda` — fresh arg type, infer body at level+1 with fresh effect,
    result is `Fun(arg, eff, ret)`, close
  - `Apply` — infer func and arg at level+1, unify
    `Fun(arg_ty, test_eff, ret_ty)` with `func_ty`, unify `test_eff` with
    ambient `eff`, handle effect raising, close return type
  - `Let` — infer value at level+1, generalize + close, infer body with
    extended env
  - `Vacant` — fresh type, error `Todo`
  - `Integer`/`Binary`/`String` — prim with the concrete type
* [ ] Tests (using `eyg-parser` in dev-deps to parse source):
  - `variable` — unknown variable → `MissingVariable`
  - `literal` — `5` → `Integer`, `"hello"` → `String`
  - `simple_function` — identity, applied identity, multi-arg
  - `let` — basic binding, shadowing
  - `let_polymorphism` — `let f = (x) -> { x }` used at `Int` and `String`

---

## Milestone 7: Inference Engine — Data Structures

Extend `do_infer` for: `Tail`, `Cons`, `Empty`, `Extend`, `Select`,
`Overwrite`, `Tag`, `Case`, `NoCases`.

* [ ] Type schemes for each (mirroring `contextual.gleam`):
  - `Tail` → `List(q(0))`
  - `Cons` → `(q(0), List(q(0))) -> List(q(0))`
  - `Empty` → `Record(Empty)` (i.e. unit)
  - `Extend(l)` → `(q(0), Record(q(1))) -> Record(RowExtend(l, q(0), q(1)))`
  - `Overwrite(l)` → `(q(0), Record(RowExtend(l, q(1), q(2)))) -> Record(RowExtend(l, q(0), q(2)))`
  - `Select(l)` → `Record(RowExtend(l, q(0), q(1))) -> q(0)`
  - `Tag(l)` → `q(0) -> Union(RowExtend(l, q(0), q(1)))`
  - `Case(l)` → `(inner->ret, Union(tail)->ret) -> Union(RowExtend(l,inner,tail)) -> ret`
    (with effect in branches)
  - `NoCases` → `Union(Empty) -> q(0)`
* [ ] Wire each as a `prim(scheme, ...)` call in `do_infer`
* [ ] Tests:
  - `list` — `[]` → `List(0)`, `[3]` → `List(Integer)`
  - `list_polymorphism` — list of identity functions
  - `record` — `{}` → `{}`, `{a: 3}` → `{a: Integer}`
  - `record_unification` — destructuring + field access
  - `select` — `{name: 5}.name` → `Integer`, `x.name` → open row,
    `{}.name` → `MissingRow`
  - `tag` — `Ok` → `(0) -> Ok: 0 | ..1`, `Ok(8)` → `Ok: Integer | ..1`

---

## Milestone 8: Inference Engine — Effects & Builtins

Extend `do_infer` for: `Perform`, `Handle`, `Builtin`, `Reference`, `Release`.
Port the complete builtin type table.

* [ ] Type schemes:
  - `Perform(l)` → `Fun(q(0), EffectExtend(l, (q(0), q(1)), Empty), q(1))`
  - `Handle(l)` → handler + exec → return (see `contextual.gleam` `handle` fn)
  - `Builtin(id)` → lookup in builtin table; error `MissingBuiltin` if unknown
  - `Reference(cid)` → lookup in `refs`; error `MissingReference` if unknown
  - `Release(pkg, rel, cid)` → lookup in `refs`; error `UndefinedRelease`
* [ ] `crates/eyg-analysis/src/builtins.rs` — builtin type table:
  - `equal` → `(q(0), q(0)) -> Boolean`
  - `fix` → `Fun(Fun(q(0), q(1), q(0)), q(1), q(0))`
  - `never` → `(Never) -> q(1)`
  - Integer ops: `int_add`, `int_subtract`, `int_multiply` → `(Int, Int) -> Int`;
    `int_divide` → `(Int, Int) -> Result(Int, {})`;
    `int_absolute` → `Int -> Int`;
    `int_parse` → `String -> Result(Int, {})`;
    `int_to_string` → `Int -> String`;
    `int_compare` → `(Int, Int) -> Lt:{} | Eq:{} | Gt:{}`
  - String ops: `string_append`, `string_split`, `string_split_once`,
    `string_replace`, `string_uppercase`, `string_lowercase`,
    `string_starts_with`, `string_ends_with`, `string_length`,
    `string_to_binary`, `string_from_binary`
  - Binary ops: `binary_from_integers`, `binary_fold`
  - List ops: `list_pop`, `list_fold`
* [ ] Tests:
  - `builtin` — `!int_add` type, `!int_add(1, 2)` type, unknown builtin error
  - `perform` — `perform Log("thing")` with open effect
  - `perform_unifies_with_env` — `perform Log(5)` with `Log: (String, {})` in
    context → `TypeMismatch`
  - `only_unknown_effect` — `(f) -> { f(5) }` has open effect from `f`
  - `combine_effect` — multiple performs in sequence/nested
  - `combine_with_pure` — pure subexpression doesn't leak effects
  - `combine_unknown_effect` — unknown function + known perform
  - `first_class_function_with_effects`
  - `unify_fn_arg` — function passed as argument with effects
  - `poly_in_effect` — polymorphic let-bound function used with different effects

---

## Milestone 9: CLI Integration

Wire `eyg-analysis` into the `eyg-run` CLI binary.

* [ ] Add `--type-check <FILE>` flag to `Args` struct in `src/main.rs`
      (mutually exclusive with existing modes)
* [ ] Detect file extension or content:
  - `.eyg` → parse source with `eyg_parser::from_string`, then type-check
  - `.json` / other → deserialize dag-json as `Node`, then type-check
* [ ] On success: print the resolved top-level type to stdout (using
      `debug::render_mono`), exit 0
* [ ] On type errors: print each error (with `debug::render_reason`) to stderr,
      still print inferred type to stdout, exit 1
* [ ] Integration tests (in `tests/cli_tests.rs`):
  - `--type-check` on a well-typed `.eyg` file → exit 0, prints type
  - `--type-check` on a well-typed `.json` file → exit 0, prints type
  - `--type-check` on an ill-typed file → exit 1, errors on stderr
  - `--type-check` combined with parse error → exit 1, parse error on stderr
  - `--type-check` with missing variable → exit 1, "missing variable" on stderr

---

## Milestone 10: End-to-End & Regression Tests

Comprehensive test coverage and cross-validation with the Gleam implementation.

* [ ] Data-driven test fixture `testdata/type_check_cases.json` with entries:
      `{ name, source, expected_type, expected_errors }` — source is EYG text,
      expected_type is the rendered top-level type string, expected_errors is a
      list of error substrings (empty for well-typed programs)
* [ ] Port all test cases from `contextual_test.gleam` into the fixture
      (≥15 cases covering: variables, literals, functions, let, polymorphism,
      lists, records, select, tags, builtins, perform, effects, handle)
* [ ] Test that existing interpreter tests still pass unchanged (no regressions)
* [ ] Verify `make check` passes (all workspace tests + clippy)
* [ ] Edge cases:
  - Empty program (Vacant) → type is a fresh variable, error `Todo`
  - Deeply nested let-polymorphism
  - Recursive type detection (occurs check)
  - Large programs with many type variables
