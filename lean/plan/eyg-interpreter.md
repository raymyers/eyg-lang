---
name: eyg-interpreter-plan
description: Plan to port the EYG reference interpreter to Lean 4, passing every spec/ test suite
date: 2026-06-16
---

# EYG Interpreter in Lean — Implementation Plan

## Goal

Build a Lean 4 interpreter for EYG that behaves **identically** to the Gleam
reference interpreter, structured the same way (both are pure: a CEK-style
state machine threaded through a step loop). "Identical" is pinned down
operationally: **every fixture in `spec/` must pass**, checked by a Lean port
of the Gleam test harness.

This is the executable workhorse. The companion document
[`eyg-semantics.md`](./eyg-semantics.md) builds the *formal* semantics (a
fuel-indexed functional big-step interpreter wired into the cslib transition
system) and proves it agrees with this interpreter. See
[`eyg-difference-semantics.md`](./eyg-difference-semantics.md) for the design
rationale behind the two-artifact approach.

## Source of truth

The Lean port mirrors these Gleam modules one-for-one:

| Gleam (`packages/gleam_interpreter/src/eyg/interpreter/`) | Lean (`Eyg/Interpreter/`) | Role |
|---|---|---|
| `../ir/tree.gleam` (`gleam_ir`) | `Eyg/Ir/Tree.lean` | IR expression type |
| `value.gleam` | `Value.lean` | runtime values + `Switch` |
| `break.gleam` | `Break.lean` | failure reasons |
| `cast.gleam` | `Cast.lean` | value coercions used by builtins |
| `state.gleam` | `State.lean` | CEK machine: `step`/`eval`/`apply`/`call`/`perform`/`deep` |
| `builtin.gleam` | `Builtin.lean` | the 29 builtins + default env |
| `expression.gleam` | `Expression.lean` | `execute`/`resume`/`call` drivers |

Test data (the contract): `spec/evaluation/{core,builtins,effects}_suite.json`,
`spec/ir_suite.json`. The harness to replicate is
`packages/gleam_interpreter/test/eyg/interpreter_test.gleam` and
`packages/gleam_ir/test/eyg/ir/dag_json_test.gleam`.

## Key design decisions (deviations from the Gleam shape)

These exist because Lean's kernel rejects what Gleam happily allows; each keeps
observable behavior identical.

1. **Builtins dispatched by name, not stored in the environment.** Gleam stows
   a `Dict(String, Builtin)` of *functions* inside `Env` (`state.gleam:42`) to
   dodge a module cycle. In Lean a function whose codomain mentions `Value`
   cannot live inside the `Value`/`Env` inductive (non-strict-positivity). So
   `Env` collapses to just `Scope = List (String × Value)`, and builtins are
   resolved by their identifier string through a single total
   `callBuiltin : String → List Value → …`. `ir.Builtin id` is valid iff `id`
   is in the known set (matches `UndefinedBuiltin`).
2. **First-order `Value` ⇒ derivable `DecidableEq`.** With builtins out of the
   env, `Value`, `Kontinue`, and `Stack` form one `mutual inductive` block with
   no function fields, so equality is decidable — required because the harness
   compares result values structurally.
3. **Records compared order-insensitively.** Gleam `Record` is a `Dict`. Use a
   representation with canonical equality (sorted-assoc list, or `Std.TreeMap
   String Value`) so `{a:1, b:2}` and `{b:2, a:1}` are equal, matching
   `should.equal` on Gleam dicts.
4. **Metadata is `Unit` for the spec.** `ir.Node(m)` is metadata-generic; every
   fixture uses `Nil`. Model `Expr` with a metadata type parameter but
   instantiate at `Unit` for the runner. (`Trace`/`Delimit` carry `meta`; keep
   the field so the machine shape matches, even though `Unit` makes it inert.)
5. **Two evaluation drivers.** A `partial def` step-loop is the runnable
   interpreter that makes the suites green (no termination obligation — EYG has
   `fix`). The total fuel-indexed version is built in `eyg-semantics.md` and
   proved to agree.

---

## Milestone 0 — Scaffolding & IR types

**Deliverable:** `Eyg/Ir/Tree.lean` compiles; the IR mirrors
`gleam_ir/.../tree.gleam` exactly and can represent every `source` node in the
spec fixtures.

- [ ] Add an `Eyg.Interpreter`/`Eyg.Ir` namespace layout under `lean/Eyg/`.
- [ ] Define `inductive Expr (m)` with all constructors from `tree.gleam`:
      `Variable, Lambda, Apply, Let, Binary (ByteArray), Integer (Int),
      String, Tail, Cons, Vacant, Empty, Extend, Select, Overwrite, Tag, Case,
      NoCases, Perform, Handle, Builtin, ContentReference, ReleaseReference,
      RelativeReference`.
- [ ] Define `Node m := Expr m × m` and constructor helpers (`variable`,
      `lambda`, …) mirroring the Gleam smart constructors.
- [ ] Decide `Int` model: EYG ints are native machine ints with a target
      "safe range" guard (`gleam_ir/.../integer.gleam`). Use Lean `Int` plus an
      `Integer.isSafe : Int → Bool` (magnitude ≤ 2^53−1) so overflow yields
      `Unrepresentable`, matching JS-target behavior the spec encodes.
- [ ] `#eval`/`deriving Repr, BEq` smoke check on a hand-built term.

## Milestone 1 — Values, environments, continuations

**Deliverable:** `Value.lean` + the machine-state types compile as one mutual
inductive with derived `DecidableEq`.

- [ ] `mutual inductive` block for:
  - `Value`: `Binary, Integer, String, LinkedList (List Value),
    Record (record repr), Tagged (String) Value, Closure (param) (body : Node)
    (captured : Scope), Partial Switch (List Value)`.
  - `Switch`: `Cons, Extend String, Overwrite String, Select String, Tag String,
    Match String, NoCases, Perform String, Handle String, Resume Context,
    Builtin String` (`value.gleam:20`).
  - `Kontinue`: `Arg (Node) (Scope), Apply Value Scope, Assign String (Node)
    Scope, CallWith Value Scope, Delimit String Value Scope Bool, Trace Value`
    (`state.gleam:63`).
- [ ] Type aliases: `Scope := List (String × Value)`,
      `Stack := List (Kontinue × m)` (Gleam's `Empty | Stack(k,meta,rest)`),
      `Context := Stack × Scope` (the captured resumption inside `Resume`).
- [ ] `deriving DecidableEq, Repr`; add `unit`, `true`, `false`, `ok`, `error`,
      `some`, `none`, `tag` helpers from `value.gleam`.
- [ ] Confirm record equality is order-insensitive (decision #3).

## Milestone 2 — Core CEK machine (no effects/builtins yet)

**Deliverable:** `State.lean` evaluates the pure lambda-calculus core; a
`partial def` loop runs `Variable/Lambda/Apply/Let/Integer/String/Binary` and
the `Vacant`/`Undefined*` error paths.

- [ ] `Control := E (Node) | V Value`; `Next := Loop Control Scope Stack |
      Break (Except Debug Value)`; `Debug := Reason × m × Scope × Stack`.
- [ ] `eval` (one expr → next config), mirroring `state.gleam:91`: `Lambda`→
      `Closure`, `Apply`→push `Arg`, `Let`→push `Assign`, `Variable`→scope
      lookup or `UndefinedVariable`, literals → `V`, `Vacant`→`Vacant`,
      reference nodes → the matching `Undefined*` reasons.
- [ ] `apply` (value meets a frame), mirroring `state.gleam:137`: `Assign`,
      `Arg`→push `Apply`, `Apply`/`CallWith`→`call`, `Delimit`/`Trace`→
      pass-through.
- [ ] `call` skeleton (`state.gleam:152`): `Closure`→bind param, push `Trace`,
      enter body; `Partial(switch, applied)` accumulation; `term`→
      `NotAFunction`.
- [ ] `partial def loop`/`step` (`state.gleam:76`) + `execute`
      (`expression.gleam:26`).
- [ ] Sanity `#eval`: identity application, `let`, currying produce the right
      `Value`.

## Milestone 3 — Structured values: records, variants, lists, matching

**Deliverable:** every `Switch` case in `call` is implemented; the
record/variant/list/pattern-match fixtures in `core_suite.json` pass.

- [ ] Implement `call`'s `Partial` cases exactly as `state.gleam:160-207`:
      `Cons` (prepend, `cast.as_list`), `Extend`/`Overwrite` (`cast.as_record`,
      `Overwrite` requires existing field → else `MissingField`), `Select`
      (`MissingField` on absent), `Tag`→`Tagged`, `Match` (compare label, call
      branch vs otherwise), `NoCases`→`NoMatch`.
- [ ] Port `Cast.lean` (`cast.gleam`): `asInteger/asString/asBinary/asList/
      asRecord/asTagged/...`, each producing `IncorrectTerm`/`MissingField` on
      mismatch.
- [ ] Verify arity accumulation: a `Partial` under-applied stays `Partial`
      (`state.gleam:203`).

## Milestone 4 — Builtins

**Deliverable:** `Builtin.lean` implements all 29 builtins; `builtins_suite.json`
passes (modulo effects, which land in M5).

- [ ] `callBuiltin : String → List Value → m → Scope → Stack → Return`
      replacing the env-stored dict (decision #1); arity handling like
      `call_builtin` (`state.gleam:214`): under-applied → `Partial`.
- [ ] Arithmetic: `int_add/subtract/multiply` with `Integer.isSafe` guard →
      `Unrepresentable` on overflow; `int_divide` (0 → `Error(unit)`);
      `int_absolute`, `int_compare` (→ `Lt/Eq/Gt` tags), `int_parse`
      (malformed → `Error`; out-of-range → `Unrepresentable`), `int_to_string`.
- [ ] Strings: `string_append/split/split_once/replace/uppercase/lowercase/
      starts_with/ends_with/length/to_binary/from_binary`. **Match the
      cross-target quirks the Gleam code documents**: empty-pattern
      `split_once` (`builtin.gleam:167`) and empty-`from` `replace`
      (`builtin.gleam:191`) — the fixtures encode these.
- [ ] Binary: `binary_from_integers/size/concat/compare/fold`.
- [ ] Lists: `list_pop`, `list_fold` (note `list_fold`/`binary_fold` build a
      continuation stack rather than recursing — `builtin.gleam:288,357`;
      reproduce the frame layout so effects performed inside the folded fn
      surface correctly).
- [ ] Recursion: `fix`/`fixed` (`builtin.gleam:24-43`), `equal`, `never`.
- [ ] String `length` semantics: confirm grapheme vs code-point counting
      matches Gleam `string.length`; pick the model the fixtures expect.

## Milestone 5 — Algebraic effects: perform / handle / resume

**Deliverable:** deep-handler effect machinery works; `effects_suite.json`
passes including the resume-and-continue protocol.

- [ ] `perform`/`do_perform` (`state.gleam:239-260`): walk the stack to the
      nearest `Delimit` frame with a matching label, accumulate the traversed
      prefix, build `Resume((prefix, env))`, and reinstate
      `CallWith(arg) :: CallWith(resume) :: rest`. Unmatched → `UnhandledEffect`.
- [ ] `deep` (`state.gleam:263`): push `Delimit(label, handler, env, False)`,
      call `exec` with `unit`.
- [ ] `Resume` case in `call` (`state.gleam:199`): `move` the popped frames back
      onto `k` and continue with the supplied value.
- [ ] `resume` driver (`expression.gleam:10`) for the harness's reply step.
- [ ] Note: shallow handlers (`Delimit … True`) are stubbed in Gleam; keep the
      field but only deep is exercised by the suite.

## Milestone 6 — Spec harness & evaluation suites GREEN

**Deliverable:** a Lean test that loads the three evaluation suites and the
harness reproduces `interpreter_test.gleam` exactly; **all fixtures pass**.

- [ ] JSON: use `Lean.Json` (or Std) to parse the fixture files.
- [ ] IR decoder for the `{"0": code, …}` dag-json node shape
      (`spec/README.md:44-92`) → `Node Unit`.
- [ ] Value decoder for `{binary|integer|string|list|record|tagged}`
      (`interpreter_test.gleam:31`).
- [ ] Expectation decoder: `{value: …}` vs `{break: {UndefinedVariable |
      UndefinedBuiltin | NotImplemented→Vacant}}` (`interpreter_test.gleam:108`).
- [ ] Effect-folding harness (`interpreter_test.gleam:182`): run `execute`; for
      each expected effect assert `Break(UnhandledEffect(label, lift))`, then
      `resume(reply, env, k)`; finally compare to the expectation.
- [ ] Wire as a `lake test` target (or `#eval`-based assertion script) over
      `core_suite`, `builtins_suite`, `effects_suite`.
- [ ] **DoD:** zero failures across all three suites.

## Milestone 7 — IR codec & `ir_suite.json` (encode / decode / CID)

**Deliverable:** dag-json round-trips and CIDs match `ir_suite.json`.

- [ ] `Eyg/Ir/DagJson.lean`: encoder + decoder mirroring
      `gleam_ir/.../dag_json.gleam`; assert decode∘encode round-trips and that
      decoding every fixture `source` succeeds.
- [ ] `Eyg/Ir/Cid.lean`: canonical block encoding (`to_block`) → CIDv1.
      **Hard part / sequence last:** computing the `cid` strings needs SHA-256
      + multihash + CIDv1 + base32 (`gleam_ir/.../cid.gleam`). Options, in order
      of preference: (a) find/port a Lean SHA-256; (b) treat `Sha256` as an
      injected effect like Gleam does and feed precomputed digests; (c) defer
      CID-string equality and only verify structural round-trip first.
- [ ] **DoD:** `ir_suite.json` CIDs reproduced (or, if deferred, round-trip +
      decode coverage green with CID equality tracked as a follow-up).

---

## Definition of done

- `lake build` clean; `Eyg/Interpreter/*` mirrors the Gleam modules.
- The Lean harness passes **every** fixture in
  `spec/evaluation/{core,builtins,effects}_suite.json`.
- `ir_suite.json` round-trips; CIDs match (or the gap is explicitly tracked).
- A short `notes/`-style header in each Lean module points at the Gleam file it
  mirrors, so drift is reviewable.

## Risks / watch-list

- **Non-termination:** `fix`/`list_fold` mean no structural recursion — the
  runnable interpreter is `partial def`. Totality lives in `eyg-semantics.md`.
- **Record equality** must be canonical (decision #3) or value comparisons
  spuriously fail.
- **Cross-target string/int quirks** are deliberately baked into fixtures;
  porting the stdlib calls naively will fail those cases — follow the comments
  in `builtin.gleam`.
- **CID hashing** is the only piece needing crypto; keep it isolated so the
  evaluation suites (the real interpreter contract) aren't blocked on it.
