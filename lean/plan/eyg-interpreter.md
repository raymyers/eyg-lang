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

## Milestone 0 — Scaffolding & IR types  ✅ DONE

**Deliverable:** `Eyg/Ir/Tree.lean` compiles; the IR mirrors
`gleam_ir/.../tree.gleam` exactly and can represent every `source` node in the
spec fixtures.

- [x] Add an `Eyg.Interpreter`/`Eyg.Ir` namespace layout under `lean/Eyg/`.
      (`Eyg.Ir.Tree` namespace; file `lean/Eyg/Ir/Tree.lean`, wired into `Eyg.lean`.)
- [x] Define `inductive Expr (m)` with all 23 constructors from `tree.gleam`.
- [x] Define `Node m` and constructor helpers (`variable_`, `lambda`, …, plus
      composites `func/call/block/list/record/match_/get/tagged/true'/false'/
      add/subtract/multiply`) mirroring the Gleam smart constructors.
- [x] `Int` model: Lean `Int` + `Eyg.Ir.Integer.isSafe` (magnitude ≤ 2^53−1).
- [x] `deriving Repr, BEq, DecidableEq, Inhabited` + `native_decide`/`decide`
      smoke checks on hand-built terms.

**Notes / deviations actually taken:**
- `Node` is a **single-field `structure` in a `mutual` block with `Expr`**, not
  the planned `Expr m × m` `Prod` alias. Reason: Lean's `DecidableEq` deriving
  cannot see through `Prod` (nested inductive) and bails, but direct mutual
  recursion `Expr → Node → Expr` derives cleanly. `DecidableEq` is needed
  transitively by `Value` (M1), so it is established here. Projections are
  `Node.expr` / `Node.annotation` instead of `.1` / `.2`.
- Renames to dodge Lean reserved tokens: smart constructor `variable` →
  `variable_`, `let`/`case`/`match` helpers → `let_`/`case_`/`match_`,
  `true`/`false` → `true'`/`false'`; structure field `meta` → `annotation`.
- `Cid := String` (canonical CIDv1 string); references all fail with `Undefined*`
  for the spec so no richer model is needed yet.
- Local `Repr ByteArray` instance (core lacks one) so the tree can `deriving Repr`.

## Milestone 1 — Values, environments, continuations  ✅ DONE

**Deliverable:** `Value.lean` + the machine-state types compile as one mutual
inductive with derived structural equality.

- [x] `mutual inductive` block for `Value` / `Switch` / `Kontinue`
      (`Eyg/Interpreter/Value.lean`). `Stack` is **not** in the block — it is a
      `List (Kontinue m × m)` alias (see deviation below).
  - `Value`: `Binary, Integer, String, LinkedList (List Value),
    Record (List (String × Value)), Tagged, Closure (param) (body : Tree.Node)
    (env : Scope), Partial Switch (List Value)`.
  - `Switch`: all 11 cases; `Resume` carries
    `(frames : List (Kontinue m × m)) (env : Scope)` = state.gleam `Context(m)`.
  - `Kontinue`: `Arg, Apply, Assign, CallWith, Delimit … Bool, Trace`.
- [x] Aliases: `Scope := List (String × Value)`, `Env := Scope` (decision #1, no
      builtin dict), `Stack := List (Kontinue m × m)`,
      `Context := Stack × Scope`.
- [x] `deriving Repr, BEq, Inhabited`; helpers `unit, tag, true', false', bool,
      ok, error, some', none'` + record helpers `recordInsert/recordGet/mkRecord`.
- [x] `Break.lean`: `Reason` (12 cases) `deriving Repr, BEq, Inhabited`.
- [x] Record equality is order-insensitive — `native_decide` smoke checks pass.

**Notes / deviations actually taken:**
- **`BEq`, not `DecidableEq` (revision of decision #2).** `DecidableEq` deriving
  cannot see through `List`/`Prod` nesting, and `Value` recurses through `List`
  in four places (LinkedList, Record, Partial args, Closure/Resume env). The
  harness only needs **Bool** structural comparison, which `deriving BEq`
  provides and *does* derive through `List`. Prop-level `DecidableEq` is deferred
  (only needed for the semantics proofs in `eyg-semantics.md`); revisit there,
  e.g. via a hand-rolled instance or a direct-recursion list encoding.
- **Records kept canonical** (sorted-by-key, unique) via `recordInsert`/
  `mkRecord` so derived `BEq` is order-insensitive (decision #3). Every
  record-building site in M3/M4 must route through these.
- **`Stack` is a `List (Kontinue m × m)` alias**, matching Gleam's
  `Empty | Stack(k,meta,rest)` and the `do_perform`/`move` list accumulator; this
  also keeps `Stack` out of the mutual block.
- Reserved-token renames: `some`→`some'`, `none`→`none'`, `true`/`false`→
  `true'`/`false'`; `Reason` field `module`→`module_`; `Kontinue` field
  `then`→`then_`.

## Milestone 2 — Core CEK machine (no effects/builtins yet)  ✅ DONE

**Deliverable:** `State.lean` evaluates the pure lambda-calculus core; a
`partial def` loop runs `Variable/Lambda/Apply/Let/Integer/String/Binary` and
the `Vacant`/`Undefined*` error paths.

- [x] `Control := E Node | V Value`; `Next := Loop … | Break (Except Debug
      Value)`; `Debug := Reason × m × Env × Stack`. Also `EvalReturn`
      (`Except Debug …`, for `eval`/`apply`) and `Return` (`Except Reason …`,
      for `call`/`callBuiltin`/`perform`/`deep`) — see error-type discipline.
- [x] `eval` (`state.gleam:91`): all 23 nodes incl. literals, `Variable`
      lookup/`UndefinedVariable`, `Vacant`, reference `Undefined*`, and the
      `Builtin id` validity check via `isBuiltin` (decision #1).
- [x] `apply` (`state.gleam:137`): `Assign`/`Arg`/`Apply`/`CallWith`/`Delimit`/
      `Trace`.
- [x] `call` skeleton (`state.gleam:152`): `Closure` (bind, push `Trace`, enter
      body), generic `Partial` accumulation, `NotAFunction`. **Switch-specific
      arms are TODO(M3-M5)** — marked in the source above the catch-all.
- [x] `step`/`ofEvalReturn` (`state.gleam:76`), `partial def loop`, `execute`
      (`expression.gleam:26`), `resume` (`expression.gleam:10`).
- [x] Sanity `#guard`: identity application, `let`, currying, unbound-variable
      break — all pass at build time.

**Notes:** `meta` (a Lean reserved token) is spelled `ann` for the per-frame
metadata variable. `eval`/`apply` use a local `let res : Return …` then
`mapError` to attach `Debug`, matching the Gleam `result.map_error` boundary
exactly. `eval`/`apply`/`call` are `partial def` in one `mutual` block
(anticipating M5's `fix`-driven non-termination; only `loop` truly needs it).

## Milestone 3 — Structured values: records, variants, lists, matching  ✅ DONE

**Deliverable:** every structured-value `Switch` case in `call` is implemented;
the record/variant/list/pattern-match fixtures in `core_suite.json` pass.
(Suite-level validation lands in M6; M3 is checked by `#guard`s for now.)

- [x] Implemented `call`'s `Partial` arms (`state.gleam:160-207`): `Cons`
      (`Cast.asList`, prepend), `Extend`/`Overwrite` (`Cast.asRecord`,
      `recordInsert`; `Overwrite` requires existing field via `recordGet` else
      `MissingField`), `Select` (`recordGet`/`MissingField`), `Tag`→`Tagged`,
      `Match` (compare label, `call` branch vs otherwise), `NoCases`→`NoMatch`.
- [x] `Cast.lean` (`cast.gleam`): `asInteger/asString/asBinary/asList/asRecord/
      asTagged`, each `IncorrectTerm` on mismatch.
- [x] Arity accumulation verified: under-applied `Partial` stays `Partial` via
      the generic catch-all (`state.gleam:203`).
- [x] `#guard` checks: record select / missing-field break / overwrite (hit &
      miss) / list literal / variant match (hit & otherwise) — all pass.

**Notes:** `call`'s `Partial` block uses explicit `match` on `Cast` results
rather than `do`-notation — the `Return` abbrev fixes the `Except` success type,
so the do-monad couldn't be inferred (`Bind Return`). Builtins (M4) and effects
(M5) still fall through the catch-all and are marked `TODO` there.

## Milestone 4 — Builtins  ✅ DONE (pending suite validation in M6)

**Deliverable:** all 30 builtins implemented; `builtins_suite.json` passes
(modulo effects, M5). Suite validation lands in M6; M4 is `#guard`-checked.

- [x] `callBuiltin` (`State.lean`, in the `call` mutual block) replaces the
      env-stored dict (decision #1); arity via `Builtin.builtinArity`, under/over-
      applied → `Partial` (`state.gleam:214`). 26 pure builtins in
      `Builtin.run`; 4 stack-coupled (`fix/fixed/list_fold/binary_fold`) inline.
- [x] Arithmetic: `int_add/subtract/multiply` w/ `Integer.isSafe` →
      `Unrepresentable`; `int_divide` (0 → `Error unit`); `int_absolute`,
      `int_compare` (`Lt/Eq/Gt`), `int_parse` (malformed→`Error`, unsafe→
      `Unrepresentable`), `int_to_string`.
- [x] Strings: `append/split/split_once/replace/uppercase/lowercase/starts_with/
      ends_with/length/to_binary/from_binary`, incl. empty-pattern `split_once`
      and empty-`from` `replace` quirks (over **scalar values**, not graphemes —
      see notes).
- [x] Binary: `binary_from_integers/size/concat/compare/fold`.
- [x] Lists: `list_pop`, `list_fold` (continuation-stack frame layout
      reproduced; `binary_fold` likewise).
- [x] Recursion `fix`/`fixed`, `equal`, `never`.
- [x] `#guard`: int_add, partial under-application, overflow break, divide-by-0,
      int_to_string, string_append, equal, list_fold sum, **fix-based factorial
      4 = 24** — all pass.

**Notes / risks carried to M6 (where the fixtures decide):**
- **`[BEq m]` now threads through the machine** (`eval/apply/call/callBuiltin/
  step/loop/execute/resume`): `Value`'s derived `BEq` needs `[BEq m]`, and the
  `equal` builtin uses it. Harmless at `m = Unit`.
- **Unicode approximations** (Lean core lacks grapheme support): `string_length`
  counts scalar values not graphemes; `string_replace` empty-`from` / `string_
  uppercase`/`lowercase` use scalar/`Char` ops. May diverge from Gleam on
  non-ASCII fixtures — revisit if M6 fails.
- **`int_parse`** uses `String.toInt?`; confirm it matches Gleam `int.parse`
  (sign/leading-zero/`+` handling) against the fixtures.

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
