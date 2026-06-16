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
| `builtin.gleam` | `Builtin.lean` | the 30 builtins + default env |
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

## Milestone 5 — Algebraic effects: perform / handle / resume  ✅ DONE (pending M6)

**Deliverable:** deep-handler effect machinery works; `effects_suite.json`
passes including the resume-and-continue protocol. Suite validation in M6;
M5 is `#guard`-checked.

- [x] `perform`/`doPerform` (`state.gleam:239-260`): walk the stack to the
      nearest matching `Delimit`, accumulate the traversed prefix, build
      `Resume(prefix, env)`, reinstate `CallWith arg :: CallWith resume :: rest`;
      unmatched → `UnhandledEffect`.
- [x] `deep` (`state.gleam:263`): push `Delimit(label, handler, env, false)`,
      `call exec unit`.
- [x] `Resume` arm in `call` (`state.gleam:199`): `move` popped frames back onto
      `k`, continue with the supplied value.
- [x] `resume` driver (`expression.gleam:10`) already present (M2) for the
      harness reply step.
- [x] Shallow `Delimit … true` field kept for shape parity; only deep exercised.
- [x] `#guard`: abort handler (`\p.\r. p` ⟶ 1), **resume-and-continue**
      (`\p.\resume. resume 5` over `let x = perform "Get" unit in x + 10` ⟶ 15),
      unhandled effect ⟶ break — all pass.

The interpreter core (M2–M5) is now feature-complete; the remaining milestones
build the JSON spec harness (M6) and IR codec/CID (M7) that validate it against
the real `spec/` fixtures.

## Milestone 6 — Spec harness & evaluation suites GREEN  ✅ DONE — 104/104

**Deliverable:** a Lean harness that loads the three evaluation suites and
reproduces `interpreter_test.gleam`; **all fixtures pass**.

- [x] JSON via `Lean.Data.Json` (`Json.parse`, `getObjVal?`/`getStr?`/`getInt?`/
      `getArr?`; objects iterated through `.obj m |>.toList`).
- [x] IR decoder (`Eyg/Spec/Harness.lean` `decodeNode`) for the `{"0": code, …}`
      dag-json shape, incl. base64 (`decodeB64`) for `{"/":{"bytes":…}}` and the
      integer `isSafe` rejection.
- [x] Value decoder `{binary|integer|string|list|record|tagged}` (`decodeValue`).
- [x] Expectation decoder `{value}` vs `{break: {UndefinedVariable |
      UndefinedBuiltin | NotImplemented→Vacant}}` (`decodeExpectation`).
- [x] Effect-folding runner (`runFixture`): `execute`, then per expected effect
      require `Break (UnhandledEffect label lift)` and `resume reply env k`;
      finally compare value (`==`) or break reason.
- [x] `lake exe spec` target over all three suites; exits non-zero on any fail.
- [x] **DoD met:** `spec evaluation: 104/104 fixtures passed`.

**Notes:** two fixtures forced the Unicode work flagged in M4 — `string_split`
on an empty pattern returns grapheme clusters, and `string_length` counts
grapheme clusters. Added a combining-mark-aware `graphemes` helper in
`Builtin.lean` (covers the combining-diacritics ranges the fixtures use) and
routed both builtins through it. `string_split_once`/`string_replace`
empty-pattern quirks already passed (ASCII fixtures).

## Milestone 7 — IR codec & `ir_suite.json` (encode / decode / CID)  ✅ DONE — 21/21 CID

**Deliverable:** dag-json round-trips and CIDs match `ir_suite.json`.

- [x] Encoder + decoder mirroring `dag_json.gleam` (in `Eyg/Spec/Harness.lean`:
      `decodeNode`/`encodeNode`); every fixture `source` decodes and
      `decode ∘ encode` round-trips (21/21).
- [x] `Eyg/Ir/Cid.lean`: canonical block encoding (`toBlock`, via
      `Json.compress` over a sorted-key object) → CIDv1. **Chose option (a):**
      a from-scratch Lean **SHA-256** (FIPS 180-4, verified against the
      `"abc"`/empty test vectors), plus base32-lower, LEB128 varint, the
      sha2-256 multihash, and the dag-json codec `0x0129` → multibase `b…`.
- [x] **DoD met:** `ir round-trip: 21/21 | CID match: 21/21`.

**Notes:** the canonical dag-json bytes fall out of `Lean.Json.compress`, whose
backing object is a `Std.TreeMap` ordered by `String.compare` — bytewise, which
matches dag-json key ordering for the IR's single-ASCII-char node keys (and the
nested single-key bytes/CID objects). Hand-verified the version+codec varint
prefix decodes to the `baguqeera…` base32 head before running the suite.

---

## Definition of done  ✅ ALL MET

- [x] `lake build` clean; `Eyg/Interpreter/*` mirrors the Gleam modules
      (`Tree`, `Value`, `Break`, `Cast`, `Builtin`, `State`; drivers `execute`/
      `resume` in `State`).
- [x] The Lean harness passes **every** fixture in
      `spec/evaluation/{core,builtins,effects}_suite.json` — **104/104**
      (`lake exe spec`).
- [x] `ir_suite.json` round-trips (21/21) **and** CIDs match (21/21).
- [x] Each Lean module opens with a header pointing at the Gleam file it mirrors.

**How to run:** `cd lean && lake exe spec` →
`spec evaluation: 104/104 fixtures passed` /
`ir round-trip: 21/21 | CID match: 21/21` (exit 0).

## Milestone 8 — Post-completion cleanup  🔶 IN PROGRESS (review findings)

A diff review of M0–M7 (`559ae428^..c53d36ba`) re-ran the suite — **104/104 and
21/21 CID confirmed, exit 0** (note: the first attempt was a false pass — macOS
lacks `timeout`, so `lake exe spec` never ran; verify by reading the printed
counts, not just the exit code). The port is otherwise a clean, faithful mirror.
The following minor items are non-blocking but worth tidying:

- [x] **Two sources of truth for the builtin set.** Collapsed: `isBuiltin` is now
      `(Builtin.builtinArity id).isSome` (`State.lean`) and the duplicate
      `builtinNames` list is deleted. `builtinArity` (`Builtin.lean`, mirroring
      Gleam's `builtin.all`) is the single source. Suite still 104/104 + 21/21.
- [x] **Stale comments referencing "M7 part B" as future work.** Fixed both:
      the `encodeB64` doc and the IR-suite comment in `Harness.lean` now describe
      CID equality as implemented (it is, and the runner reports `CID match`).
- [x] **Doc nit:** source-of-truth table now reads "the 30 builtins" (26 pure +
      4 stack-coupled), matching the code.
- [ ] **(optional) `move` is `List.reverseAux`.** `State.lean:85` hand-rolls
      `frames.reverse ++ k`. Kept for one-to-one parity with Gleam's `state.move`;
      fine to leave, but a one-liner alias would do.
- [ ] **(low-confidence) `binary_from_integers` negative inputs.**
      `Builtin.lean:183` uses `UInt8.ofNat (i.toNat % 256)`; `Int.toNat` clamps
      negatives to 0, so a negative element becomes byte 0 rather than wrapping
      mod 256. No fixture exercises negatives, so unverified against Gleam —
      confirm the intended truncation semantics if negatives are ever in scope.

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
