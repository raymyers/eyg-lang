---
date: 2026-06-17
milestone: T6b
status: delivered (partial — `fixed` re-application done; `fix` creation still a hypothesis)
---

# T6b: `partialFixed` rule + `fixed` re-application preservation

## What was delivered (green, sorry-free, axioms clean, spec 104/104)

The internal `fixed` partial that `fix` produces is now **typed** and its
**re-application** (the `fix` unrolling `fix builder = builder (fix builder)`) is
**proven** to preserve typing. Concretely:

- **`HasTypeV.partialFixed`** (`Runtime.lean`) — the bespoke rule for
  `.Partial (.Builtin "fixed") [builder]` (which has no `partialBuiltin` typing,
  `Builtins.scheme "fixed" = none`):
  ```
  partialFixed {builder D γ R τ} :
    HasTypeV builder (.fun (.fun D γ R) .empty (.fun D γ R)) →
    Ty.TyEquiv (.fun D γ R) τ →
    HasTypeV (.Partial (.Builtin "fixed") [builder]) τ
  ```
  i.e. the fixpoint value inhabits the recursion arrow `D →⟨γ⟩ R`; the builder is a
  **pure** (`∅`-latent) `(D→⟨γ⟩R) →⟨∅⟩ (D→⟨γ⟩R)`.
- The full **`HasTypeV` cascade**: `conv`, `canonical_arrow`, and the seven
  `cases hf`/`cases hv`/`cases hw`/`cases hp` sites across `preservation_V`,
  `reduce1Run_done_value_typed`, `progress`, `reduceCall_perform_wait`,
  `builtinAppPreserves`, `builtinAppNoBadCrash` — each gains a `partialFixed` arm
  (the re-application in the two preservation sites; a contradiction/exhibit-step
  elsewhere).
- **`reduceCall_fixed`** (`rfl`) + **`fixed_reapply_preserves`** (the shared lemma):
  feed `fixed builder : D→⟨γ⟩R` into the pushed `Apply builder :: CallWith arg`
  frames — `Apply builder` weakens via `effWeaken_empty` (pure builder), `CallWith
  arg` uses the calling frame's `hw : EffWeaken γ ε`. The builder is `conv`-ed to the
  frame's exact arrow form (`congrFun he _ he`), sidestepping any stack-endpoint
  conversion (resolves original finding 2).
- **Constraint A** (from `2026-06-16-T6b-fix-scoping.md`): added the
  `Ty.EffWeaken εf ε` premise to `BuiltinAppPreserves` **and** `FixPreserves`, threaded
  the calling frame's `hw` at every `hsat`/`hfix` call site. The general-builtin
  discharge ignores it (the arity drivers never read the function latent);
  `BuiltinAppNoBadCrash`/`FixNoBadCrash` needed no change (fix/fixed never crash).

## ⚠ Key correctness finding — `partialFixed` **must** restrict to an arrow fixpoint

The first attempt typed the fixpoint at an arbitrary `α` (mirroring the gleam scheme
`fix : (q0→⟨q1⟩q0)→⟨q1⟩q0` with `q0` free). This is **unsound** and broke every
canonical-forms lemma:

- A `fixed` value is a `.Partial`; typing it at `α := .integer` would make
  `canonical_integer` (a value at `.integer` is an `.Integer`) **false**.
- Operationally, `fix (\x. int_add x 1) : Int` is well-typed under the raw scheme but
  **crashes**: the `fixed` Partial is bound where an `Int` is expected and the
  `int_add` cast fails (a *bad* crash on a well-typed program — a soundness
  violation).

So `α` is pinned to `.fun D γ R`. `fix` is operationally sound only at arrow fixpoints
(a base-type fixpoint either diverges or cast-crashes); the arrow restriction both
keeps the canonical lemmas valid and excludes the footgun. This is a sound,
conservative narrowing (covers all real recursion: the recursive *function* `D→⟨γ⟩R`
may still be effectful when called).

## What remains — `fix` **creation** (`FixPreserves`/`FixNoBadCrash`) is still a hypothesis

`FixPreserves` is about `reduceCall (.Partial (.Builtin "fix") applied) arg` (the
saturation that *creates* `fixed builder`). It is **not** discharged here, and the
headline theorems still take it (and `FixNoBadCrash`) as hypotheses. Why creation is
still blocked for the *general* case:

- At creation (`applied = []`), the fix-partial is typed via `partialBuiltin` with the
  scheme instantiation `(A→⟨B⟩A)→⟨B⟩A`, so the builder `arg : A→⟨B⟩A` has latent
  `B = εf`, **arbitrary** (gleam's `q1` is a free row var — effectful builders are
  typeable, `contextual.gleam:530`).
- Building the successor's `partialFixed` requires the builder **pure** (`B = ∅`).
  For general `B` this is unprovable — exactly the general-row-subsumption gap (Open
  Question 3).

**Net effect of this slice:** `FixPreserves` is now a *satisfiable, pure-builder-
inhabitable* hypothesis (the successor it asserts well-typed genuinely is, via
`partialFixed`) rather than the previously *vacuous* one (a `fixed` value had no
typing at all). The novel `fixed`-re-application metatheory — the genuinely hard part
flagged as "effect-threading, not mechanical plumbing" in the scoping note — is done.

## Recommended next step to fully discharge `fix`

Two routes (the planner decision (i)/(ii) from `2026-06-16-T6b-fix-scoping.md`):

- **(i) pure-builder narrowing** — pin the `fix` *scheme* to `⟨1, (q0→⟨∅⟩q0)→⟨∅⟩q0⟩`
  (builder latent `= ∅`). Then creation's `εf = ∅` by construction, `partialFixed` is
  buildable, and `FixPreserves`/`FixNoBadCrash` discharge **unconditionally** for the
  pure-builder fragment — making the headline soundness theorems drop the `Fix*`
  hypotheses. Cost: our `fix` types strictly fewer programs than gleam (forbids
  builders that perform *while constructing* the recursive function — not standard
  recursion). Touches `Scheme.scheme`, `scheme_cases`, and the `fix` arm of
  `builtinAppPreserves`. A documented, sound, but analyzer-divergent narrowing.
- **(ii) general row-variable subsumption** (`EffSub'`, substitution-stable) — the
  cleaner end state; discharges `fix` *and* a realistic effectful fragment without
  narrowing the scheme. The open research piece (Open Question 3).

Either is a self-contained follow-up; the `partialFixed` infrastructure they both need
is now in place.
