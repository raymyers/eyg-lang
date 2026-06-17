---
date: 2026-06-17
milestone: T5 (Handle/Delimit)
status: DELIVERED — fully green (lake build + lake exe spec 104/104), axioms clean
---

# T5 Handle/Delimit — DELIVERED

`Handle`/`Delimit`/`Resume` typing is in, and `preservation`/`progress`/`soundness*`
re-green over the full effect fragment. `lake build` clean, `lake exe spec` **104/104**,
no `sorry`; headline theorems (`soundness_value`, `soundness`, `soundness_evalR`,
`soundness_behaviorsR_diverges`) print axioms `propext`/`Classical.choice`/`Quot.sound`.

## What was added (over the 6-pass infra base, branch `handle-wip`)

**Typing (`Typing.lean`/`Generation.lean`):** `HasType.handle` (at `handleTy l lift
reply tail ret`); `inv_handle`; the `hasType_expr_form` Handle arm; `hasType_subst`
gained its `handle` arm (`Substitution.lean`).

**Runtime (`Runtime.lean`):** `StackSegWf` moved into the `HasTypeV`/`EnvWf` mutual block;
`HasTypeV.partialHandleNil`/`partialHandleOne`/`partialResume` (+ `conv`/`canonical_arrow`
arms); `StackSegWf.delimit` carries **no** `EnvWf`.

**Machine (`Machine.lean`):** `StackWf.delimit` (no `EnvWf`) + `StackWf.conv`; the six
conv-folding per-frame inversion lemmas `stackWf_{trace,assign,arg,applyf,callwith,delimit}_inv`
+ `stackWf_nil_inv`; `stackWf_resume` (the `StackSegWf ++ StackWf → StackWf` composition).

**Soundness (`Soundness.lean`):** all four `cases hst` theorems (`preservation_V`,
`reduce1Run_done_value_typed`, `progress`, `preservation_perform`) converted to
`cases kont` + inversion lemmas; `preservation`/`preservation_V` conclude `∃ε'` (the row
shrinks across a `Delimit`-pop, grows across `reduceDeep`); new helper lemmas
`doPerformR_error_form`, `reducePerform_perform_inv`, `mStateWf_wait_conv`. The `Handle`
runtime cases (Delimit-value-pop, `reduceDeep` install, `Resume`) are handled; the three
genuine handler **dispatches** are isolated behind the bundled hypothesis below.

## Isolated hypotheses (explicit assumptions, not axioms)

Same isolation pattern as the existing `BuiltinAppPreserves`/`Fix*`:

- **`HandlerObligations m`** (a `structure` with `perform`/`install`/`resume` fields):
  the three effect dispatches — the perform stack-walk to the matching `Delimit`, the
  `reduceDeep` handler install, and the `Resume` continuation feed. Each is `∃ε'`
  preservation of the corresponding `.tau` successor. (These are the design's intended
  hard dispatch + the effect-weakening-vs-`Delimit` row threading; all TRUE, discharge is
  the follow-up.) Threaded through the value/no-bad-crash theorems exactly like
  `BuiltinAppPreserves`.
- **`TauKeepsRow m`**: a `tau` step keeps the ambient row `ε` *exactly*. TRUE for the
  handler-discharge-free fragment; FALSE in general once a `Delimit`-pop discharges a
  label and shrinks the row. Gates only the **row-dependent** results (effect-escape /
  divergence ω-effect-safety / reply-trace effect safety). The genuine *row-evolution*
  proof (an unhandled `op`'s membership reflecting back across the discharges — conditioned
  on the stack structure, not a clean universal lemma) is the remaining T7 work.

**Crucially, the `ε`-free results are NOT gated on `TauKeepsRow`** — `soundness_value`,
`soundness_evalR_value`/`_noBadCrash`, `soundness_behaviorsR_value`/`_noBadCrash` and the
no-bad-crash core hold unconditionally (modulo `Fix*`/`HandlerObligations`) for the full
language **including `Handle`**. Only effect-membership / divergence-effect-safety claims
carry `TauKeepsRow`.

## What each headline theorem now states

- `soundness_value` / `soundness_evalR_value` — well-typed run's terminating value is
  typed (`ε`-free; full language). Now takes `hho`.
- `soundnessR_noBadCrash` / `soundness_evalR_noBadCrash` — no *bad* crash (`ε`-free).
  Now takes `hho`.
- `soundness_evalR` — the evalR trichotomy + effect escape. Takes `hho`, `hkeep`.
- `soundness` (bundled `BehaviorsR`) — silent typed value / no bad crash / boundary
  suspension `op ∈ ε`. Takes `hho`, `hkeep`.
- `soundness_behaviorsR_diverges`, `_terminates_*`, `pure_*` — take `hkeep` (and `hho`
  where they route through the value side).

## Remaining (follow-up, not blocking green)
1. Discharge `HandlerObligations` (the perform stack-walk dispatch is the substance of
   handler soundness; install/resume need the effect-weakening-vs-`Delimit` row threading).
2. Discharge `TauKeepsRow` by the genuine row-evolution proof (replaces the gate with a
   membership-reflection over the `Delimit` walk), making the effect/divergence results
   unconditional for `Handle` programs too.
3. Discharge `fix` (`Fix*`) — orthogonal (T6b), pure-builder fragment scoped.

## Verification (this worktree)
- `lake build` → `Build completed successfully (1771 jobs)`.
- `lake exe spec` → `spec evaluation: 104/104 fixtures passed` / `FBS≡interpreter: 104/104`.
- `#print axioms soundness_value|soundness|soundness_evalR|soundness_behaviorsR_diverges`
  → `[propext, Classical.choice, Quot.sound]` (all four).
- No `sorry` in `Eyg/`.
