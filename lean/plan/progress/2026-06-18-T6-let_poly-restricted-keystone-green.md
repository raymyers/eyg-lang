---
date: 2026-06-18
milestone: T6 — restricted `let_poly`: typing layer + readiness keystone GREEN (per-file); only StackWfV engine coupling remains
status: WIP (gen branch builds green; Soundness needs the StackWfV coupling; saved as a patch)
---

# Restricted `let_poly` — typing layer + readiness keystone are GREEN; engine coupling is all that's left

Executing the restricted-`let_poly` route (the `2026-06-18-T6-let_poly-instantiation-levelmap-gap.md`
finding: forbid nested let-generalization in the generalized body, so `hasType_subst` stays arbitrary-σ
with vacuous `Let` arms). **The entire gen branch now builds green per-file**; the only red module is
`Soundness.lean`, which needs the value-aware `StackWfV` coupling. Saved as
`2026-06-18-T6-let_poly-cascade-WIP.patch` (379 lines, applies on the infra commits).

## Green per-file (in the WIP patch)

- **`Tree.lean`** — `Node.noLet` (structural: no `Let` node anywhere), the value-restriction guard.
- **`Scheme.lean`** — relocated `Ty.genArity`/`reindexGen`, `Scheme.genAt`/`genAt_arity`/`freeVars`/
  `freeVars_mono` (so the constructor can name `genAt`).
- **`Typing.lean`** — `CtxWf`; the **`HasType.let_poly`** constructor (premises: lambda typing, `CtxWf n Γ`,
  **`Node.noLet lbody`**, body-at-`genAt n defnTy`); `ctxWf_ctxConv` + the `hasType_ctxConv` `let_poly` arm.
- **`Generation.lean`** — `inv_let` unified to a mono/poly disjunction (poly exposes `noLet`);
  `hasType_expr_form` arm.
- **`Substitution.lean`** — `hasType_subst` re-stated with `(hnl : Node.noLet e)`: the `let_`/`let_poly`
  arms are **vacuous** (`simp [Node.noLet] at hnl` ⇒ `False`); all other arms unchanged (arbitrary σ).
  `closure_typed_of_lambda_subst` threads `noLet`; the unused `hasTypeV_subst_closure` deleted.
- **`Generalization.lean`** — `generalizes_closure_ready`/`genAt_closure_ready` thread `noLet`. **The
  readiness keystone is complete**: `genAt_closure_ready hΓ hnl henv hlam : ∀ args, HasTypeV (Closure …)
  ((genAt n defnTy).instantiate args)` — green, no `LevelMap`/`WfLevel` needed (the finding's payoff).

## All that remains: the `StackWfV` two-engine coupling (`Soundness.lean`)

Three red sites (`weakenEffAux:52` already fixed in the patch; the two `inv_let` consumers at
`:204`/`:2728` are the Let-push of each engine). The wall (re-confirmed this session): at the Assign-**pop**
the incoming `val` is generic (`HasTypeV val defnTy`), but the poly `EnvWf.cons` needs
`∀ args, HasTypeV val ((genAt n defnTy).instantiate args)` — readiness about *this* `val`, not derivable
from `val : defnTy`. So the closed `Rdy` (from `genAt_closure_ready` at the push, about
`Closure lx lbody fenv`) must be **carried** to the pop in a value-aware stack predicate. Checklist
(unchanged from the coupling design, now atop the green keystone):

1. **`StackWf.assign`** → store an arbitrary scheme `s` (mono = `.mono defnTy`); update its inversion +
   `stackSeg_toStackWf`'s assign arm.
2. **`StackWfV v k …`** (value-aware: `assign` carries `∀ args, HasTypeV v (s.instantiate args)`; `trace`
   recurses; other heads drop to `StackWf`; `conv` folds) + `stackWfV_toStackWf` + inversions.
3. **`MStateWf`** value case → `∃ τin, HasTypeV v τin ∧ StackWfV v k τin ε τ`; the E-case carries `Rdy`
   about the closure the control will become (a control-aware clause or `StackWfE`) across the
   lambda→closure step.
4. Re-green **`preservation_E`** (Let-push builds the poly Assign frame + computes `Rdy` via
   `genAt_closure_ready`; lambda-step hands `Rdy` to `StackWfV`), **`preservation_V`** (Assign-pop reads
   `Rdy`, feeds `EnvWf.cons`), **`progress`**; every `.V`-producing arm now wraps `StackWfV` (trivial for
   non-assign heads). **Mirror in the B engine** (`StackWfVB`).
5. Polymorphic-reuse `example`: `let id = \x.x in pair (id 1) (id "a")`.

This is the Handle-sized engineering piece (no green intermediate — the constructor breaks both engines at
once). The design is fully settled and the keystone it depends on is green; it is pure mechanical coupling.
Tree green at HEAD (`.lean` working changes stashed into the patch).

## ⚠ `StackWfV` design refinement — the forgetful-map soundness point (resolved)

Working the `StackWfV`↔`StackWf` relationship surfaced a subtlety worth pinning before the grind:

- **`StackWf.assign` must store a *scheme* `s`** (mono = `.mono defnTy`), as the forgetful target of
  `StackWfV.assign`. It is the **structural** (weaker) claim — it does **not** assert the incoming value is
  ready for `s`. (A poly→mono fold is *unsound*: scheme-binding specialization `body:(x,s) ⊢ → body:(x,.mono (s.inst args))` is **false** — the body may use `x` at other instances. So the forgetful map must keep the scheme, not specialize it.)
- **`StackWfV.assign` adds the value-specific readiness** `∀ args, HasTypeV v (s.instantiate args)`. This is
  the only sound carrier of the binding obligation (it is exactly the false-for-generic-`v` value-subst
  lemma, true only for the specific closure).
- **Consequence:** `MStateWf`'s value case must use **`StackWfV` consistently** (every `.V`-state along the
  run). The structural `StackWf.assign` alone is **insufficient for no-crash soundness** — an Assign-pop
  with an un-ready value can bad-crash when the body instantiates `x`. So the soundness fold carries
  `StackWfV` at each value state; `stackWfV_toStackWf` (drop the readiness → structural `StackWf.assign`) is
  used only in the answer-type/segment composition where no pop-binding happens.

So the grind is: (1) `StackWf.assign` store `s` (+ inversion + the 2 construction sites + `stackSeg`
arm); (2) `StackWfV` inductive (8 frames; only `assign` carries readiness, `trace` recurses, others mirror
`StackWf`) + `stackWfV_toStackWf` + inversions; (3) `MStateWf` value case → `StackWfV`, with the E-control
case carrying `Rdy` about the future closure (computed at the push via `genAt_closure_ready`, where
`env = fenv`, the one coherent point) across the lambda→closure step; (4) re-green preservation_E/V/progress
+ the `MStateWfB`/`StackWfB` mirror. Coherent, large, no green intermediate.
