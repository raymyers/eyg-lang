---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 3b: obstruction (B) RESOLVED — the level-native value judgment `HasTypeVAt`/`EnvWfAt` and the value-side readiness keystone `genAtV_closure_ready_value`, landed additively, non-vacuous on the nested Caveat-5 term down to a concrete runtime closure
status: one green additive commit (new file `Eyg/Types/RuntimeAtV.lean`); obstruction (B) from the previous session is closed; Caveat 5's soundness gap is now closed on BOTH the term-typing and value-typing sides, all the way to a `Value.Closure`
kind: progress
component: lean (Eyg/Types/RuntimeAtV.lean, Eyg.lean)
---

# G1 Phase 3b: `HasTypeVAt` + `EnvWfAt` + the value-side readiness keystone

Continuation of `progress/2026-07-08-G1-phase3b-HasTypeAtV-instantiation-keystone-landed.md`. That
session resolved obstruction **(A)** — the level-native *term* judgment `HasTypeAtV`, its
instantiation-direction re-typing induction `hasTypeAtV_substAt`, and the term-level readiness keystone
`genAtV_instantiate_lam_ready` — and scoped out obstruction **(B)**, the value-typing side. This
session **resolves (B) in full**.

## The gap (B) closed

`Runtime.lean`'s `HasTypeV.closure` requires a **magnitude** `HasType ((x,.mono argTy)::Γ) body retTy
εb` derivation of the closure's lambda body, and `EnvWf.cons` requires `∀ args, HasTypeV v
(s.instantiate args)`. Because `HasType.let_poly` carries `noLambdaLet`, no magnitude `HasType`
derivation exists once the body itself binds a polymorphically-used lambda-`let` (generalization nested
≥ 2 deep — the exact Caveat-5 shape). So even with `TypingAtV.lean`'s term-level re-typing in hand,
there was no route to an actual `HasTypeV (Value.Closure …)` judgment: the constructor demands the
wrong (magnitude, `noLambdaLet`-restricted) premise.

## What landed (one additive commit, new file `Eyg/Types/RuntimeAtV.lean`)

### 1. `HasTypeVAt lvl v τ` / `EnvWfAt env Γ` — the level-native value/environment judgments

A `mutual` block mirroring `HasTypeV`/`EnvWf`:

- **`HasTypeVAt.closure`** is the constructor that differs: it consumes a **level-native**
  `HasTypeAtV lvl Γ ⟨.Lambda x body, a⟩ τ ε` lambda derivation (`TypingAtV.lean`) — which *does* exist
  for arbitrarily nested generalization, no `noLambdaLet` — plus `EnvWfAt env Γ` and a `Ty.TyEquiv τ τ'`
  leaf (the `HasTypeV` leaf-conversion design, kept but **without** forcing a syntactic arrow, so the
  keystone's `instantiateV args` conclusion type slots in directly). Base literals (`int`/`str`/`bin`)
  thread `Ty.TyEquiv` exactly as `HasTypeV`; `HasTypeVAt.conv` derived.
- **`EnvWfAt.cons`** states its readiness over `HasTypeVAt s.level`/`Scheme.instantiateV` at the
  scheme's own generalization level, with the natural instantiation-args side-condition
  `∀ t ∈ args, ∀ l ∈ t.levels, l ≤ s.level` — the value-side of `hasTypeAtV_substAt`'s `hσ` bound
  (a level-`ℓ` scheme is opened only at types whose levels do not exceed `ℓ`; deeper generalization
  levels do not exist at the point of instantiation). Discharged trivially for ground arguments.

### 2. `genAtV_closure_ready_value` — the value-side readiness keystone (level-native `generalizes_closure_ready`)

For a let-bound lambda presented via its `lam` components at ambient level `ℓ` (body at a strictly
higher `lvl'`, context `Γ` below `ℓ` via `CtxWfV ℓ Γ`, polymorphic bindings above `ℓ` via
`PolyAbove ℓ Γ`) whose runtime environment realizes `Γ` level-natively (`EnvWfAt env Γ`), the runtime
closure `Value.Closure x lbody env` inhabits **every** (well-formed) instantiation of its generalized
scheme `genAtV ℓ (.fun argTy εb retTy)`. Composes `genAtV_instantiate_lam_ready` (term level) with
`HasTypeVAt.closure`. This is exactly the `EnvWfAt.cons` obligation (`s.level = ℓ`), discharged with
**no `noLambdaLet`** on the closure body — the level-native analog of the magnitude
`generalizes_closure_ready`.

### 3. The nested demonstration — the whole chain down to a concrete runtime closure

Reusing `hInnerV`/`hOuterV_instantiate` (`TypingAtV.lean`):

- `hOuterVClosure_ready` applies `genAtV_closure_ready_value` to the outer lambda
  `\x. (let inner = \y.y in inner x)` (body = `hInnerV` at the strictly higher level `2`, generalizing
  the nested `inner` at level `2`) over the empty environment (`EnvWfAt.nil`): the **actual runtime
  closure** `Value.Closure "x" outerBody []` inhabits *every* instantiation of `genAtV 1 (α → α)`.
- `hOuterVClosure_typed_integer_arrow` instantiates at `[integer]` (levels `[]`, side-condition
  trivial) and reduces `(genAtV 1 (α → α)).instantiateV [integer] = integer → integer` by `rfl`: the
  genuine `Value.Closure` inhabits `Integer → Integer` — the outer type variable `α` (level `1`)
  genuinely replaced by `integer`, the nested inner scheme (level `2 ≠ 1`) correctly re-generalized.
- `hOuterVClosure_via_constructor` reaches the same conclusion straight from `HasTypeVAt.closure`
  fed `hOuterV_instantiate`, making the `term derivation → closure value` step fully explicit.

This is the **value-side "wall falls" check**: the whole chain `term derivation → closure value →
typed-at-every-instantiation` closes non-vacuously for the doubly-nested Caveat-5 case the original
`HasType`/`HasTypeV`/`generalizes_closure_ready` chain reaches only vacuously.

## Scope decisions (the honest boundaries)

- **Only the generalization-bearing value shapes are mirrored** — base literals (to realize
  ground-typed environments) and the crux `closure`. The runtime-continuation / partial value shapes
  (`partialBuiltin` → `BuiltinPartialWf`, `partialResume` → `StackSegWf`, and the data/partial
  constructors) carry **zero** generalization content — each is a mechanical `HasTypeV → HasTypeVAt lvl`
  transliteration threading `Ty.TyEquiv` unchanged. They belong to the Phase-5 `Machine`/`Runtime`
  re-green, not the Caveat-5 mathematics, and are deliberately out of scope here. `HasTypeVAt` is thus
  a *focused* judgment complete on the load-bearing axis, not (yet) a drop-in `HasTypeV` replacement.
- **The instantiation-args side-condition** `args' levels ≤ s.level` on `EnvWfAt.cons`/the keystone is
  the value-side of the term keystone's `hσ` bound. It is the natural well-formedness restriction on
  instantiation arguments (already threaded through `hasTypeAtV_substAt`), not a new obstruction; it is
  discharged trivially for ground arguments (the demonstration's `[integer]`). No new mathematical
  uncertainty surfaced.

## What this closes / what remains

- **Obstruction (B) is closed.** The term-level re-typing is turned into a genuine
  `HasTypeVAt (Value.Closure …)` judgment, and the value-side readiness keystone
  `genAtV_closure_ready_value` discharges `EnvWfAt.cons` for a `genAtV ℓ`-generalized binding with no
  `noLambdaLet` restriction, non-vacuously down to a concrete runtime closure at `Integer → Integer`.
- **This is the complete mathematical resolution of Caveat 5's soundness gap** — both the term-typing
  (`HasTypeAtV`/`hasTypeAtV_substAt`/`genAtV_instantiate_lam_ready`) and the value-typing
  (`HasTypeVAt`/`EnvWfAt`/`genAtV_closure_ready_value`) sides of nested let-polymorphism, all the way to
  a `Value.Closure`.
- **Remaining (Phases 4–7, engineering not open mathematics):** fold this back into the load-bearing
  path — drop `noLambdaLet` from `HasType.let_poly` in `Typing.lean`, and re-green
  `Machine.lean`/`Runtime.lean`/`Soundness.lean` over the level-native judgments (including the
  mechanical mirror of the omitted partial/continuation value shapes). The mathematics is settled.

## Current state

Tree green at HEAD (one commit this session on top of `c51f70c1`): `lake build` 1777 jobs, `lake exe
spec` 104/104 evaluation + 104/104 FBS≡interpreter + 21/21 round-trip + 21/21 CID, `#print axioms` for
`soundness`/`soundness_evalR` (and `genAtV_closure_ready_value`/`hOuterVClosure_typed_integer_arrow`/
`hOuterVClosure_via_constructor`) = `[propext, Classical.choice, Quot.sound]`, no `sorry` in
`Eyg/Types/*.lean`. Purely additive — `HasType`, `HasTypeV`, `EnvWf`, `HasTypeAt`, `HasTypeAtV`,
`Generalizes`/`generalizes_closure_ready`/`closure_typed_of_lambda_subst`, `Runtime.lean`,
`Soundness.lean` all untouched; the only edits outside the new file are the `import` line in `Eyg.lean`
and the plan/note.
