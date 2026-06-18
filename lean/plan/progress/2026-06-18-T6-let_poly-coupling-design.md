---
date: 2026-06-18
milestone: T6 — `let_poly` machine-coupling design specification
status: DESIGN SPEC (implementation is the next milestone session; keystone + impossibility banked)
---

# `let_poly` — the machine-coupling design (full specification)

Builds on `2026-06-18-T6-gen-declarative-keystone.md`. The semantic keystone
(`generalizes_closure_ready`) is green; this note specifies the *machine* wiring so the
implementation session can start from a settled design rather than re-deriving it.

## The problem, restated precisely

For a value-restricted `let x = (λ…) in body` (the only `gen`-eligible form), preservation's
**`Assign`-pop** step must discharge `EnvWf.cons`'s polymorphic clause
`∀ args, HasTypeV v (s.instantiate args)`. The keystone delivers this **iff** it is fed the
let-site facts (`HasType Γ ⟨λ⟩ defnTy ε`, `EnvWf fenv Γ`, `Generalizes s Γ defnTy`). But:

- `MStateWf`'s value case is `∃ τin, HasTypeV v τin ∧ StackWf k τin ε τ` — the value's type is
  **decoupled** from the stack, so the `Assign`-pop sees only an arbitrary `v : defnTy`.
- A **value-agnostic** readiness premise on the frame is the **false** value-substitution
  lemma (proved impossible last commit — false even for arrow `defnTy` via open-row capture).

So the `Assign`-pop cannot know `v` is the let's closure without a **coupling** that ties the
value position to the frame across the lambda→closure→pop sequence.

## The irreducible obstacle (verified this session)

Any sound coupling must distinguish the **poly** `Assign` frame from the **mono** one (mono
`let x = 3` binds a non-closure; poly binds a closure needing readiness). **That flavor is
NOT observable from the runtime stack** `k` — the runtime frame is `Kontinue.Assign x body
fenv` in both cases; the mono/poly distinction lives only in the `StackWf` *typing* (which
constructor typed the frame), and `MStateWf` existentially quantifies the `StackWf` proof, so
a `def`-level `MStateWf` clause cannot branch on it. Hence a clean coupling **requires making
the value-position visible to the frame typing** — `StackWf`/`MStateWf` must become
*value-aware* at the `Assign` head. This is the genuine refactor (the "MStateWf-freshness
invariant" the plan's deepened finding named), and it is what makes `let_poly` a milestone
slice rather than a mechanical edit.

## Two viable designs (pick at implementation time)

### Design A — value-aware `Assign` head (recommended)

Thread the bound value into the head-frame typing. Change `MStateWf`'s value case to
`∃ τin, HasTypeV v τin ∧ StackWfV v k τin ε τ`, where `StackWfV v k …` equals `StackWf` on the
tail and, at an `Assign` head, carries a **bind-readiness** `RBind`:

- mono frame: `RBind v := HasTypeV v defnTy` (already implied by `HasTypeV v τin`);
- poly frame: `RBind v := (∃ p b, v = Value.Closure p b fenv) ∧ (∀ args, HasTypeV v (s.instantiate args))`.

The poly `RBind` is **observable+sound**: the closure-capturing-`fenv` shape is established at
the lambda→closure step (the closure's env *is* `fenv`, the let-site env the frame stored),
and the readiness is the keystone fed the stored let-site facts. Cost: `StackWfV` (a value-
aware wrapper or an extra `Assign`-head index) + re-green `preservation_E` (Let-push: build the
poly frame), the lambda→closure step (establish `RBind`), `preservation_V` (Assign-pop: read
`RBind`), `progress`, `soundness_value`. **Scope can be limited to the `MStateWf`/`StackWf`
world first** (value-soundness, no-bad-crash, progress); the `MStateWfB`/`StackWfB` base-row
engine (effect/divergence results) is a *separate* follow-up — `let_poly` is effect-orthogonal,
so the B-world coverage can lag without affecting the ε-free headline.

### Design B — global freshness counter

Thread `N : Nat` with the invariant "every type var in the config's typing is `< N`" and make
`gen` generalize only vars `≥ N`; then any instantiating `σ` fixes all config contexts
value-agnostically (so the keystone applies without a per-frame value match). Cleaner *locally*
but the "all config types `< N`" invariant over the **existential** `MStateWf` typing is itself
awkward to state and preserve (it must hold of every `EnvWf`/`StackWf` witness), and `N` grows
at each `gen`. Judged **less clean** than A for this codebase.

## Implementation checklist (Design A, `MStateWf` world first)

1. `HasType.let_poly` (value-restricted: `defn = ⟨.Lambda _ _⟩`) + `Generalizes s Γ defnTy`
   premise + body under `(x,s)::Γ`. Fix `hasType_expr_form` (Let arm) and `inv_let`
   (return mono ∨ poly, or generalize to a scheme) + add `inv_let_poly`.
2. `StackWfV` (value-aware Assign head) or `StackWf.assignGen` + the value-aware `MStateWf`
   value case. Re-prove the affected `StackWf` inversions/`conv`-folds.
3. `preservation_E` Let-push (build the poly `Assign` frame storing the let-site facts);
   lambda→closure step (establish `RBind`); `preservation_V` Assign-pop (keystone discharges
   `EnvWf.cons`). Re-green `progress`, `soundness_value`.
4. A polymorphic-reuse `example` (`let id = \x.x in (id 1, id "a")`).
5. (Follow-up) mirror into `StackWfB`/`MStateWfB` for the effect/divergence results.

## Status of progress this session
- `Eyg/Types/Generalization.lean` keystone — green, axiom-clean (committed `ea253040`).
- Impossibility of the value-agnostic route — proved/recorded (committed `b206c7cf`).
- This design spec — the settled wiring for the implementation session.
- `lake build` 1772 + `lake exe spec` 104/104 remain green; headline `soundness` axioms clean.
The remaining `let_poly` implementation (Design A) is the next milestone session; the other
open PLAN item (`FixPreserves`/`FixPreservesB`) is the documented research/`fix`-scheme decision.
