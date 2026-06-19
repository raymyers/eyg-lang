---
date: 2026-06-18
milestone: T6 — `let_poly` threading: item-1 blast-radius DECISION (WfBelow) + `LevelMap.mono` glue
status: DELIVERED (the nested-descent glue lemma, green) + DESIGN DECISION (item 1 resolved)
---

# `let_poly` — the `WfBelow n` blast-radius decision + `LevelMap.mono`

The constructive-`genAt` session (`2026-06-18-T6-let_poly-constructive-genAt-delivered.md`) landed the
substitution-stability algebra (`generalizesAt_subst`, `genAt_substScheme`, `genArity_subst`). The
level-redesign note left **item 1** open — the minimal-blast-radius call between a full level-indexed
`HasTypeAt n` judgment vs. a `WfBelow n` side-invariant — flagging it as "the key design call" that
decides whether *both* preservation engines must be re-typed. This session **resolves item 1** and lands
the one missing piece of descent glue.

## Item-1 DECISION: the `WfBelow n` route — keep `HasType` level-free; localize `n` to the gen layer

Resolved in favour of the side-invariant (`WfBelow n`) route, because the level need **never reach the
two preservation engines**. The enabling structural fact (verified):

> **`Soundness.lean` does not import `Substitution.lean` or `Generalization.lean`.**
> Import graph: `Typing → {Generation, Runtime} → Machine → Soundness`; the gen branch is
> `Typing → Substitution → Generalization`, a *separate* subtree. `hasType_subst` is consumed only by
> `closure_typed_of_lambda_subst → generalizes_closure_ready → genAt_closure_ready`, all in the gen
> branch.

Consequence — the level `n` and the well-formedness side-condition live in exactly two places, **both off
the Soundness import path**:

1. **The `let_poly` constructor's premises** — it stores its level `n`, pins its scheme to `genAt n
   defnTy`, and carries the context-below-level witness `hΓ : ∀ σ' fixing [0,n), substCtx σ' Γ = Γ`
   (equivalently a `CtxWf n Γ`). The constructor is otherwise an ordinary `HasType` node.
2. **`hasType_subst`** (re-stated with a `Ty.LevelMap n σ` premise) and **`genAt_closure_ready`** —
   `Generalization.lean`/`Substitution.lean` only.

The two preservation engines (`StackWf*`/`preservation_*` E **and** the base-row B engine) therefore
treat `let_poly` as an **opaque constructor** carrying a body typing plus a *precomputed, closed*
readiness fact `Rdy : ∀ args, HasTypeV (Closure …) ((genAt n defnTy).instantiate args)` — produced once
at the Let-push via `genAt_closure_ready` and carried by the value-aware `StackWfV` (the coupling design,
unchanged). **Neither engine ever mentions `n`.** This is the decisive reduction: the soundness-side work
is the plain `StackWfV` machine-coupling cascade from
`2026-06-18-T6-let_poly-coupling-design-sharpened.md`, with **no level threading** — exactly what makes
the full level-indexed `HasTypeAt n` alternative unnecessary (it would have forced re-typing both
engines for no soundness-side benefit).

## `LevelMap.mono` — the nested-`let_poly` descent glue (delivered green)

The level-redesign note's "⚠ crux a naive attempt misses" is the **nested `let_poly`**: when
`hasType_subst` (threading a `LevelMap n σ` for the outer scope) descends into a let-bound lambda whose
body contains an inner `let_poly` at a deeper level `n' > n`, the inner generalization's
substitution-stability (`generalizesAt_subst`/`genAt_substScheme`) requires `LevelMap n' σ`, not
`LevelMap n σ`. The note worried this needs "re-levelling as it descends".

It does **not** — a single substitution suffices, by monotonicity:

```
theorem Ty.LevelMap.mono : LevelMap n σ → n ≤ n' → LevelMap n' σ
```

A `LevelMap n` fixes `[n,∞)` (so a fortiori `[n',∞)`) and keeps `[0,n)` within `[0,n) ⊆ [0,n')`; the new
band `[n,n')` is fixed (`σ i = var i`, free var `i < n'`). So the **outer-scope `σ` is already a
`LevelMap` at every deeper let's level** — `hasType_subst`'s `let_poly` arm discharges the inner
`generalizesAt_subst` from the *same* `σ` it was called with, no re-levelling. (Binders only *raise* the
level, and `genAt`'s arity/`reindexGen` are level-monotone in the relevant sense, so the outer `LevelMap`
covers the descent.) Green, axioms `propext`/`Quot.sound`, `lake build` 1772 + `lake exe spec` 104/104.

## Remaining for the slice (unchanged shape; now fully scoped, no level in the engines)

1. **Typing layer** — add `HasType.let_poly` (value-restricted; scheme `genAt n defnTy`; premises
   `HasType Γ defn defnTy ε`, `hΓ` context-below-`n`, `HasType ((x, genAt n defnTy)::Γ) body bodyTy ε`).
   Cascade the no-catch-all inductions: `hasType_ctxConv` (via `generalizes_ctxConv`), `hasType_subst`
   (the `let_poly` arm via `generalizesAt_subst` + `LevelMap.mono` for the descent), `weakenEff`
   (`Soundness.lean:57`), `inv_let` (unify to a scheme form) + `hasType_expr_form` arm (Generation.lean).
2. **`hasType_subst` re-statement** — premise `Ty.LevelMap n σ` (+ a `CtxWf`/`TyWf` well-formedness
   threaded through its own induction; the `lam` arm bumps the scope). All within `Substitution.lean`.
3. **Machine coupling** — generalize `StackWf.assign` to store a scheme; add value-aware `StackWfV` (+
   `stackWfV_toStackWf`, inversions, `conv`); `MStateWf` value case → `StackWfV`; re-green
   `preservation_E`/`_V`/`progress` (push computes `Rdy` via `genAt_closure_ready`; Lambda-step carries
   it; Assign-pop feeds `EnvWf.cons`). **Mirror in the B engine** (`StackWfVB`). No level appears here.
4. **Example** — `let id = \x.x in pair (id 1) (id "a")` types polymorphically.

Items 1–3 remain the all-or-nothing cascade through the two-engine `Soundness.lean` (no standalone-green
sub-increment — adding the constructor breaks every `HasType` induction/inversion at once). This session's
deliverable is the **item-1 decision** (which removes level threading from the engines) plus the
**`LevelMap.mono`** glue (which removes re-levelling from `hasType_subst`'s descent) — both landed/green.
