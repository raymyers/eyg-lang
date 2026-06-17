---
date: 2026-06-17
milestone: T6b (fix) / Open Question 3 — effect weakening foundation
status: foundation DELIVERED (green, isolated, additive)
---

# Effect-row subsumption `EffSub` — the effect-weakening prerequisite

## Context

`fix` (T6b) cannot be typed by the exact-match application frames
(`StackWf.applyf`/`callwith`, `Eyg/Types/Machine.lean`), which require an applied
function's *latent* effect row to **equal** the ambient row. The `fix` unrolling
applies the **pure** builder (`α →⟨∅⟩ α`) inside the recursion's effectful ambient,
so exact match would demand `∅ = ⟨Log|μ⟩` — false. This is finding 3 of
`2026-06-16-T6b-fix-scoping.md` and Open Question 3 of the plan: `fix` (and a
realistic effectful fragment, and pure-builtin application under a non-empty ambient)
need **effect weakening / row subsumption**.

## Delivered (`Eyg/Types/EffSub.lean`, green, axiom-clean)

The relation + its metatheory, additively and in isolation (mirrors the
membership-based style of `Eyg/Types/EffRow.lean`):

- **`EffSub e₁ e₂`** — semantic/membership subsumption: every operation `EffContains
  e₁ l a b` is matched by `EffContains e₂ l a' b'` with `TyEquiv a a' ∧ TyEquiv b b'`.
  This is exactly the property soundness needs: an op a weakened function emits is in
  `ε_f`, hence (by `EffSub`) in the ambient — **effect safety survives weakening**.
- `effContains_extend_inv` — inversion on an `effectExtend` head, stated on a *variable*
  head so the case split never trips dependent elimination on distinct string literals
  (the trap that broke the first draft).
- `effContains_mono`, `effSub_refl`, `effSub_trans`.
- **`effSub_empty : EffSub .empty e`** — the key fact for the `fix` pure builder
  (latent `∅`) and pure builtins under an effectful ambient.
- `tyEquiv_effSub`, `effSub_tyEquiv_left/right` — absorb the row reorderings the typing
  judgment already reasons up to.
- `effSub_extend` (guarded by freshness of the new head in the tail) — extension by a
  genuinely-new operation is a weakening; the freshness guard is load-bearing (Leijen
  scoped-label shadowing).
- Sanity examples incl. `∅ ⊑ ⟨Log⟩` and `⟨abort⟩ ⊑ ⟨log, abort⟩`.

## What this unblocks / the consuming slice (next) — design worked out

The `StackWf` integration is the *consuming* slice (not done here). The initial sketch
was "add a weakening `applyf`/`callwith` variant (`ε_f ⊑ ε`) and re-prove the application
cases." Tracing the actual `applyf`-fire proof (`Soundness.lean:446` `preservation_V`)
shows that is **not sufficient on its own** — and pins down the real shape:

### Why a `StackWf` weakening constructor alone does not close

When a weakened `applyf` (function `f : argTy →⟨ε_f⟩ retTy`, ambient `ε ⊇ ε_f`) *fires*
on a **closure**, `reduceCall` runs the closure body under a `Trace :: rest` stack, and
`rest` expects `retTy` at ambient `ε`. The closure stores its body typed at its own
latent `ε_clo ≈ ε_f` (`HasTypeV.closure`). The current proof converts that to the
ambient via `HasType.conv` — which works **only because exact-match `applyf` forces
`TyEquiv ε_clo ε`**. Under weakening we have merely `EffSub ε_f ε`, so we must re-type
the body `HasType body retTy ε_f → HasType body retTy ε`. That is **`HasType` effect
weakening**, and it is **not admissible** by plain induction: the `app` rule's IH
weakens the *ambient* but the applied function's type mentions the latent row
covariantly, so weakening `∅ → ε` inside an arrow is not recoverable from the IH (the
covariance wall — the same reason effect weakening is a declarative *rule*, not a lemma,
in Koka/Links/Frank).

The lambda-value escape (a lambda is `ε`-general, so `fix`'s nested-lambda builder body
re-types at any `ε` for free) covers *that one example* but **not** the general
`applyfWeak` constructor, which must accept any builder value of type `α →⟨ε_f⟩ α`.

### The actual required change (Open Question 3, full)

Add a declarative **effect-subsumption rule** to `HasType`:

```
HasType.subEff : HasType Γ e τ ε₁ → EffSub ε₁ ε₂ → HasType Γ e τ ε₂
```

(sound — a term performing only `ε₁` ops runs in any `ε₂ ⊇ ε₁`; standard algebraic-
effect subsumption). This is what `effSub_empty`/`EffSub` were built to feed. The
cascade it triggers:

1. **Inversion lemmas** (`inv_app`/`inv_lam`/`inv_perform`/… in `Typing.lean`, and
   `hasType_expr_form`) must "see through" `subEff` — each now returns its premise
   row up to `EffSub` (a smaller row `ε'` with `EffSub ε' ε`) rather than the exact
   ambient. This is the bulk of the work and changes lemma *statements*.
2. A weakening **`StackWf.applyfWeak`/`callwithWeak`** (or fold the weakening into the
   `applyf`/`callwith` premises via `EffSub`), with new arms at the ~4 `cases hst`
   sites (`preservation_V:435`, `progress:1118`, `reduce1Run_done_value_typed`) and the
   `induction hst` at `Soundness.lean:76` / `stackWf_append`.
3. preservation's `subEff` case (recurse on the premise, compose `EffSub`), progress
   likewise.

This is **session-sized and comparable in weight to `Handle`** (it touches the shared
`HasType` inversion cascade), so it is its own slice, not a quick wire-up after `EffSub`.
Once it lands, `effSub_empty` types `fix`'s pure-builder application and the
pure-builtin-under-effect case, and the `partialFixed` cascade
(`2026-06-16-T6b-fix-scoping.md`) can then land `FixPreserves`/`FixNoBadCrash`.

`EffSub` itself is the foundational half of Open Question 3; it is purely additive
(nothing imports it yet), zero cascade risk, delivered as one green axiom-free commit.
