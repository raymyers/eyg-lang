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

## What this unblocks / the consuming slice (next)

The `StackWf` integration is the *consuming* slice (not done here): add a weakening
variant of `applyf`/`callwith` allowing the function's latent row to be an `EffSub` of
the ambient (`ε_f ⊑ ε`), then re-prove the application preservation/progress cases. With
`effSub_empty` in hand, the `fix` pure-builder application (`Apply builder` at the
effectful ambient) and the pure-builtin-under-effect case both type. After that, the
`partialFixed` cascade (`2026-06-16-T6b-fix-scoping.md`) can land `FixPreserves`/
`FixNoBadCrash`.

This is the foundational half of Open Question 3; it is purely additive (nothing imports
`EffSub` yet), so it carries zero cascade risk and was deliverable as one green commit.
