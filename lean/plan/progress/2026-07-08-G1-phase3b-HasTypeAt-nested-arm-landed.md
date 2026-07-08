---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 3b: the level-tracking judgment HasTypeAt + a non-vacuous, arbitrary-depth hasTypeAt_subst; nested Let-binds-Lambda genuinely typed and re-substituted
status: LANDED — one green additive commit on top of 0339ba28; the nested example (the exact shape noLambdaLet rejects) type-checks under HasTypeAt AND is re-typed non-vacuously by hasTypeAt_subst
kind: progress
component: lean (Eyg/Types/TypingAt.lean, new file)
---

# G1 Phase 3b: `HasTypeAt` + `hasTypeAt_subst` — the nested `let_poly` arm fires for arbitrary depth

Continuation of `progress/2026-07-08-G1-phase3b-hasType_substAt-nested-arm-grounded.md`, which reduced
the wall to a single missing hypothesis (`n ≤ n_let`) and prescribed the fix: a level-tracking judgment
whose `let_poly` generalizes at exactly the ambient level. This session **built that judgment and proved
the substitution lemma**, non-vacuously, for arbitrarily deep nesting. All additive — one new file
`Eyg/Types/TypingAt.lean`, nothing existing touched.

## What landed (new file `Eyg/Types/TypingAt.lean`)

### `HasTypeAt (lvl : Nat) : Ctx → Node m → Ty → Ty → Prop`

An additive, parallel copy of `HasType`, threading the ambient de-Bruijn level `lvl`. All ~21
constructors mirror `HasType`; the design decisions (the non-mechanical part) are:

- **`let_poly` generalizes at exactly `lvl`** — stores `Scheme.genAt lvl defnTy`, records `CtxWf lvl Γ`,
  and types its body at the fresh level `lvl + 1`. The stored generalization level *is* the ambient
  level by construction, so the `n ≤ n_let` gap of the previous session becomes `rfl`.
- **`let_poly` carries NO `noLambdaLet`.** That predicate is the vacuity-guard the *unprovable*
  `hasType_subst` `let_poly` arm needs; here the arm is genuinely provable, so it is dropped and nested
  `Let`-binds-`Lambda` bodies — the exact shape `noLambdaLet` (and all of Caveat 5) reject — are
  genuinely accepted.
- **`lam`/`let_` store an explicit sublevel `lvl'`** (premises `lvl ≤ lvl'` and
  `∀ i ∈ argTy.freeVars, i < lvl'`) rather than *computing* a bump `max lvl (argTy.genArity 0)`. This is
  the one subtlety not spelled out by the prior note: a *computed* bump does **not** commute with an
  ambient `LevelMap lvl` substitution when `lvl > 0` (`genArity 0 (subst σ argTy) ≠ genArity 0 argTy` in
  general — `genArity_subst` only gives equality for a `LevelMap` at the *same* level `0`, which we do
  not have), so the body IH would land at a level the reconstructed node cannot match. A *stored* `lvl'`
  reconstructs at the identical level; `freeVars (subst σ argTy) < lvl'` then follows structurally from
  `LevelMap lvl σ` (ambient vars `< lvl` map into `[0,lvl) ⊆ [0,lvl')`; fresh vars `≥ lvl` are fixed and
  were already `< lvl'`).

### `hasTypeAt_subst`

```
theorem hasTypeAt_subst {lvl Γ e τ ε} (σ : Nat → Ty)
    (h : HasTypeAt lvl Γ e τ ε) (hσ : Ty.LevelMap lvl σ) (hΓ : CtxWf lvl Γ) :
    HasTypeAt lvl (substCtx σ Γ) e (Ty.subst σ τ) (Ty.subst σ ε)
```

A direct induction (`revert hσ hΓ; induction h`). Every arm reuses the *existing magnitude* machinery
(`genAt`/`CtxWf`/`LevelMap`) per the note's recommendation:

- `var`/`builtin`: `Scheme.subst_instantiate'` unchanged.
- `lam`/`let_`: body IH at the stored `lvl'` (`LevelMap.mono` + `CtxWf.mono` + `ctxWf_cons` lift `σ`
  and the context); the reconstructed premise `freeVars (subst σ argTy) < lvl'` is the structural
  `LevelMap` argument above.
- **`let_poly`**: body IH at `lvl + 1` (`LevelMap.mono`/`CtxWf.mono` by `lvl ≤ lvl+1`; the extended
  context is `CtxWf (lvl+1)` via a new helper `genAt_freeVars_lt` — the ambient free vars of
  `genAt lvl defnTy` are `< lvl < lvl+1`). `substCtx_cons_genAt hσ` rewrites the substituted extended
  context into the `genAt lvl (subst σ defnTy) :: substCtx σ Γ` the rule demands, and
  `HasTypeAt.let_poly` reconstructs (`CtxWf lvl (substCtx σ Γ)` by `ctxWf_substCtx`). **`n_let = lvl`
  by construction, so no `n ≤ n_let` premise is ever needed** — the wall is gone.

One new helper: `genAt_freeVars_lt` (`∀ i ∈ Scheme.freeVars (genAt n d), i < n`), from
`Scheme.mem_freeVars` + `Ty.mem_freeVars_subst` + `genArity_spec`.

### The "does the wall fall" check (three theorems in the `NestedExample` section)

- **`hInner`**: `HasTypeAt 1 [("x", mono α)] (let inner = \y.y in inner x) α ! ∅` — the inner core, a
  `Let`-binds-`Lambda` node (`noLambdaLet` of it is `False`), generalizing `inner` to `∀β. β→β` at
  level 1 and instantiating it at `x`'s type `α`.
- **`hOuter`**: `HasTypeAt 0 [] (let outer = \x. (let inner = \y.y in inner x) in outer 1) integer ! ∅`
  — the whole doubly-generalized nested term (reusing `hInner` verbatim as the outer lambda's body),
  the exact Caveat-5 shape. It type-checks under `HasTypeAt`.
- **`hInner_subst`**: applies `hasTypeAt_subst` to `hInner` with the **non-identity** substitution
  `σα : α ↦ integer` (a `LevelMap 1`), producing
  `HasTypeAt 1 [("x", mono integer)] (let inner = \y.y in inner x) integer ! ∅`. The ambient `α` is
  genuinely replaced (context and result type both change from `α` to `integer`), and the polymorphic
  `inner` `let` is re-generalized in the substituted context. **Non-vacuous: the arm fires on a term
  `hasType_subst` cannot even reach, under a substitution that is not the identity.**

(Applying `hasTypeAt_subst` at level 0 would force `σ = id` — `LevelMap 0` fixes every index — hence
the demonstration is at level 1, where a `LevelMap 1` genuinely substitutes the level-0 ambient var.)

## Why this closes the substitution-commutation half completely (recap)

The wall was `generalizes_subst_false`: no ambient substitution discharges the flat-encoding
`let_poly` commutation. The prior session already removed it two ways (magnitude `genAt_substScheme`
under `LevelMap`, and unconditional level-native `genAtV_substSchemeV_generalizesAtV`). The only
remaining obstruction to a *full induction* was the ambient-level bookkeeping `n ≤ n_let`, unrecordable
in `HasType.let_poly`. `HasTypeAt` records it as an index and pins `n_let = lvl`, so the induction goes
through with the existing magnitude lemmas — no `genAtV`/`GeneralizesAtV` needed for this deliverable
(they remain the endgame representation for Phases 4+, esp. the readiness-keystone down-shift removal).

## Current state

Tree green at HEAD (this note's commit on top of `0339ba28`): `lake build` 1775 jobs (was 1774; +1 for
the new file), `lake exe spec` 104/104 evaluation + 104/104 FBS≡interpreter + 21/21 round-trip,
`#print axioms` for `soundness`/`soundness_evalR` = `[propext, Classical.choice, Quot.sound]`, no
`sorry` in `Eyg/Types/*.lean`. `hasTypeAt_subst`/`hOuter`/`hInner_subst` depend only on
`[propext, Quot.sound]`. Everything is additive — `HasType`, `hasType_subst`, `HasType.let_poly`,
`Soundness.lean` untouched.

## What remains for Phase 3b / Phase 4

`HasTypeAt` + `hasTypeAt_subst` prove the nested `hasType_subst` arm is *provable* (fast GO on the
question the whole plan turned on). Migrating from the magnitude `genAt`/`CtxWf` to the level-native
`genAtV`/`CtxWfV`/`GeneralizesAtV` (needed for the readiness keystone's down-shift removal), and then
wiring the relaxed rule into `Typing.lean` (dropping `noLambdaLet` from `HasType.let_poly` itself),
remain Phase 3b-tail / Phase 4 work. This session deliberately took the magnitude route (strictly less
code, fully supported by landed lemmas) per the prior note's recommendation.
