---
date: 2026-06-18
milestone: T6 — `let_poly` constructive generalization `genAt`: substitution-stability DELIVERED
status: DELIVERED (the `generalizesAt_subst` crux, via the design fork's constructive route)
---

# `let_poly` — constructive `genAt` + substitution-stability `generalizesAt_subst`, green

The previous session machine-checked `generalizes_subst_false` (the declarative `Generalizes` is **not**
substitution-stable) and `generalizesAt_subst` "resisted a direct proof" for the *declarative*
level-indexed `GeneralizesAt` (`∃σ'`): an arbitrary instantiation of the substituted scheme does not
reduce through `subst_instantiate'`, and the `∃` exposes no structural `s.body = …d…` handle. The
recorded resolution was the **constructive-gen fork** (level-redesign note §2): reformulate the witness
as a *computed* generalization so substitution-stability becomes a `subst`/`shift` **commutation**, not
an existential chase. **That fork is now delivered, green, axioms clean.**

## What landed (`Eyg/Types/Generalization.lean`, `Eyg/Types/Scheme.lean`)

Foundational `subst`/`freeVars` lemmas (`Scheme.lean`, standalone, broadly reusable):
- **`Ty.subst_congr_free`** — two substitutions agreeing on every free variable give equal results
  (the `σ₂ = id` case is the pre-existing `subst_eq_of_fixes_free`).
- **`Ty.mem_freeVars_subst`** — `i ∈ freeVars (subst σ t) ↔ ∃ v ∈ freeVars t, i ∈ freeVars (σ v)`
  (the standard free-var-set-under-substitution characterization).

Constructive generalization (`Generalization.lean`):
- **`Ty.genArity n d`** = `(d.freeVars.map (·+1-n)).foldr max 0` — one quantifier slot per generalized
  (`≥ n`) variable; closed-below-`n` types get arity `0`. Helpers `Ty.mem_le_foldr_max`,
  `Ty.foldr_max_le`, and **`Ty.genArity_spec`** (every `v ≥ n` free in `d` has `v - n < genArity n d`).
- **`Ty.reindexGen n arity`** — `v ↦ var (v+arity)` if `v < n` (ambient, shift past the prefix), else
  `v ↦ var (v−n)` (generalized → quantifier `v−n`).
- **`Scheme.genAt n d`** = `⟨d.genArity n, subst (reindexGen n (genArity n d)) d⟩` (+ `Scheme.ext'`,
  componentwise scheme equality).
- **`genAt_generalizesAt : GeneralizesAt n (genAt n d) d`** — every instantiation of `genAt n d` is a
  `subst`-instance of `d` whose witness fixes `[0,n)`. (Notably the witness fixes `[0,n)` *regardless of
  arity*: an ambient `i < n` is reindexed to `i + arity ≥ arity`, which `instantiate` shifts straight
  back to `var i`.)

The substitution-stability core (`Generalization.lean`):
- **`Ty.LevelMap n σ`** := `(∀ i ≥ n, σ i = var i) ∧ (∀ i < n, ∀ w ∈ freeVars (σ i), w < n)` — exactly
  the ambient-into-ambient class the level-redesign note pins as what `hasType_subst` threads.
- **`Ty.shift_eq_reindexGen`** — on a type with all free vars `< n`, `reindexGen n k` *is* `shift k`
  (the ambient case hinge).
- **`genArity_subst : LevelMap n σ → (subst σ d).genArity n = d.genArity n`** — arity is preserved (the
  weighted max is unmoved: a level map fixes `[n,∞)` and keeps `[0,n)` at weight `0`); proved by
  `Nat.le_antisymm` from `foldr_max_le`/`mem_le_foldr_max`/`mem_freeVars_subst`.
- **`genAt_substScheme : LevelMap n σ → substScheme σ (genAt n d) = genAt n (subst σ d)`** — the
  commutation. Body equality via `subst_subst` on both sides + `subst_congr_free`, split on `v ≥ n`
  (generalized: reindexed to quantifier `v−n < arity`, `σ` fixes it) vs. `v < n` (ambient: LHS shifts
  `σ v`, and `reindexGen` acts as `shift` on it since `FV(σ v) ⊆ [0,n)`).
- **`generalizesAt_subst : LevelMap n σ → GeneralizesAt n (substScheme σ (genAt n d)) (subst σ d)`** —
  one line from the commutation + `genAt_generalizesAt`. **This is the substitution-stability the
  `hasType_subst` `let_poly` arm needs** (with the rule's scheme pinned to `genAt`).

Rule-facing bridges into the existing keystone (so the threading session has the connectives ready):
- **`genAt_generalizes`** — `genAt n d` satisfies the declarative `Generalizes` that
  `generalizes_closure_ready` consumes (for a context below level `n`).
- **`genAt_closure_ready`** — push-time polymorphic readiness: the let-bound lambda's closure inhabits
  **every** instantiation of `genAt n defnTy`. This is exactly the closed `Rdy` the `Assign`-push
  computes once and the coupling design's `StackWfV` carries to the pop.

Axioms: `propext`/`Quot.sound` only (no `Classical.choice`, no `sorry`, no new `axiom`s).
`lake build` 1772 + `lake exe spec` 104/104.

## Why this closes the crux the design fork identified

The declarative `∃σ'` form could not relate the substituted scheme's *arbitrary* instantiations back to
`subst σ d`. Pinning the witness to the **computed** `genAt n d` makes the scheme body *structurally*
`subst (reindexGen …) d`, so `substScheme σ (genAt n d)` and `genAt n (subst σ d)` are both `subst`s over
`d`'s free variables and the equality is a pointwise `subst`/`shift` calculation — no existential to
invert. The level discipline is what makes it true: a `LevelMap` cannot collide a generalized variable
(`≥ n`) into `FV(Γ) ⊆ [0,n)` (the exact failure `generalizes_subst_false` exhibits for the level-naive
predicate), because it fixes `[n,∞)` and keeps `[0,n)` within `[0,n)`.

## Remaining for the `let_poly` slice (unchanged shape, now unblocked)

The substitution-stability blocker is resolved. The dedicated implementation session still has to thread
it through the judgment (the level-redesign note items 1, 3, 4):

1. **Pin the `let_poly` rule's scheme to `genAt`** (or carry a `GeneralizesAt n s d` premise *plus* the
   constructive witness), and decide the minimal-blast-radius level carrier: a full level-indexed
   `HasTypeAt n` vs. a `CtxWf n Γ`/`TyWf n τ` side-invariant consumed only where gen/subst happen.
2. **Re-state `hasType_subst`** with the `LevelMap n σ` premise (replacing the arbitrary `σ`); its
   `let_poly` arm now discharges via `generalizesAt_subst`. Re-green its existing callers — verify the
   substitutions they pass are level maps (the keystone's instantiation `σ` should qualify).
3. The machine coupling (`StackWfV`, carried readiness, both preservation engines) from
   `2026-06-18-T6-let_poly-coupling-design-sharpened.md` — unchanged, now atop the level-aware predicate.

These remain a multi-step structural change with no standalone-green sub-increment through the two-engine
`Soundness.lean`; this session's deliverable is the previously-missing **algebra**, landed standalone and
green, exactly as the design fork directed ("land (2) as a standalone green lemma before threading").
