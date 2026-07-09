# G2 Phase 1 — `hasType_substAt_multi` GREEN (go/no-go gate passed)

Date: 2026-07-09. Branch `lean-cslib-subproject`. Spike file `Eyg/Types/G2Spike.lean`.

## Result

The plan's single genuinely-new lemma is **proven, machine-checked, no sorry, axioms
`[propext, Classical.choice, Quot.sound]`**. The go/no-go gate for the whole G2 rearchitecture is
GREEN. The `le`-proof induction skeleton carried over arm-by-arm as predicted — the spike compiled on
the first real attempt (only fix: a missing `open Eyg.Ir`).

## The refined σ-condition (strictly generalizes `_le`, drops the plan's `NoGenAt l h`)

Plan §3 tentatively proposed `hσ : l = 0 ∨ (NoGenAt l h ∧ PolyAboveFV l Γ e)`. The condition that
actually makes the induction go through — and is *simpler* — **strictly extends** `_le`'s `{0, ℓ}`
bound with a third disjunct:

```
hσ : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl ∧ PolyAboveFV l Γ e)
```

The `l = ℓ` disjunct must be kept (self-review caught this): it is `_le`'s regime, covering the
boundary case `l = ℓ = lvl'` (e.g. `\x. perform "op" x`, whose body sublevel can equal the gen
level — and in the floor form `l = ℓ` is the `s.level` disjunct). Dropping it would make the lemma
*fail to subsume* `hasType_substAt_le`; a corollary `hasType_substAt_le_of_multi` now machine-confirms
the subsumption.

Key simplification vs the plan: **no per-level `NoGenAt l h` is threaded.** For a σ-range level
`l < lvl` (the new disjunct), `NoGenAt l h` is *free* via the existing `noGenAt_of_lt` (reachable
gen levels are all `≥ lvl > l`); ambient only grows going down, so `l < lvl ≤ lvl'` discharges every
bound-type `l < lvl'` obligation and the `let_poly` gen-level dodge. The `l = ℓ` disjunct is
discharged by the derivation-level `NoGenAt ℓ h` (`hng`) exactly as in `_le`. Only the var arm needs
a genuine per-level fact — `PolyAboveFV l Γ e` — for capture avoidance against context schemes.

This means the readiness-construction side conditions the closure promise must bound are just
`l < lvl` and `PolyAboveFV l` per arg level — no derivation-indexed `NoGenAt` obligation on the
promise. Simplifies Phase 2/3 accordingly (update §2/§3's promise phrasing when integrating).

## Supporting helper added

`ctxWfV_substCtxAt_lt` — the `σ`-levels-`< L` variant of `ctxWfV_substCtxAt` (the existing one needs
`≤ ℓ` with `ℓ < L`; the let_poly arm now supplies `< lvl` directly).

## Where it lives / next

Kept in the spike file for Phase 1 (G1 methodology). Phase 2 promotes `hasType_substAt_multi` +
`ctxWfV_substCtxAt_lt` into `Typing.lean` and strengthens `genAtV_closure_ready_value_node`'s promise
to the floor form, consuming this lemma. Ambient-monotonicity is already `noGenAt_of_lt` (no new
lemma needed); floor-nesting reduces to it (inner floor `= lvl'_y > ambient(y) ≥ lvl'_x =` outer
floor).
