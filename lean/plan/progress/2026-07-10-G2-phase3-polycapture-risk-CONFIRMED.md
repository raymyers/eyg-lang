# G2 Phase 2b/3 de-risk — poly-capture breaks the universal route (CONFIRMED)

Date: 2026-07-10. `Eyg/Types/G2DiscSpike.lean`: `Γcap`, `hΓpa_fails` (`[propext]`). Additive; validated
with `lake env lean`. This is the compiler-first de-risking probe flagged at the end of the Phase-2
note, run **before** touching runtime files.

## The probe

`closDisc_closure_ready_value` (the universal readiness payoff) requires
`hΓpa : ∀ l, PolyAboveFV l Γ ⟨lam⟩`. `PolyAboveFV l Γ e` demands every free var's scheme satisfy
`arity = 0 ∨ (level ≠ 0 ∧ level ≠ l)`. For a **polymorphic** binding (`arity ≠ 0`) the right disjunct
fails at `l = level`, so `∀ l` is satisfiable only if the captured context is **mono-only**.

`hΓpa_fails` machine-confirms it: for `Γcap = [a : ∀α. α→α]` (a `genAtV 1` scheme) and body `\w. a`,
`¬ (∀ l, PolyAboveFV l Γcap ⟨\w. a⟩)` — it fails at `l = 1 = a`'s gen level.

## Why this matters — it is the ordinary case, not an edge case

A closure that captures **and uses** an outer polymorphic binding is the everyday nested-polymorphism
program:

```
let a = id in
let b = \w. a w in   -- b is let_poly; its captured Γ holds the poly `a`; its body uses `a`
b 5
```

`b`'s readiness (`EnvWf.cons`'s `∀ args, … → HasTypeV b_closure …`) is genuinely consumed at `b 5`, and
`b`'s captured context is poly. So the universal route — which needs mono capture — does **not**
discharge it. My Phase-2 "var/builtin arms are unconditional, no carrier" simplification was therefore
too aggressive: it is correct only for the mono-capture fragment.

## The fix (Phase 2b, before runtime)

Restore the plan's args-**avoidance** condition, but only that part:

- **`ClosDisc.var`/`.builtin`** gain `∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level ∨ PolyAboveFV l Γ ⟨.Variable x⟩`
  (the arg levels avoid captured poly scheme levels).
- **`EnvWf.cons`'s promise** becomes conditional on that same shape and, for the poly-capture fragment,
  is discharged by the **floor keystone** `genAtV_instantiate_lam_ready_floor` (whose `hargs` already
  carries `l = 0 ∨ l = ℓ ∨ (l < lvl' ∧ PolyAboveFV l Γ)`), not the fully-universal lemma.

Two corrections to the Phase-2 claim:

- The **numeric floor** `l < lvl'` **is** eliminated — the universal raise (`hasType_fullRaise`) lifts
  the sublevel above the args, so no per-binding floor number is threaded.
- The **`PolyAboveFV` set-avoidance is not** eliminated — it returns. So `ArgsDisc` is only *partly*
  superseded by `ClosDisc`.

Crucially the avoidance stays **carrier-free**: `Γ` is already a `HasType`-derivation index, so
`PolyAboveFV l Γ e` is computable from the index — there is no floor list to thread alongside `Γ` (the
user's ctx-struct concern remains unnecessary).

## Open sub-question for Phase 2b

The promise is established at `b`'s `let_poly` (def-site `Γ_b` known) but consumed at the `b @ args`
var node (use-site `Γ_use`). The recorded var-node condition is about `Γ_use ∋ b`; the promise needs
avoidance w.r.t. `Γ_b`. These must be shown to align — the plan flagged this as risk #1/#3. Since
`polySchemeLevels Γ_b` are all `< lvl_b = s.level` (captured from outer scopes, freshness), the
alignment should reduce to "arg levels `< s.level` avoid them, arg levels `≥ s.level` or `= 0` trivially
avoid them" — to be proven in Phase 2b. This is the real remaining mathematical content.

## Next

Phase 2b: augment `ClosDisc.var`/`.builtin`, prove the hybrid `closDisc_closure_ready_value` covering
poly capture via the floor keystone, and settle the def-site/use-site avoidance alignment. Only then
proceed to the Phase-3 runtime re-thread. Compiler-first (no in-head level reasoning).
