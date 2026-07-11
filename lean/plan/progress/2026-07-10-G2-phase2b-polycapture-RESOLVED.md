# G2 Phase 2b — poly-capture readiness RESOLVED (hybrid, GREEN)

Date: 2026-07-10. `Eyg/Types/G2DiscSpike.lean`, no sorry, axioms
`[propext, Classical.choice, Quot.sound]`. Additive; `lake env lean` (independent of WIP
`Soundness.lean`). Resolves the risk confirmed earlier the same day.

## The settled args condition — Γ-free, Rémy-shaped

`ClosDisc.var`/`.builtin` now carry

```
hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ s.level ≤ l
```

This is **carrier-free**: it mentions only the looked-up scheme `s` and the instantiation `args` — no
context, no floor list. It is exactly what a Rémy/OCaml inferencer produces (a scheme is instantiated
at fresh unification vars at the *current* level `≥ s.level`, or at generalized-away level `0`), so it
rejects nothing legitimate. It strictly generalizes the old `HasTypeRT` bound `l = 0 ∨ l = s.level`
(now `≤` instead of `=`), which is what lets it cross the G30/W1 wall (arg level 2 `≥` scheme level 1).

## The def-site ↔ use-site bridge (plan risk #1/#3, discharged)

The promise is *established* at a closure's `let_poly` (def-site context `Γ_b` known) but *consumed* at
a `b @ args` var node (use-site). The bridge that makes the Γ-free condition sufficient:

`polyAboveFV_of_argCond` : `(l = 0 ∨ ℓ ≤ l)` + `CtxPolyBd Γ` + `CtxWfV ℓ Γ` ⟹ `PolyAboveFV l Γ e`
(`ℓ = s.level` = the closure's gen level). A captured poly binding has level `≠ 0` (`CtxPolyBd`) and
`< ℓ ≤ l` (`CtxWfV ℓ Γ`), hence `≠ l`; the `l = 0` case is `≠ 0` directly.

Key reuse: this needs **no new runtime invariant** — `CtxPolyBd` (and `polyAboveFV_of_ctxPolyBd`)
already exist in `Typing.lean` and are already threaded by the current architecture
(`genAtV_closure_ready_value_node` consumes them). The freshness the plan worried about *is*
`CtxPolyBd` + `CtxWfV`.

## The readiness lemmas

- `genAtV_ready_polyaware` — `genAtV_instantiate_lam_ready_universal` with its `∀ l` mono-only `hΓpa`
  split into `PolyAboveFV ℓ Γ` (at the gen level) + a per-arg-level `PolyAboveFV`. Identical raise +
  floor-keystone mechanism; now covers poly-capturing closures.
- `closDisc_closure_ready_value_hybrid` — the promise a discipline-widened `EnvWf.cons` stores:
  `∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ ℓ ≤ l) → HasTypeV (Closure x lbody env)
  ((genAtV ℓ defnTy).instantiateV args)`. Combines the discipline (`retTy`/`εb`/`argTy < lvl'`) with
  the bridge; carrier-free. This is the poly-capture generalization of Phase-2's
  `closDisc_closure_ready_value` (which is kept as the mono-fragment special case + `hΓpa_fails` the
  motivating witness).

## Corrections folded in

- Phase-2's "var/builtin unconditional, no carrier at all" was too strong: the `l = 0 ∨ s.level ≤ l`
  avoidance is recorded (still carrier-free). The **numeric floor** `l < lvl'` remains eliminated (the
  universal raise). `ArgsDisc` is partly superseded — its `polySchemeLevels` avoidance survives as this
  `s.level ≤ l` condition, but its per-binding floor list does not.

## Remaining hypotheses (Phase-3 threading)

`closDisc_closure_ready_value_hybrid` still takes `CtxPolyBd Γ`, `CtxWfV ℓ Γ`, and
`hΓsl : ∀ b ∈ Γ, b.2.level < lvl'` as hypotheses — all standard runtime context invariants the machine
well-formedness already carries (`CtxPolyBd` is live in the current tree). Discharging them from
`EnvWf`/`MStateWf` is Phase-3 plumbing, not new mathematics.

## Next (Phase 3, runtime re-thread)

Widen `EnvWf.cons`'s promise to the conditional form (`l = 0 ∨ s.level ≤ l`), store `ClosDisc` on
`HasTypeV.closure`, swap `MStateWf`/`StackWf*`/frames RT → `ClosDisc`, swap `soundness`'s entry premise
`HasTypeRT h → ClosDisc h`, and discharge readiness at the `let_poly` preservation site via
`closDisc_closure_ready_value_hybrid`. Session-A/B pairing; `Soundness.lean` red only across it.
