# G2 Phase 3 — started (ClosDisc promoted) + blast-radius map for the paired surgery

Date: 2026-07-10. `Eyg/Types/ClosDisc.lean` (builds green via `lake build Eyg.Types.ClosDisc`).

## Landed this turn (additive, green, committed)

`ClosDisc` promoted from the spike into its own build-tree module `Eyg/Types/ClosDisc.lean`
(depends only on `HasType`/`Typing`, so it sits **before `Runtime`**). Carries the Phase-2b
`var`/`builtin` arg condition `l = 0 ∨ s.level ≤ l`. `G2DiscSpike.lean` now imports it; the readiness
lemmas stay in the spike pending the `G2Spike`-chain promotion. This is the first, separable, green
atom of the runtime re-thread.

## Why the rest is one atomic breaking change (not committed this turn)

The two remaining Phase-3 edits are **entangled** and cannot be split:

1. **Add a `ClosDisc` field to `HasTypeV.closure`** (Runtime, mutual inductive).
2. **Widen `EnvWf.cons`'s promise** from `l = 0 ∨ l = s.level` to `l = 0 ∨ s.level ≤ l`.

Widening the promise's *condition* makes the promise **stronger** (must hold for more args), so every
**producer** of `EnvWf.cons` must now prove the stronger readiness — which needs
`closDisc_closure_ready_value_hybrid`, which needs the stored `ClosDisc` field from (1). So (1) and (2)
land together or not at all.

## Blast-radius map (for Session-A: non-Soundness cone green)

- `HasTypeV.closure` — **~12 sites** across `Runtime.lean` (def + inversions), `Substitution.lean`
  (`genAtV_closure_ready_value`/`_node` produce it), `Machine.lean`, `Soundness.lean`. Each construction
  gains a `ClosDisc` arg; each `cases`/inversion gains a binder.
- `EnvWf.cons` — **~20 construction sites** (Runtime, Substitution, Machine, Soundness). Each producer's
  promise proof must be re-established at the wider condition. Base/atomic values (arity 0) are trivial
  (`args = []`); the real work is the `let_poly` preservation producer → route through
  `closDisc_closure_ready_value_hybrid`, supplying `CtxPolyBd`/`CtxWfV`/`hΓsl` from the machine
  well-formedness already threaded.
- Also swap in `MStateWf`/`StackWf*`/frames: `HasTypeRT` → `ClosDisc` (`StackSegWf.assign` carries
  `HasTypeRT hbody`; `mStateWf_initial` entry premise). Retire `RTSubstReady`/`HasTypeRTAt`/
  `hasTypeRT_subst`/`HasTypeRT` once nothing consumes them.

### Session split (per the authorized pattern)

- **Session-A:** land (1)+(2) and re-green the whole non-`Soundness` cone (`Runtime`, `Substitution`,
  `Machine`, `Generalization`, …) with `Soundness.lean` the only red file. Validate each file with
  `lake env lean`; do **not** commit until the cone (minus Soundness) is green.
- **Session-B:** re-green `Soundness.lean` — the two closure-apply crux sites reduce to the mechanical
  `HasTypeV.closure` rebind + supplying the stored `ClosDisc`; var-preservation swaps `inv_var_rt` for
  the `ClosDisc` var-arm inversion; the `let_poly` case supplies the promise via
  `closDisc_closure_ready_value_hybrid`.

## Promotion still owed (can precede or accompany Session-A, all additive/green)

The readiness lemmas (`closDisc_closure_ready_value_hybrid`, `genAtV_ready_polyaware`,
`polyAboveFV_of_argCond`, `argsRaiseOffset*`) and the `G2Spike` chain they rest on
(`hasType_substAt_multi`, `genAtV_instantiate_lam_ready_floor`/`_universal`, the `raise*` helpers) must
be promoted from the spike files into the real tree (e.g. `Substitution.lean` / a new
`Eyg/Types/ClosDiscReady.lean` imported after `Runtime`) so Session-B can consume them.

## Next

Session-A. Compiler-first, `lake env lean` per file, commit only when the non-Soundness cone is green.
Watch the `ClosDisc` dependent-inversion friction (seen in the Phase-2 inhabitation) at the
`Soundness` consumption sites — set up the node concretely before `cases`.
