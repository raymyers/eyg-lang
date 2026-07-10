# G2 route decision — B (unconditional), prove-or-refute the level raise

Date: 2026-07-09. Branch `lean-cslib-subproject`. User decision (Ray).

## Decision

Reject the `ArgsDisc`-conditional soundness (route A). Target **unconditional** soundness over the
full level-native `HasType` judgment — "something is wrong if we can't do that." First deliverable:
a prove-or-refute of whether `ArgsDisc` can be *avoided entirely*.

## What the current contract actually is (verified in-tree, not from the report)

- Committed `soundness`/`soundness_evalR` are **unconditional** over `hty : HasType [] prog τ ε`.
  `HasTypeRT` does **not** exist in committed `Soundness.lean`; the committed `MStateWf.E` types the
  running control with plain `HasType` (`git show HEAD:…Soundness.lean`, `mStateWf_E`).
- The level-native `HasType.let_poly` already has **no `noLambdaLet`** (Typing.lean:130) — the
  judgment already admits nested generalizable (value-restricted) lets. The report's Caveat 5 prose
  predates the level-native migration.
- The real restriction is `EnvWf.cons`'s readiness promise (`Runtime.lean:219`): it only guarantees
  the looked-up value is typeable at instantiations whose arg levels are all in `{0, s.level}`.
  Off-scheme instantiation levels (G30/G31) fall outside that bound. **That `{0,s.level}` bound is
  the wall**, not the top-level statement.
- `HasTypeRT` is a construct of the *working-tree WIP* migration (re-architecting `MStateWf.E` to
  carry a running-typing invariant); it is where the storability wall bites.

## The reduction (why B should be achievable)

Universal readiness = `∀ args, HasTypeV (Closure x body env) (s.instantiateV args)` with **no**
condition on args. Key fact: the runtime **value** carries no fixed inner gen levels — the *typing
derivation* does. So for each instantiation we may re-derive the body with inner gen levels chosen
**fresh above the incoming args**. Since argTy/retTy/context all have levels `< lvl'` while inner
gen levels are `≥ lvl'`, shifting levels `≥ lvl'` up by `N > max(args levels)` is invisible to the
scheme, the final type, and the context — it only pushes inner gen levels above the args, killing
capture. Then `hasType_substAt_multi` (proven this session — the multi-level tool G15/G16 lacked)
finishes.

So route B reduces to one lemma: **`hasType_shiftGE`** — shifting all levels `≥ c` up by `N`
preserves `HasType` (context/final-type unchanged when their levels are `< c`). This is the walled
G15/G16 "raise/relabel" metatheorem, now attackable with `hasType_substAt_multi`. If it goes through,
`ArgsDisc` and the `{0,s.level}` bound both vanish and soundness stays unconditional. If an arm
genuinely resists, that arm's obstruction is the refutation → fall back to route A.

## Evidence landed

**V7** (`G2Validation.lean`) — the decisive capture-prone case: a closure whose body has an **inner
generalizable let** (`\x. let g = \y.y in g x`, scheme `genAtV 1 (α→α)`) typed at the off-scheme
instantiation `[.var 2 0]`. Compiles; axioms `[propext, Quot.sound]`. The readiness derivation
generalizes the inner `g` at a **fresh** level (3 ≠ 2), sidestepping capture — machine-checked
demonstration that universal, `ArgsDisc`-free readiness holds even where the `substAt` route captures.

## Next

Attack `hasType_shiftGE` in a spike. Increments: define the level-`≥ c` shift on `Ty` (+ commutation
with `substAt`/`instantiateV`/`genAtV`), then the `HasType` equivariance induction, then universal
readiness, then wire into a universal `EnvWf.cons` promise. Refutation surface: the var-arm
instantiation relabel and the `let_poly` genAtV-arity preservation under the shift.
