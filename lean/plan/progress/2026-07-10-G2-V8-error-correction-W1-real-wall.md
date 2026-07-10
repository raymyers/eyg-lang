# G2 correction — V8 was NOT a wall witness; W1 (G30) is the real one

Date: 2026-07-10. Machine-checked (`G2Validation.lean`: `w1`, `w1_old_condition_fails`,
`w1_floor_condition_holds`). **This note corrects a reasoning error in the two `2026-07-10-G2-B1*`
notes** — do not act on their "B1 blocked → need decoupling" conclusion.

## The error

I claimed V8 (`\x. let g=\y.y in \w. g x` at `[.var 2 0]`) is a case where readiness can't be
established without decoupling the `let_poly` rule. **Wrong**, for two reasons pinned by the ground
truth (`HasTypeRT.var`, Typing.lean:968, records args condition `l = 0 ∨ l = s.level`):

1. A closure's own `HasTypeV.closure` `hfv` forces the instantiation arg's levels **below** its
   sublevel `lvl'`, and every inner gen level sits `≥ lvl'` — so the arg is always below the inner
   gen levels: **no capture**. V8's arg (2) is below its sublevel (≥3); the floor keystone handles it.
2. V8's inner `g = \y.y` is closed — `x` never flows into `g`'s generalized region — so there is no
   capture structure at all.

The `v8_moving_g_moves_retTy` / `v8_fixing_retTy_strands_g` lemmas are true arithmetic but attached to
a scenario that isn't a real blocked readiness obligation. My "B1 blocked" conclusion was premature.

## The real wall (W1 = G30), machine-checked

The genuine wall is **maintaining `HasTypeRT` across a closure-apply**. `let a = \x.x in \w. a w`:
applying `\w. a w` makes `a w` the control, instantiating `a` at `[w = .var 2 0]` (level 2).
`HasTypeRT.var` needs `args ⊆ {0, s.level=1}` — and `2 ∉ {0,1}` (`w1_old_condition_fails`). That is
why the old `{0,s.level}` `HasTypeRT` cannot be maintained — the documented G30 wall, now a permanent
regression.

The **floor-widened** condition `l = 0 ∨ l = 1 ∨ l < B` with `B =` a's defn sublevel `3` **holds**
(`w1_floor_condition_holds`) — crossing the wall for this args-disciplined derivation.

## Corrected status of route B

- **G30 closes.** `a`'s `retTy = .var 1 0` (low), so even an undisciplined derivation (sublevel 2)
  raises a's floor to 3 with `retTy` fixed — the fullRaise-lifts-floor route works here.
- **The genuine residual is still the escaping-`retTy` case** (`a`'s `retTy` carries an *inner
  lambda-binder* level `≥ a`'s sublevel, e.g. `a = \x.\w.w`), where raising a's floor would move that
  level. **Whether that is reachable AND blocked is STILL OPEN** — V8 did not test it (its arg was
  below the sublevel). This is the correct next witness to build.
- **The maintenance question** (does the floor condition survive an arbitrary derivation's
  closure-applies?) reduces to: is `w`'s level `< a`'s floor at every use? That is the args-discipline
  (route A) unless re-leveling (raise, or the decoupling) establishes it — and re-leveling is only
  blocked in the escaping-`retTy` residual, which is unbuilt.

## Next (compiler-first, no more in-head level reasoning)

Build the escaping-`retTy` residual witness (`a` returning an inner lambda whose binder escapes at a
level `≥ a`'s sublevel), instantiated so its floor would need raising past that level, and test
whether `hasType_fullRaise` closes it or genuinely blocks. That — not V8 — decides whether route B is
unconditionally achievable with existing machinery or needs the decoupling.
