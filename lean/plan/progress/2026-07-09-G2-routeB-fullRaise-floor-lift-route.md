# G2 route B — the concrete path: `hasType_fullRaise` (landed) lifts the floor, then the floor keystone

Date: 2026-07-09. Follows `2026-07-09-G2-routeB-unconditional-decision.md`. Key discovery: the raise
lemma the crux needs is **already largely built** (G16), and it composes with this session's floor
keystone into a route to unconditional readiness.

## What already exists (G13–G16, committed on this branch)

- `Ty.raiseTy t o` (Scheme.lean:1264) — shift every level `≥ t` by `o`; `raiseTy_eq_self_of_levels_lt`
  fixes types with all levels `< t`.
- `levels_raiseTy`, `length_filter_levels_raiseTy` (arity preserved, no freshness), `raiseTy_substAt_comm`
  (unconditional), `raiseTy_tyEquiv`, `raiseTy_effWeaken`, `instantiateV_genAtV_raiseTy` (Scheme.lean).
- `raiseScheme_U`/`raiseCtx_U` + lemmas, `instantiateV_raiseScheme_U`, `ctxWfV_raiseCtx_U` (Typing.lean).
- **`hasType_fullRaise`** (Typing.lean:2030): `1 ≤ t → HasType lvl Γ e τ ε → t ≤ lvl →
  HasType (lvl+o) (raiseCtx_U t o Γ) e (raiseTy t o τ) (raiseTy t o ε)`. Machine-checked, axiom-clean.
  The **uniform** derivation-level generalization-level raise.

G16 already identified the ground-args route (its "sharpest remaining route") but stopped: it framed
readiness as needing `NoGenAt` (old architecture) and proposed restricting `EnvWf.cons` to ground
runtime args. This session's `hasType_substAt_multi` + floor keystone remove the `NoGenAt` need and
handle non-ground off-scheme args directly, which reframes the route.

## The subtlety that makes ground-args-only insufficient

Runtime *evaluation* args are ground, but establishing `HasTypeV` of a **closure value whose body
references an env-polymorphic var** requires typing that body — which instantiates the env var at a
**non-ground off-scheme level**. Concretely, `HasTypeV (Closure "w" (a w) env)` at `.var 2 0 → .var 2 0`
must type `a w` with `a : genAtV 1 (α→α)` instantiated at `[.var 2 0]` (level 2 ∉ {0, 1}). So the
`{0,s.level}` promise genuinely fails and ground-only readiness does not suffice. This is the G30/G31
wall, precisely located.

## The route (uses landed machinery + this session's floor keystone)

`genAtV_instantiate_lam_ready_floor` (this session) types the lookup at `[.var 2 0]` **iff**
`2 < floor(a)` where `floor(a) =` a's stored defn sublevel `lvl'`. That is a *per-binding, local*
condition — NOT the global `ArgsDisc` discipline. And it is **establishable post-hoc**:

`hasType_fullRaise` at threshold `t = lvl'`, offset `o` large, lifts a's stored body derivation to
sublevel `lvl'+o` **while fixing a's advertised type** — a's own gen vars sit at level `1 < t = lvl'`,
so `raiseTy lvl' o` leaves the scheme `genAtV 1 (α→α)` untouched (`raiseTy_eq_self_of_levels_lt`).
So: to consume readiness at off-scheme args, first `fullRaise` the env binding's stored derivation to
push its floor above the incoming args' levels, then apply the floor keystone. No `ArgsDisc`, no
statement change, no `{0,s.level}` bound.

## Sub-lemmas needed (next session, focused)

1. **`hasTypeV_closure_raise_floor`** — from `HasTypeV.closure` at sublevel `lvl'`, produce one at
   sublevel `lvl'+o` with the **same** type `τ`, via `hasType_fullRaise` on the stored body. Obstacle
   to clear: `raiseCtx_U t o Γ` must equal `Γ` (the closure's captured context), i.e. the captured
   `Γ` has all poly levels `< lvl'` — OR prove `EnvWf env Γ → EnvWf env (raiseCtx_U lvl' o Γ)`
   (readiness preserved under raise). One of these must hold for the stored env; likely provable since
   captured bindings were generalized below the capturing lambda's sublevel.
2. **Universal `EnvWf.cons` promise** — replace `∀ args, (levels ⊆ {0,s.level}) → HasTypeV v (s.inst
   args)` with the floor form `∀ args, (levels `l = 0 ∨ l = s.level ∨ l < floor) → …`, floor stored
   per binding; discharge at construction via the floor keystone, and at consumption raise-then-apply.
3. Wire into `MStateWf`/var-preservation; confirm the consumption site's args levels are always
   `< floor` after the raise (the raise is chosen per-consumption to make it so).

## Status

**Prove, not refute** (V7). The crux raise lemma is **already landed** (`hasType_fullRaise`, uniform
mode); the type-fixed two-modes wall G16 hit is **sidestepped** here because we raise the *env
binding's floor* (fixing its type, since its gen vars are below the threshold) rather than trying to
fix an interleaved retTy. Next session: the two sub-lemmas above, then the `EnvWf.cons` refactor.
