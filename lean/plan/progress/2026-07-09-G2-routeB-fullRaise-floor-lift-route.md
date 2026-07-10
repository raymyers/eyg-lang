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

## Sharp boundary (traced concretely with `instantiateV_raiseScheme_U`)

**What closes — every binding whose `retTy` levels are `< its sublevel lvl'` (all combinator
polymorphism).** For `let a = \x.x in \w. a w`, `a` is consumed at `[.var 2 0]` (level 2 = `w`'s
level). If the derivation chose `a`'s sublevel `lvl' = 2`, the floor condition `2 < lvl'` fails.
Fix: `fullRaise` `a`'s stored derivation `2 → 2+o`. Since `a`'s `retTy = .var 1 0` (level `1 < 2`),
`raiseTy 2 o` **fixes `retTy`** (`raiseTy_eq_self_of_levels_lt`) — `a`'s advertised type is unchanged
and its floor now clears the arg. The floor keystone then discharges. No `ArgsDisc`, no statement
change.

**Residual hard case — the interleaving.** A binding whose `retTy` carries an *inner-lambda-binder*
level `m ≥ lvl'` (e.g. a body returning `\w.w : .var m 0 → …` with `m ≥ lvl'`), consumed at an arg
`≥ m`. Raising the floor past `m` would move `retTy`'s level `m`, changing the advertised type — the
same interleaving G16 hit. **Open question: is this case reachable by a well-typed program?** If
provably unreachable (an invariant like "a binding actually *instantiated* at level `≥ m` cannot have
`m` escape into its own `retTy`"), route B closes fully. If a concrete reachable program forces it,
that is the refutation → route A (per-binding floor promise, disciplined derivations) or a
gen-level/ambient-decoupling rule change is forced.

## Sub-lemmas the closing case needs (mutual, next session)

- **`hasTypeV_raiseTy` / `envWf_raiseCtx_U`** (mutual): `HasTypeV v τ → HasTypeV v (raiseTy t o τ)` and
  `EnvWf env Γ → EnvWf env (raiseCtx_U t o Γ)`, `1 ≤ t`. The value-level analog of `hasType_fullRaise`
  — a mutual induction over the `HasTypeV`/`EnvWf` structure (closure arm delegates to
  `hasType_fullRaise` on the stored body + `envWf_raiseCtx_U` on the captured env; `instantiateV_
  raiseScheme_U` handles the readiness-promise arm). This is the concrete build. Substantial but
  well-defined.
- Then `hasTypeV_closure_raise_floor` (lift sublevel, fix type) is a corollary for the closing case.

## Status

**Prove, not refute** for the closing case (V7 + the trace above); the residual interleaving case is
a genuine open reachability question — the honest refutation surface. The crux raise machinery is
**already landed** (`hasType_fullRaise`). Next session: the mutual `hasTypeV_raiseTy`/`envWf_raiseCtx_U`,
then decide the residual case by proving unreachability or constructing the witness.
