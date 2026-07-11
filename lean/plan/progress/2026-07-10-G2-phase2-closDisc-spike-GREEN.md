# G2 Phase 2 — `ClosDisc` front-door discipline + universal readiness, GREEN

Date: 2026-07-10. `Eyg/Types/G2DiscSpike.lean`, no sorry, axioms
`[propext, Classical.choice, Quot.sound]`. Additive; validated with `lake env lean` (independent of
the WIP `Soundness.lean`). Phase 0 signed off by the user: **bolt the discipline on at the front
door** (restrict the entry premise), not a rule change.

## `ClosDisc` — the entry-premise restriction

A `HasType`-derivation-indexed predicate (`NoGenAt`-shaped), the front-door condition that confines
`soundness`'s entry to the derivations a Rémy/OCaml-style inferencer produces:

- `lam` / `let_poly` arms additionally record `retTy.levels < lvl' ∧ εb.levels < lvl'` — the CLOSING
  case (`argTy < lvl'` is already forced by the `HasType.lam` rule).
- **Recurses into lambda/defn bodies** (unlike `HasTypeRT`). It is a *static* whole-derivation
  property, so it is storable on a closure value and consumed as-is at apply time — dissolving the
  G27–G31 storability wall.
- `var`/`builtin`/atomics are **unconditional leaves**.

### Key simplification over the plan's `ArgsDisc`

The plan (§2) designed `ArgsDisc` with a per-binding **floor carrier** `F` threaded alongside `Γ`,
because it consumed the *floor* keystone (which still carries an args condition). Finding (7)'s
**universal-closing lemma** discharges readiness at **any** args with **no** args condition — so the
`var`/`builtin` arms need record nothing, and **there is no floor carrier to thread**. `ClosDisc`
supersedes `ArgsDisc`; the user's "use a ctx struct if you thread a lot" hint turned out unnecessary —
there is nothing to thread.

## The readiness payoff

- `argsRaiseOffset args` + `argsRaiseOffset_pos` / `lt_of_mem_args` — pick a raise offset dominating
  every level in `args` (via `foldr max`), so the universal-closing lemma applies at arbitrary args.
- `closDisc_closure_ready_any` — for a closing-case closure, `HasType ℓ Γ ⟨lam⟩
  ((genAtV ℓ defnTy).instantiateV args) ε` for **every** `args`, no args condition.
- `closDisc_closure_ready_value` — the value-level readiness (mirrors `genAtV_closure_ready_value`,
  universal): `∀ args, HasTypeV (Closure x lbody env) ((genAtV ℓ defnTy).instantiateV args)`. This is
  exactly the promise a discipline-widened `EnvWf.cons` will store once its `l = 0 ∨ l = s.level` bound
  is dropped.

## Two residual hypotheses (Phase-3 threading)

`closDisc_closure_ready_value` still takes two standard captured-context invariants as hypotheses:

- `hΓwf : CtxWfV ℓ Γ` — recorded on the `let_poly` node (`hcw`); `CtxWfV lvl' Γ` follows by `ℓ < lvl'`.
- `hΓsl : ∀ b ∈ Γ, b.2.level < lvl'` — the captured schemes' *gen levels* below the sublevel. A runtime
  well-formedness fact (gen levels grow inward), to be threaded in Phase 3.
- `hΓpa : ∀ l, PolyAboveFV l Γ ⟨lam⟩` — capture-avoidance. **Risk flagged:** `∀ l` PolyAboveFV
  effectively forces the captured `Γ` to be **mono-only** (a poly binding has `s.level = l` for some
  `l`, failing `s.level ≠ l`). If reachable closures genuinely capture *polymorphic* bindings that
  their body uses, the universal route may not cover them and the floor route (or a per-arg-level
  `PolyAboveFV`) is needed there. Must be checked when Phase 3 supplies `hΓpa` from the real context.

## Deferred

Tagging the canonical disciplined programs (`r1`, `v5`, `v6` — already disciplined derivations) with
`ClosDisc` explicitly is deferred to Phase 3: reconstructing `ClosDisc` at a concrete `let_poly` node
in isolation fights dependent-index elaboration; the consumption site in Phase 3 has the context set up
for the inversion. `W2` (`w2_interleave_body`) is the derivation the discipline *excludes* (its `\w`
binder level 3 = `g`'s gen level 3 → no `hret` proof).

## Next (Phase 3)

Widen `EnvWf.cons` to the universal promise, store `ClosDisc` on `HasTypeV.closure`, swap
`MStateWf`/`StackWf*`/frames RT → `ClosDisc`, swap `soundness`'s entry premise `HasTypeRT → ClosDisc`,
and discharge `hΓpa`/`hΓsl` from runtime well-formedness — settling the mono-only-`hΓpa` risk first
(it may force keeping the floor route for poly-capturing closures). Pair Session-A (non-Soundness cone
green) / Session-B (Soundness) per the authorized pattern.
