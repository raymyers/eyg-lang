---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 3b: substitution-commutation wall removed (both magnitude- and level-native); the non-vacuous let_poly arm fired in isolation; exact residual gap machine-grounded
status: two green additive commits landed on top of 3261754c; the full hasType_substAt induction is blocked only by a missing ambient-level-tracking judgment (n ≤ n_let), now pinned precisely — NOT open mathematics
kind: progress
component: lean (Eyg/Types/{Scheme,Generalization}.lean)
---

# G1 Phase 3b: the `hasType_subst` `let_poly` wall's substitution-commutation is removed; the residual gap is a level-tracking judgment

Continuation of `progress/2026-07-08-G1-phase3b-scheme-level-field-and-substAt-ported.md`. That
session (batch `lake build` only) landed `subst_instantiateV`/`CtxWfV` and pinned the remaining work
as "level-parameterize `hasType_subst`". This session **had Lean tool access** and used it to (a)
build the level-native `GeneralizesAtV` keystone, (b) fire the `hasType_subst` `let_poly` arm
non-vacuously in isolation on the *existing* judgment, and (c) machine-ground the exact one hypothesis
a full induction still lacks. Both the wall's *substitution-commutation* (the thing
`generalizes_subst_false` proves impossible for the flat encoding) is now discharged, and the residual
blocker is reduced from "open" to a specific, additive piece of judgment plumbing.

## Landed, two commits

### 1. Level-native `GeneralizesAtV` + unconditional substitution-stability

- `Ty.substAt_var_self` (`Scheme.lean`): `substAt ℓ (fun i => .var ℓ i) t = t` — the level-native
  analog of `subst_id`; the `arity = 0` witness below.
- `GeneralizesAtV ℓ s d` (`Generalization.lean`): `∀ args, ∃ τ, s.instantiateV args = substAt ℓ τ d`.
  The level-native mirror of `GeneralizesAt`. The magnitude `GeneralizesAt n s d` requires its witness
  `σ'` to **fix `[0,n)`** — a side-condition on the witness. `GeneralizesAtV`'s ambient-fixing clause
  is instead **structural**: `substAt ℓ` only ever rewrites `var ℓ _`, so for `ℓ ≠ 0` it fixes the
  ambient level-`0` scope automatically (`substAt_fixes_zero`).
- `genAtV_generalizesAtV`: `genAtV ℓ d` generalizes `d` at level `ℓ`.
- **`genAtV_substSchemeV_generalizesAtV`** — the keystone: for an **arbitrary** ambient (level-`0`)
  `σ`, `substSchemeV σ (genAtV ℓ d)` still generalizes `subst σ d` at level `ℓ`, with **no
  `LevelMap`/`hclean`/`ℓ ≠ 0` premise whatsoever**. `substSchemeV` only rewrites the body's level-`0`
  content while `genAtV`/`instantiateV` quantify at level `ℓ`, so an ambient substitution structurally
  cannot collide a generalized level-`ℓ` variable into the context. **This is precisely the
  implication `generalizes_subst_false` machine-checks is FALSE for the declarative `Generalizes` on
  the flat encoding — trivial here, on the real 12-former `Ty`/`Scheme`.** The substitution-commutation
  half of the wall is removed.

Commit 1: `lake build` 1774, spec 104/104, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`.

### 2. The `hasType_subst` `let_poly` arm, fired non-vacuously (isolated, on the existing `HasType`)

- `substCtx_cons_genAt` (`Generalization.lean`): under `LevelMap n σ`,
  `substCtx σ ((x, genAt n defnTy) :: Γ) = (x, genAt n (subst σ defnTy)) :: substCtx σ Γ`
  (via the *existing* magnitude `genAt_substScheme`). This is the exact equation a `hasType_subst`
  body-IH must match to reconstruct a `let_poly` node.
- **`hasType_substLM_letPoly`**: given `LevelMap n σ` at the let's stored level `n`, `CtxWf n Γ`, and
  the two substituted sub-derivations (`defn : subst σ defnTy`; `body` under the substituted
  generalized binding), the whole `Let`-binds-a-`Lambda` node reconstructs via `HasType.let_poly`
  (`CtxWf n (substCtx σ Γ)` re-established by `ctxWf_substCtx`). `noLambdaLet` is required **only on
  the inner lambda body `lbody`** — the rule's genuine restriction — **not on the whole term**. The
  general `hasType_subst` cannot even reach this term (its `noLambdaLet` on the whole term is `False`
  the moment a `let` binds a `Lambda`); this lemma discharges the arm the general lemma leaves vacuous.

Commit 2: `lake build` 1774, spec 104/104, axioms unchanged, no `sorry`.

## The exact residual gap — machine-grounded, not hand-argued

I worked through the full `hasType_substAt` induction (generalized over the ambient level `n`, with
`Ty.LevelMap n σ` and `CtxWf n Γ` threaded) by hand against the actual rule set. Every arm goes
through with the *existing* magnitude machinery **except for one hypothesis in the `let_poly` arm**:

- **`var`/`builtin`**: `subst_instantiate'` (already proved), unchanged — the ambient `σ` here is a
  `LevelMap`, strictly more restrictive than the arbitrary `σ` those already handle.
- **`lam`/`let_`**: descend under a binder introducing a mono binding of type `argTy`/`defnTy`. To keep
  `CtxWf` we bump the threaded level to `n' = max(n, 1 + maxFV(argTy))`; `LevelMap.mono` and
  `CtxWf.mono` lift both `σ` and the tail to `n'`, and `ctxWf_cons` re-assembles. Clean.
- **`let_poly`** (stored level `n_let`, premise `CtxWf n_let Γ`): reconstruct at `n_let` via
  `hasType_substLM_letPoly`. This needs `genAt_substScheme`/`ctxWf_substCtx` at `n_let`, i.e.
  **`LevelMap n_let σ`**. We hold `LevelMap n σ`. `LevelMap.mono` lifts it **upward** only:
  `LevelMap n σ → LevelMap n_let σ` requires **`n ≤ n_let`**. That is the *sole* missing fact.

`n ≤ n_let` says: a `let_poly`'s stored generalization level is at least the ambient de-Bruijn level
at its position — the standard well-formedness of a de-Bruijn-level generalization discipline (each
nested `let` generalizes at a *fresh* level above everything in scope). It is **true of every
well-formed derivation**, but `HasType.let_poly` records only `n_let` and `CtxWf n_let Γ`, **not the
ambient level**, so it cannot be derived from the current judgment. The two lemmas above are exactly
the induction step *modulo* this one hypothesis — supplied here as `LevelMap n σ` at the let's own
`n`, which a caller who knows `n = n_let` can give, but a generic induction cannot.

### Why this is the whole gap (and why the down-shift wall does NOT reappear here)

The 2026-06-19 "foundational wall" note located the obstruction in the **readiness keystone**
(`closure_typed_of_lambda_subst` → `genAt_closure_ready`), where the substitution is the
`instantiate` witness `σ_args`, a **down-shift**, which is not a `LevelMap`, so `genAt_substScheme`
cannot apply. That is a real wall — **for value/readiness typing**. It is a *different* lemma from the
term-substitution `hasType_subst`. In `hasType_subst` the ambient `σ` is a parameter we are free to
constrain to a `LevelMap`; we never form a down-shift. So the term-substitution `let_poly` arm has
**no down-shift wall** — only the `n ≤ n_let` bookkeeping gap. (The V-world `subst_instantiateV`/
`GeneralizesAtV` additionally removes the *readiness* down-shift wall, since `substAt ℓ` leaves
disjoint levels untouched — but wiring that into the readiness keystone is later Phase 3b/4 work.)

## What closes it: a level-tracking judgment (the next concrete deliverable)

Add a judgment `HasTypeAt (lvl : Nat) : Ctx → Node m → Ty → Ty → Prop`, parallel/additive to
`HasType`, that threads the ambient de-Bruijn level:

- `let_poly` generalizes at **exactly** `lvl` (stores `genAt lvl defnTy` / `genAtV lvl defnTy`, or a
  `GeneralizesAt lvl` / `GeneralizesAtV lvl` predicate), records `CtxWf lvl Γ`, and types its body at
  `lvl + 1` (or at `lvl` with the fresh band above — pick per the level-redesign note);
- `lam`/`let_` bump `lvl` past the bound type's free variables when descending;
- every other constructor passes `lvl` through unchanged.

Then `hasType_substAt` threads `LevelMap lvl σ`, and in the `let_poly` arm `n_let = lvl` **by
construction**, so `n ≤ n_let` is `rfl` and `hasType_substLM_letPoly` applies directly, non-vacuously,
for arbitrarily deep nesting. This is the missing plumbing — additive, ~25 constructors mirroring
`HasType`, mechanical modulo the four interesting arms (`var`, `lam`/`let_`, `let_poly`) whose proofs
are the lemmas already landed. It does not touch `HasType`/`hasType_subst`/soundness, so it cannot
regress the 104/104 spec.

**Design choice to settle first:** whether `HasTypeAt` should reuse the magnitude `genAt`/`CtxWf`
(reusing `genAt_substScheme`/`hasType_substLM_letPoly` verbatim — the fastest path to a *proved*
non-vacuous nested `hasType_substAt`) or the level-native `genAtV`/`CtxWfV`/`GeneralizesAtV`
(the endgame representation, needed anyway for the readiness keystone's down-shift removal). The
magnitude route is strictly less code and already fully supported by landed lemmas; the level-native
route is the one that also unblocks Phases 4–7. Recommendation: prototype the magnitude route first
(fast GO on "nested `hasType_substAt` is provable"), then migrate to `genAtV` once the shape is fixed.

## Current state

Tree is green at HEAD (two commits this session on top of `3261754c`): `lake build` 1774 jobs,
`lake exe spec` 104/104 on all three lines, `#print axioms` for `soundness`/`soundness_evalR` =
`[propext, Classical.choice, Quot.sound]`, no `sorry` in `Eyg/Types/*.lean`. Everything landed is
purely additive — `HasType`, `hasType_subst`, `HasType.let_poly`, `genAt`/`instantiate`/`GeneralizesAt`
and all soundness declarations are untouched. This note plus the plan checklist update are the only
further changes.
