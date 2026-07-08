---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 3b: the readiness keystone's down-shift wall is confirmed removed at the mathematics level; two distinct, precisely-located plumbing obstructions remain (neither is the down-shift wall)
status: one green additive commit (substAt_instantiateV, the cross-level instantiation commutation); the level-native readiness keystone does NOT close this session — obstructions (A) substAt-ℓ re-typing induction + (B) Runtime.lean's magnitude-HasType value judgment, both multi-session plumbing, both distinct from the down-shift mathematics
kind: progress
component: lean (Eyg/Types/Scheme.lean)
---

# G1 Phase 3b: the readiness keystone — down-shift wall removed (math), two plumbing obstructions located

Continuation of `progress/2026-07-08-G1-phase3b-HasTypeAt-nested-arm-landed.md`. That session solved the
**term-substitution** side (`HasTypeAt`/`hasTypeAt_subst`, non-vacuous arbitrary-depth `let_poly` arm)
and flagged the **readiness/value-typing** side as the remaining Phase 3b-tail / Phase 4 work. This
session determined precisely whether the level-native machinery
(`genAtV`/`instantiateV`/`substSchemeV`, `GeneralizesAtV`, `genAtV_substSchemeV_generalizesAtV`,
`CtxWfV`, `substAt`/`substAt_substAt_comm`) suffices to prove a level-native readiness keystone
(`generalizesAtV_closure_ready`) that discharges `EnvWf.cons`'s obligation for a **nested** generalized
lambda, where the original `generalizes_closure_ready`/`genAt_closure_ready` chain is blocked.

**Verdict.** The 2026-06-19 *down-shift* wall is confirmed **removed at the mathematics level** — every
substitution-commutation the readiness keystone rests on is provable level-natively (this session added
the last missing one). But the readiness keystone itself does **not** close additively this session,
blocked by **two distinct obstructions, neither of which is the down-shift wall**, each a multi-session
piece of judgment plumbing. This matches — and sharpens — the prior notes' own forecast that the
readiness keystone needs the level-native migration + a value-judgment relaxation.

## Why the original chain is blocked, re-confirmed from the code (step 1)

`generalizes_closure_ready` (`Generalization.lean:135`) → `closure_typed_of_lambda_subst`
(`Substitution.lean:148`) → `hasType_subst` (`Substitution.lean:62`). For each instantiation `args`,
`Generalizes s Γ defnTy` supplies a `σ` with `s.instantiate args = subst σ defnTy` **and**
`substCtx σ Γ = Γ`; `hasType_subst σ hlam` then re-types the closure body under `σ`. This needs
`noLambdaLet body`. For a nested body (`let inner = \y…\ in …`, a `Let`-binds-`Lambda`) `noLambdaLet` is
`False` (`Tree.lean:125`), so the arm is reachable only vacuously — exactly the 2026-06-19 finding.

The substitution `σ` here is `genAt n defnTy`'s **instantiation witness** (`genAt_generalizesAt`,
`Generalization.lean:267`): it **fixes the ambient region `[0,n)`** and **moves the generalized region
`[n,∞)`** into `args`. This is the precise sense in which it is a **down-shift** / **anti-`LevelMap`**:
`Ty.LevelMap n σ` (`Generalization.lean:218`) demands the *opposite* — fix `[n,∞)`, keep `[0,n)` within
`[0,n)`. `generalizes_subst_false` (`Generalization.lean:679`) machine-checks that no *arbitrary* `σ`
discharges the flat-encoding `let_poly` commutation.

## Why the just-landed `hasTypeAt_subst` does NOT discharge the readiness keystone

`hasTypeAt_subst` (`TypingAt.lean:141`) re-types under `Ty.subst σ` (= `substAt 0 σ`, a level-`0`
ambient substitution) constrained to `Ty.LevelMap lvl σ`. It traded `hasType_subst`'s *arbitrary* `σ`
for a `LevelMap` precisely to make the `let_poly` arm go through (via `genAt_substScheme`, which needs
`LevelMap`). But the readiness keystone re-types under the **instantiation** substitution, which is
**anti-`LevelMap`** (moves the generalized region). So `hasTypeAt_subst` is structurally the wrong tool
— it is an *ambient/weakening* substitution lemma, not an *instantiation* one. At the top level
`lvl = 0` it degenerates completely: `LevelMap 0 σ` forces `σ = id` (fixes every index), so it can only
re-type under the identity — no non-trivial instantiation. (This is the same degeneration the prior
note observed for `hInner_subst`, which therefore had to be demonstrated at `lvl = 1`.)

The level-native resolution is that these two motions become **orthogonal** (distinct levels) rather
than complementary on one flat axis: instantiating the outer scheme at its own level `ℓ_out` via
`substAt ℓ_out` leaves the ambient (level `0`) and the inner-generalized (level `ℓ_in ≠ ℓ_out`) regions
structurally untouched — no down-shift.

## What this session landed (step 2, partial): `substAt_instantiateV` — the cross-level commutation

`Scheme.substAt_instantiateV` (`Scheme.lean`, one green additive commit; plus `Scheme.substSchemeVAt`,
the level-`ℓ` analog of `substSchemeV`):

```
theorem substAt_instantiateV {ℓ ℓ' : Nat} (hne : ℓ' ≠ ℓ) {σ : Nat → Ty}
    (hclean : ∀ i, ∀ j, j ∉ Ty.freeVarsAt ℓ (σ i)) (d : Ty) (args : List Ty) :
    Ty.substAt ℓ' σ ((genAtV ℓ d).instantiateV args)
      = (substSchemeVAt ℓ' σ (genAtV ℓ d)).instantiateV (args.map (Ty.substAt ℓ' σ))
```

This generalizes `subst_instantiateV` (`Scheme.lean:733`, which is the `ℓ' = 0` / level-`0`-ambient
case) to an **arbitrary level-`ℓ'`** outer substitution pushed through a scheme generalized at a
*different* level `ℓ`. It is exactly the `var`/`builtin`-arm commutation a level-native re-typing under
the **outer scheme's instantiation** (`substAt ℓ_out`, `ℓ_out ≠ 0`) would consume for a *nested* inner
scheme at level `ℓ_in = ℓ`. Proof mirrors `subst_instantiateV` via `substAt_substAt_comm` (the
cross-level commutation, needing only level-disjointness `ℓ' ≠ ℓ` + freshness `hclean`, the latter
discharged in the real system by `clean_of_levels_lt` from a `CtxWfV` bound). It confirms, machine-
checked on the real 12-former `Ty`/`Scheme`, that the down-shift wall does **not** reappear for the
instantiation substitution once generalization levels are distinct — the readiness-keystone counterpart
of `genAtV_substSchemeV_generalizesAtV` (which already did this for the *stored-scheme* commutation).

**So the mathematics half of the readiness keystone is complete**: both commutations it needs — the
stored-scheme one (`genAtV_substSchemeV_generalizesAtV`, unconditional) and the instantiated-type one
(`substAt_instantiateV`, only level-disjointness + freshness) — are proved level-natively.

## The two remaining obstructions (steps 2–3, why the keystone does NOT close this session)

Neither is the down-shift wall. Both are judgment plumbing that the plan already scopes to Phase
3b-tail / 4 / 5.

### (A) A full `substAt ℓ` re-typing induction on a `genAtV`-storing judgment is not yet built

To feed the readiness keystone we need `hasTypeAtV_substAt`: re-type a typing derivation under the
outer instantiation `substAt ℓ_out` (`ℓ_out ≠ 0`), with the closure's ambient context (level `0`)
**unchanged** (structurally fixed by `substAt ℓ_out`), and the nested inner `let_poly` (level `ℓ_in`)
reconstructed via `substAt_instantiateV` / a `substSchemeVAt`-based `genAtV` commutation. This is a full
parallel of `TypingAt.lean`'s induction, but:
- keyed on `substAt ℓ` (not `Ty.subst = substAt 0`),
- on a judgment that stores `genAtV ℓ_let defnTy` (not the magnitude `genAt`), so its `let_poly` arm
  commutes *unconditionally* in the level dimension — the current `HasTypeAt` deliberately took the
  *magnitude* `genAt`/`CtxWf` route (strictly less code, per the prior note), which stores level-`0`
  variables and re-types under level-`0` `subst`, so it cannot be reused here.

All the per-arm commutations are now proved (`substAt_substAt_comm`, `subst_instantiateV`,
`substAt_instantiateV`, `genAtV_substSchemeV_generalizesAtV`, `CtxWfV`/`ctxWfV_cons`,
`clean_of_levels_lt`), so this is *de-risked file-editing*, not open mathematics — but it is a
multi-session parallel judgment + induction, not a single-session additive slice.

### (B) `Runtime.lean`'s value judgment is stated on the magnitude `HasType` (with `noLambdaLet`)

Even with (A) solved, the keystone's conclusion `HasTypeV (Value.Closure x body env) τ` can be built
**only** via `HasTypeV.closure` (`Runtime.lean:63`), which demands a **magnitude**
`HasType ((x,.mono argTy) :: Γ) body retTy εb` (through `inv_lambda`, `Generation.lean:70`). The
depth-dependence is exact:

- **Depth 2** — outer body `let inner = \y.<noLambdaLet> in …`: the *inner* `let_poly`'s `lbody` has no
  lambda-let, so `noLambdaLet lbody` holds and the outer body **is** magnitude-`HasType`-typeable (as
  `hOuter` already witnesses, at `TypingAt.lean:259`, but note `hOuter` is under `HasTypeAt`; the
  magnitude derivation of the *outer body alone* also exists via `HasType.let_poly`). The **original
  keystone is nevertheless blocked** here (it needs `noLambdaLet` of the *whole* outer body, which is
  `False` — it binds a lambda). So a level-native keystone that closes depth 2 *would* be genuinely
  non-vacuous — the obstruction at depth 2 is purely (A).
- **Depth ≥ 3** with a polymorphically-used middle binding — e.g.
  `let a = \x. (let b = \y. (let c = \z.z in …c…c…) in …b…b…) in …`: generalizing `b` needs
  `HasType.let_poly` with `lbody = b`'s body = `let c = \z.z in …`, whose `noLambdaLet` is `False`. So
  `b` can only be bound **monomorphically** under magnitude `HasType`; if the program uses `b`
  polymorphically it does not type at all, and `HasTypeV.closure` for `a`'s closure is
  **unconstructible**. The value judgment cannot even *express* the deeply-nested closure's typing until
  `HasType.let_poly` drops `noLambdaLet` (Phase 4) or a parallel `HasTypeVAt`/`EnvWfAt` is built
  (Phase 5, itself recursive through the closure/env value forms).

(B) is a `Runtime.lean` (load-bearing, unmodifiable-this-milestone) dependence on the magnitude
`noLambdaLet`-restricted `HasType` — judgment plumbing, distinct from the down-shift mathematics, and
exactly the Phase 4/5 deliverables.

## Determination (steps 4–5)

- The **down-shift wall does NOT reappear level-natively** — confirmed at the mathematics level.
  `genAtV_substSchemeV_generalizesAtV` (stored-scheme, unconditional) + `substAt_instantiateV`
  (instantiated-type, level-disjoint + clean) are the two commutations the readiness keystone rests on,
  and both are proved on the real `Ty`/`Scheme`. This confirms the plan's central hypothesis.
- The **level-native readiness keystone does not close additively this session** — blocked by (A) a
  substAt-`ℓ` re-typing induction on a `genAtV`-storing judgment (de-risked but multi-session) and
  (B) `Runtime.lean`'s magnitude-`HasType` value judgment (Phase 4/5). Neither is the down-shift wall;
  both are anticipated plumbing. Per the plan's philosophy (and the 2026-06-19 precedent) this precise
  negative-with-located-obstruction, plus the new positive commutation `substAt_instantiateV`, is the
  honest outcome — forcing a large speculative parallel judgment + a `Runtime.lean` relaxation into one
  additive session would have left the tree red between sessions, which the Definition-of-done forbids.

## What closes it (continuation spec)

1. Migrate the level-tracking judgment to store `genAtV ℓ defnTy` (not magnitude `genAt`) and re-type
   under `substAt ℓ` — call it `HasTypeAtV` — reusing `substAt_instantiateV`/`substSchemeVAt`/
   `genAtV_substSchemeV_generalizesAtV`/`CtxWfV` for its arms. Then `hasTypeAtV_substAt` (arbitrary
   outer instantiation `substAt ℓ_out`) is provable non-vacuously for arbitrary depth.
2. `generalizesAtV_closure_ready` = compose `GeneralizesAtV` (each `instantiateV args` is a `substAt ℓ`
   instance) with a `closure_typed_of_lambda_substAt` (re-type via step 1, then build the closure).
3. Unblock (B): either Phase 4 (drop `noLambdaLet` from `HasType.let_poly`, making `HasTypeAtV` erase to
   `HasType` for arbitrary depth so `HasTypeV.closure` applies), or a parallel `HasTypeVAt`/`EnvWfAt`.
   Only then does the readiness keystone produce `HasTypeV (Closure …)` for depth ≥ 3.

## Current state

Tree green at HEAD (one commit this session on top of `485d8777`): `lake build` 1775 jobs, `lake exe
spec` 104/104 evaluation + 104/104 FBS≡interpreter + 21/21 round-trip + 21/21 CID, `#print axioms` for
`soundness`/`soundness_evalR` (and `substAt_instantiateV`) = `[propext, Classical.choice, Quot.sound]`,
no `sorry` in `Eyg/Types/*.lean`. Purely additive — `HasType`, `hasType_subst`, `HasType.let_poly`,
`Generalizes`, `generalizes_closure_ready`, `closure_typed_of_lambda_subst`, `HasTypeAt`/
`hasTypeAt_subst`, `Runtime.lean`, and `Soundness.lean` all untouched.
