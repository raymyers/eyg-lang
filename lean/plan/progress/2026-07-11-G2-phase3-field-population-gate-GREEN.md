# G2 Phase 3 — field-population gate GREEN (ClosDisc survives raise + substAt)

Date: 2026-07-11. `Eyg/Types/G2ClosDiscReadySpike.lean`, no sorry, axioms
`[propext, Classical.choice, Quot.sound]` (`closDisc_substAt_multi`) /
`[propext, Quot.sound]` (`closDisc_fullRaise`). Additive; `lake env lean` (independent of WIP
`Soundness.lean`). Commit `ac842581`.

## Result

The finding-16 gap — *can the `ClosDisc hbody` field on `HasTypeV.closure` be supplied by the readiness
lemma?* — is **closed GREEN**. `ClosDisc` is preserved through **both** transforms the readiness lemma
applies to build the closure body derivation:

- `closDisc_fullRaise` — `hasType_fullRaise` companion. The uniform `+o` relabel of levels `≥ t` shifts
  every discipline bound `retTy/εb/argTy < lvl'` to `< lvl' + o`; the `var`/`builtin` args condition
  `l = 0 ∨ s.level ≤ l` survives because `raiseScheme_U` raises `.level` in lock-step with the raised
  args (case split on the two `raiseTy` guards → `omega`).
- `closDisc_substAt_multi` — `hasType_substAt_multi` companion. `lam`/`let_poly` bounds survive with
  **no new σ-condition** (a substituted level is either an original non-`ℓ` level `< lvl'`, or from `σ`
  at an `ℓ`-position where `ℓ ∈ retTy ⇒ ℓ < lvl'` and each `hσ` disjunct is `< lvl'`). The `var`/`builtin`
  args condition survives under one added σ-hypothesis `hσdisc : σ`-levels `0 ∨ ℓ ≤ l` — **exactly the
  widened `EnvWf.cons`/promise precondition** (`substSchemeVAt` preserves `.level` definitionally; a
  substituted arg level is `0`, or `≥ ℓ ≥ s.level` since `ℓ ∈ t ⇒ s.level ≤ ℓ`).

Both are **bundled** (`⟨h', ClosDisc h'⟩` at the transformed type, like `hasTypeRT_ctxConv`), so the
re-thread of the readiness lemmas will use *their* output derivation (not `hasType_*`'s opaque one) and
read off the `ClosDisc` directly.

## Two design wins over the dependent-inversion friction (the plan's stated risk)

1. **Induct on `ClosDisc`, not `NoGenAt`.** `HasType.lam`'s type does not mention the sublevel `lvl'`
   (it is buried in the body derivation), so `ClosDisc.lam`'s `retTy < lvl'` fields are *un-invertable*
   at a lam node — `cases` binds a fresh `lvl'✝` and cannot equate it (verified: the error is a
   heterogeneous `lvl'✝ = lvl'` the unifier won't solve). Inducting on `ClosDisc` directly yields those
   fields as induction data — no inversion.
2. **Drop `NoGenAt` entirely.** `hasType_substAt_multi` inducts on `NoGenAt ℓ h`; its *only* structural
   use is the `let_poly` arm's `lvl ≠ ℓ`. That follows from a **strict** numeric `ℓ < lvl` (threaded as
   a plain `Nat` inequality, propagated to every inner ambient since lam/let bodies descend to `≥` the
   current ambient). `noGenAt_of_lt` witnesses that `ℓ < lvl` is exactly what makes `NoGenAt` hold in the
   readiness setting (post-`argsRaiseOffset` raise). So no second derivation-indexed predicate is
   cross-inverted, and every level fact is `omega`-checked.

This is why the whole thing is machine-checked rather than argued in the head (cf. the V8 in-head
level error the task warned against).

## What this de-risks

The front-door discipline **closes for the storable form**, not just the readiness *type* (finding 14's
premature "RESOLVED"). The remaining work is now genuinely mechanical threading, no open math:

- **Re-thread the readiness lemmas** (`closDisc_closure_ready_value`/`_hybrid`, `genAtV_ready_polyaware`,
  `closDisc_closure_ready_any`): replace their internal `hasType_fullRaise` + `genAtV_instantiate_lam_
  ready_floor` (which calls `hasType_substAt_multi`) with the `closDisc_*` bundled companions, carry the
  `ClosDisc`, and pass it to `HasTypeV.closure`'s new field. Do this as an additive spike against a
  locally-migrated `Runtime.olean` (add the field; don't commit) before the breaking edit.
  - Note: `genAtV_instantiate_lam_ready_floor` currently wraps `hasType_substAt_multi`; the re-thread
    needs a `closDisc`-carrying variant of that wrapper too (mechanical — same substitution, now
    bundled). Feed `closDisc_substAt_multi`'s `hσdisc` from the promise's `l = 0 ∨ ℓ ≤ l` precondition.
- Then the **Session-A** breaking edit (unblocked): add the field to `HasTypeV.closure`, widen
  `EnvWf.cons`, swap `StackSegWf`/`MStateWf`/`StackWf*` frames `HasTypeRT → ClosDisc` (using the landed
  `closDisc_ctxConv` for `stackSeg_conv_input`), re-green the non-Soundness cone.
- **Session-B**: re-green `Soundness.lean`.

## State of the tree

Green everywhere except the pre-existing WIP `Soundness.lean`. New spike + `closDisc_ctxConv`
(finding 16) committed additively; no build-tree file mutated by the field surgery yet.

## Next

Re-thread the readiness lemmas (additive spike, migrated `Runtime.olean`, no commit) so a closure the
promise builds carries its `ClosDisc` field — the last additive step before Session-A.
