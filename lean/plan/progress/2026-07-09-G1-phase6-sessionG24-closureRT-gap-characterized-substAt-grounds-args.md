---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G24". ANALYSIS session on the closure-body-HasTypeRT gap
  (the sole remaining soundness gap after the poly-let preservation obligation itself was mechanically
  discharged in G23). Corrected the central technical misconception in the G23 hand-off, precisely
  characterized the true remaining obstruction, and flagged the runtime-judgment strengthening that
  closing it requires as a sign-off decision. No code landed (deliberately — see below).
status: PARTIAL / ANALYSIS. No commits. Soundness.lean left exactly as G23 left it (uncommitted, red,
  no sorry, verified intact). Caveat 5 OPEN (poly-let preservation DISCHARGED; closure-body-RT open,
  now precisely characterized with a concrete two-part next step).
kind: progress
component: lean
---

# G1 Phase 6 (Session G24): closure-RT gap characterized; substAt DOES ground args

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake env lean`.
HEAD `1065877d`. `grep -rn sorry Eyg/Types/*.lean` empty throughout. `Soundness.lean` uncommitted-red
(52+/42−) exactly as G23 left it — verified intact, NOT edited this session.

## Why no code landed

The G23 hand-off framed the remaining work as "build `hasTypeRT_subst` (mirror ~100-line induction) +
wire 4 sites." On close reading of the substitution machinery this is not accurate: the gap is a
multi-piece design item whose keystone is a runtime-judgment strengthening the brief says to FLAG rather
than assume. Writing a speculative half-`hasTypeRT_subst` into `Soundness.lean` would have mangled the
one file that must never be committed red, for no committable green. So this was an analysis session.

## Corrected mechanism (good news: the design is sound in principle)

G23 believed the blocker was that `substAt`-re-typing keeps a var node's instantiation args unchanged,
so it could never ground `[.var 2 0]`. **That is wrong.** `substAt_instantiateV_scheme`
(`Scheme.lean:1535`) rewrites the produced var to carry `args.map (Ty.substAt ℓ σ)` — the args ARE
mapped by the substitution. So `hasType_substAt_le`'s var arm (`Typing.lean:715`) already produces a
derivation whose var-args are grounded (`[.var 2 0] ↦ [integer]` under `substAt 2` with ground σ),
exactly as the plan's line ~396 claims. The re-typing approach genuinely works.

## The true remaining obstruction (why 33 sessions did not close it)

1. **A boundedness precondition is unavoidable.** `HasTypeRT.var` needs the output args' levels
   `⊆ {0, s.level}`. `substAt ℓ (ground σ) t` has levels `⊆ (t.levels \ {ℓ}) ∪ {0}`. So HasTypeRT of the
   output holds **iff the input var's args' levels are `⊆ {0, ℓ, s.level}`**. `HasType.var` records
   nothing about args' levels; `HasTypeRT` bounds by `{0, s.level}` (no `ℓ`). So `hasTypeRT_subst` must
   take a NEW predicate `HasTypeRTAt ℓ h` (= `HasTypeRT` with var/builtin arm relaxed to
   `l = 0 ∨ l = ℓ ∨ l = s.level`) as its hypothesis — an additional ~21-arm inductive, not merely an
   induction.

2. **No groundness/level-bound fact is available at the closure-apply site.** In `preservation_V`
   (Apply-frame, closure case, Soundness `~873`/`~1035`; B-mirrors `~3378`/`~3538`) we have
   `hv : HasTypeV v argTy` and the closure's `hbody : HasType lvl'' ((x,.mono cArgTy)::Γc) body cRetTy cεb`
   — but nothing forces `argTy`, `cArgTy`, or the body's internal levels to be ground/bounded.
   `MStateWf.V` carries no groundness; mono `EnvWf.cons` binds a value at ANY type; `HasTypeV.closure`
   stores an existential `lvl'` and an arbitrarily-non-ground arrow. So even a proven `hasTypeRT_subst`
   cannot fire — there is no source for `HasTypeRTAt ℓ hbody` nor for a ground `σ`.

   The pathological witness: `\w:integer. let dummy = a in 5` with `a : ∀.α→α` (level 1) instantiated at
   `[.var 2 0]` (level 2) is statically well-typed, has a ground `integer → integer` closure type (so it
   IS applicable), and reaches `a` as a control at non-ground args when the closure body runs. Soundness
   for that step requires re-typing `a`'s node with ground args — which needs the level-2 occurrence
   grounded, i.e. needs the boundedness invariant threaded from the argument's abstraction level.

3. **Therefore the keystone is a runtime-judgment strengthening**, across
   `MStateWf`/`HasTypeV.closure`/`StackWf*` in BOTH engines: a body-var-args level-bound invariant
   (values/env bind at levels bounded by the closure's abstraction level). The "nonzero-ambient-level
   invariant" the Caveat-5 narrative names (threaded in G23) is the *first* such field; this
   body-boundedness field is not yet present. Adding it is exactly the class of change the closing-session
   brief says to FLAG for sign-off rather than assume additive.

## Separate first-engine regression surfaced (mechanical, not landed)

The G23 `HasTypeV.partialBuiltin → s.instantiateV` move left `builtinApp_arity2`'s `hbase : s.instantiate
sargs = …` and its `rw [hbase]` (Soundness `~1938`) plus the `fix` case (`~2050`), and the B-mirrors
`builtinApp_arity2_B` (`~3801`) / fix (`~3858`), typed at `s.instantiate` while the goal now needs
`s.instantiateV`. Fix is mechanical (retype `hbase` to `instantiateV`, update the caller simp sets), but
only committable once the engine reaches green — deferred with the closure gap.

## Concrete recommended next step (two independent parts)

1. **Committable in isolation (Typing.lean, per-file green):** add `HasTypeRTAt ℓ` and prove
   `hasTypeRT_subst : HasTypeRTAt ℓ h → (∀ i, ∀ l ∈ (σ i).levels, l = 0) → NoGenAt ℓ h → ℓ ≤ lvl →
   PolyAboveFV ℓ Γ e → HasTypeRT (hasType_substAt_le hℓ σ hσ' hng hlt hΓ)` (var arm: the mapped args are
   ground by the `{0,ℓ,s.level}` input bound + ground σ; every other arm mirrors `hasType_substAt_le`).
2. **Design decision / sign-off:** the runtime groundness-level-bound invariant that supplies
   `HasTypeRTAt ℓ hbody` + ground `σ` at the four closure-apply sites. This is the genuine open item.

## Tree state at stop

- `Soundness.lean`: uncommitted, red, unchanged from G23 (verified 52+/42−, no sorry).
- `Typing.lean`/`Runtime.lean`/`Machine.lean`/`Substitution.lean`: unchanged (G23's two green commits).
- `plan/eyg-g1-level-tagged-ty.md`: Session G24 entry appended under Phase 6.
- This progress note added.
- No commits this session. Caveat 5 OPEN (poly-let preservation DISCHARGED; closure-body-RT precisely
  characterized).
