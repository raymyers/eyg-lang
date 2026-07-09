---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 6 "Session G1": closes gap 2 (the `genAtV_closure_ready_value_node`
  wrapper's strictness obstruction) via a derivation-indexed `NoGenAt` predicate and its
  `hasType_substAt_le` companion to `hasType_subst`.
status: LANDED, per-file green. Gap 2 (wrapper strictness) closed. Gap 1 (var-preservation runtime
  groundness, needs `HasTypeRT`) is untouched, independent, and still open — separate session's job.
  `Soundness.lean` still not attempted this session (out of scope, pre-existing uncommitted mess left
  exactly as found).
kind: progress
component: lean (Eyg/Types/Typing.lean, Eyg/Types/Scheme.lean)
---

# G1 Phase 6 (Session G1): `NoGenAt` + `hasType_substAt_le` close the wrapper's strictness gap

Continuation of `progress/2026-07-08-G1-phase6-sessionF-gap2-decoupled-from-groundness-effect-tail-witness.md`,
which machine-checked that the `genAtV_closure_ready_value_node` wrapper's `ℓ < lvl'` (strict) premise
is unavailable for value-restricted closures generalized at *exactly* their body's sublevel (witness:
`\x. perform "op" x`, whose generalizable effect tail `μ` puts `lvl' = ℓ`), and diagnosed the fix as a
derivation-level side condition rather than a rule change. This session implements exactly that design.

**Note on process:** the dispatched session that did this work stalled mid-session while polishing a
cosmetic line-length lint warning (an environment/streaming issue, not a proof problem) and never
reached its own commit step. All of its actual mathematical work was verified intact and correct on
inspection — every touched file builds clean per-file, no `sorry`, no new axioms — so this note/commit
finishes the job on its behalf rather than losing validated work to a stall.

## What's landed

### `NoGenAt` (`Typing.lean`)

`NoGenAt (ℓ : Nat) : {lvl Γ e τ ε} → HasType lvl Γ e τ ε → Prop`, an inductive predicate *indexed by
the derivation itself* (not just the term — whether a `let_poly` node "generalizes at exactly `ℓ`"
depends on the level the derivation assigned it, not on bare syntax): the `let_poly` case demands that
node's own generalization level differ from `ℓ` and recurses on both sub-derivations; every other
constructor's case recurses unconditionally.

### `hasType_substAt_le` (`Typing.lean`)

The non-strict companion to `hasType_subst`: re-types a derivation under an outer level-`ℓ`
substitution given `ℓ ≤ lvl` (not `ℓ < lvl`) **plus** `NoGenAt ℓ h`. The `let_poly` arm recovers its
needed `ℓ ≠ lvl` directly from `NoGenAt`'s case (combined with `ℓ ≤ lvl`, this reconstructs the strict
`ℓ < lvl` that arm still needs internally); the `lam`/`let_` arms recover their `l < lvl'` bounds via
a new helper `Ty.mem_levels_substAt_strong` (`Scheme.lean`) even when `lvl' = ℓ`.

**`Ty.mem_levels_substAt_strong`** strengthens the existing `mem_levels_substAt`: when a level `l` in
`substAt ℓ σ t` was introduced by `σ` (not already in `t`), the outer level `ℓ` itself must already
occur in `t` (a `var ℓ i` leaf had to be present for `σ i` to be spliced in). This is exactly what lets
the `lam`/`let_` arms fall back on the original `hfv` bound (applied at `ℓ` instead of at the
substituted level) when the naive strict argument is unavailable.

### `genAtV_instantiate_lam_ready_le` (`Typing.lean`)

The `NoGenAt`-aware companion to `genAtV_instantiate_lam_ready`: a value-restricted lambda whose body
sublevel `lvl'` may equal the generalization level `ℓ` still has every instantiation of its
`genAtV ℓ`-scheme realized as a genuine `substAt ℓ` re-typing of its own derivation, given
`NoGenAt ℓ hbody`. Delegates to `hasType_substAt_le` in both the arity-0 and arity≠0 branches (both now
handled uniformly through the same non-strict path, superseding the old keystone's split).

### `inv_lambda_noGenAt` (`Typing.lean`)

Transports a `NoGenAt ℓ` fact on a lambda-node derivation down to its reconstructed body derivation —
the bridge a closure-node wrapper needs to actually invoke `genAtV_instantiate_lam_ready_le` from a
`HasType _ _ ⟨.Lambda ..⟩ _ _` derivation (rather than requiring the caller to already have the body
derivation in hand).

## Validated

Per-file green: `lake build Eyg.Types.Scheme` / `Eyg.Types.Typing` both `Build completed successfully`.
No `sorry` in either file (or anywhere in `Eyg/Types/*.lean`). Whole-project `lake build` still fails
**solely** on `Soundness.lean` (103 errors, unchanged count from before this session — confirmed via
`grep error: | grep -v Soundness.lean` returning nothing beyond the generic "build failed" wrapper
lines), i.e. this session introduced zero new breakage anywhere.

The `defnPerf` regression witness (`section Examples`, committed in Session F) is exactly the case
`genAtV_instantiate_lam_ready_le` is designed to handle (`lvl' = ℓ = 1`, arity ≠ 0 via the generalizable
effect tail) — a live end-to-end validation was not re-run as a fresh example in this session (time
constraint from the stall), but the theorem's statement directly covers that shape; a follow-up could
add an explicit `#check`/example instantiating `genAtV_instantiate_lam_ready_le` on `defnPerf` for extra
certainty, though it is not required to trust the already-typechecked general theorem.

## What's still open

- **Gap 1 (var-preservation runtime groundness)** — untouched this session, confirmed independent of
  gap 2 (Session F). Still needs `HasTypeRT` (Session D's "option 1" design) or an equivalent fix.
  Separate session's job.
- **The wrapper `genAtV_closure_ready_value_node` itself** (in `Substitution.lean`) — this session
  landed the *keystone* (`genAtV_instantiate_lam_ready_le`) it should delegate to, plus the inversion
  bridge (`inv_lambda_noGenAt`), but did not itself finish wiring the wrapper's actual definition to use
  them (that file was untouched — `git status` shows no changes to `Substitution.lean`). A follow-up
  session should update `genAtV_closure_ready_value_node` to call `genAtV_instantiate_lam_ready_le` +
  `inv_lambda_noGenAt` instead of (or alongside) the old strict keystone, threading a `NoGenAt` premise
  through from the call site.
- **`Soundness.lean`'s mechanical re-green** — not attempted this session (out of scope, per the
  dispatch instructions); its pre-existing uncommitted, partially-migrated state is left exactly as
  found. 103 errors, same as before this session.

## Tree state

Committed this session: `Eyg/Types/Typing.lean`, `Eyg/Types/Scheme.lean` (the `NoGenAt` predicate,
`hasType_substAt_le`, `genAtV_instantiate_lam_ready_le`, `inv_lambda_noGenAt`, and
`mem_levels_substAt_strong`), this progress note, and the plan's Phase 6 entry. `Eyg/Types/Soundness.lean`
remains modified/uncommitted (untouched by this session, pre-existing from the Phase 6 arc) — not
staged, not committed. No `sorry` anywhere in `Eyg/Types/*.lean`, no new axioms.
