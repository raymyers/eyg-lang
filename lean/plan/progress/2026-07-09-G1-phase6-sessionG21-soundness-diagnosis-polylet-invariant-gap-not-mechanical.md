---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G21". DIAGNOSIS session. Traced the full dependency
  chain of the `Soundness.lean` `let_poly` preservation case and reached a definitive finding that
  overturns the prior "purely mechanical" framing: the poly-let preservation case has a genuine
  invariant gap (`PolyAboveFV lvl Γ` + `lvl ≠ 0` are required by the closure-readiness wrapper but
  are NOT carried by the runtime state and NOT derivable from `CtxWfV`). Closing it needs a carried
  runtime invariant (architectural, approval-gated), not mechanical threading. Also found the file
  contains TWO complete engines (A `MStateWf` + a full B `MStateWfB` mirror still on the old API).
  No edits to `Soundness.lean` (left EXACTLY as found). Caveat 5 OPEN.
status: DIAGNOSIS. Soundness.lean untouched (pre-existing uncommitted partial migration, still red).
  Plan Phase 6 updated with the Session G21 finding. No commit (nothing committable: red Soundness
  cannot be committed; made no green-file changes).
kind: progress
component: lean
---

# G1 Phase 6 (Session G21): Soundness diagnosis — the poly-let case is NOT purely mechanical

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake build`.
HEAD `7e18920b` confirmed; `grep -rn sorry Eyg/Types/*.lean` empty. Working tree: only the pre-existing
uncommitted `Soundness.lean` partial-migration diff (untouched this session) + `.claude/`.

## What was done

Traced the entire call chain the `let_poly` preservation case depends on, across
`Typing.lean` / `Generation.lean` / `Substitution.lean` / `Runtime.lean` / `Machine.lean` /
`Soundness.lean`, to determine whether the remaining `Soundness.lean` re-green is the "pure execution"
the prior sessions expected. It is not — there is a small residual conceptual gap. Made **no edits** to
`Soundness.lean` (a partial migration is uncommittable and would leave a harder-to-resume state than the
clean untouched file).

## Finding 1 — the mechanical part is real and well-supported

`Soundness.lean` predates BOTH the `lvl` and the `HasTypeRT` additions to `MStateWf`:
- `MStateWf (.run (.E ...))` is now `∃ Γ τin lvl, EnvWf env Γ ∧ ∃ hty : HasType lvl Γ e τin ε,
  HasTypeRT hty ∧ StackWfE ...`. The unfold lemma `mStateWf_E` (`Soundness:32`) still returns the old
  RT-free, lvl-free tuple → the first error (`:34`). Consumers destructure `⟨Γ, τin, lvl, henv, hty,
  hst⟩` (6) where the def yields 7 (with `hrt`).
- The `.V`-producing preservation cases (int/str/bin/lambda/var/builtin/tail/...) need only the extra
  `hrt` ignored — `HasTypeV` + `StackWfV` carry no RT.
- The two `.E`-producing cases (app: `f` becomes control; let: `defn` becomes control) need RT
  re-established for the new control, supplied by the ALREADY-EXISTING RT inversions
  `inv_app_rt` / `inv_let_rt` / `hasTypeRT_lambda` (Typing `:1013/:1034/:998`) and the `HasTypeRT harg`
  field now in `StackWf.arg` / `StackWf.assign`.
This half is genuinely mechanical.

## Finding 2 — the poly-let case has a genuine invariant gap (the blocker)

`genAtV_closure_ready_value_node` (Substitution `:167`), which produces the `StackWfE`-Assign readiness
`∀ args, (bounded) → HasTypeV (Closure lx lbody env) ((genAtV lvl defnTy).instantiateV args)` for the
poly-let successor, requires:
- `hℓ : lvl ≠ 0`, and
- `hΓpa : PolyAboveFV lvl Γ ⟨.Lambda lx lbody, la⟩`.

`inv_let` / `inv_let_rt` now hand `hcw : CtxWfV lvl Γ` and `NoGenAt lvl hdefn` (free, exactly as the G20
reshape intended). But **`PolyAboveFV` and `lvl ≠ 0` are not available**:
- `MStateWf` / `EnvWf` / `HasTypeV.closure` carry **no** context-level invariant. (`MStateWf.E` =
  `∃ Γ τin lvl, EnvWf ∧ ∃ hty, HasTypeRT ∧ StackWfE`; `HasTypeV.closure` stores `lvl'` existentially
  with no lower bound.)
- `PolyAboveFV lvl Γ e` is **not derivable from `CtxWfV lvl Γ`.** `CtxWfV lvl Γ` = every binding's
  body levels are `< lvl`. For a poly binding `s = genAtV k d` (arity ≠ 0 ⟹ `k ∈ d.levels`) this gives
  `k < lvl` (so `k ≠ lvl` ✓, the second `PolyAboveFV` disjunct's `s.level ≠ ℓ` half) but says
  **nothing about `k ≠ 0`**. A `genAtV 0 d` binding with `0 ∈ d.levels` and all `d.levels < lvl`
  satisfies `CtxWfV lvl Γ` yet violates `PolyAboveFV` (whose disjunct needs `s.level ≠ 0`). Mono
  bindings are fine (`arity = 0`, first disjunct).

So `PolyAboveFV` holds iff **no poly binding sits at level 0**, i.e. every generalization in the
reachable context happened at a nonzero level. That is an invariant on the runtime context that must be
**carried** (threaded from a nonzero initial ambient level into `MStateWf`/`EnvWf`/`HasTypeV.closure`),
not merely asserted at the entry. Establishing it is an **architectural strengthening of the runtime
typing judgments** + re-proof of the Runtime/Machine lemmas — small, but genuinely conceptual, and
gated behind the standing "no large architectural change without approval" rule. This is what task
step 5 ("set the ambient level to a nonzero constant if the type signature needs it") was gesturing at,
but the level must be *carried as an invariant*, not just fixed at `mStateWf_initial`.

Cheaper alternative worth trying first: a pure lemma
`polyAboveFV_of_ctxWfV_nonzeroPoly : lvl ≠ 0 → (∀ poly binding in Γ, its level ≠ 0) → CtxWfV lvl Γ →
PolyAboveFV lvl Γ e` — still needs the "poly levels ≠ 0" hypothesis carried from somewhere, so it only
relocates the invariant, but it isolates the design surface to one added premise.

## Finding 3 — the file is TWO engines, not one

`Soundness.lean` (4278 lines) contains a full A-engine (`MStateWf`, `~:30-2840`, partially level/RT
migrated) **and** a complete B-engine mirror (`MStateWfB`, `~:2850-4278`) still **entirely on the
pre-migration API**: `Scheme.genAt`/`.instantiate` (not `genAtV`/`.instantiateV`), old 3-arg
`HasTypeV.closure henv hbody heq`, old `inv_let` tuple `⟨defnTy, hdefn, hbody⟩` /
`⟨lx,lbody,la,defnTy,n,hdl,hdefn,hcw,hnl,hbody⟩`, `genAt_closure_ready`/`ctxWf_fixed`. So the 103 errors
span two mirrored migrations. The A-engine is the one to finish first (task guidance).

## Recommended next session

1. Get approval to strengthen the runtime judgments with the nonzero-poly-level context invariant
   (carried from a nonzero initial ambient level), OR add the isolating premise lemma above.
2. Then grind the A-engine `MStateWf` mechanically: fix `mStateWf_E` to return the `HasTypeRT` field,
   thread `hrt` through every `preservation_E`/`preservation_V`/`progress` case (`.V` cases ignore it;
   app/let use `inv_app_rt`/`inv_let_rt`/`hasTypeRT_lambda`), wire the poly-let readiness via
   `genAtV_closure_ready_value_node` (now fed the carried `PolyAboveFV` + `lvl ≠ 0`).
3. Then the B-engine `MStateWfB` mirror (same recipe on `genAtV`/`instantiateV`).

## Validation gates

- No `sorry` anywhere in `Eyg/Types/*.lean` (checked). Axioms unchanged (no code change). HEAD
  `7e18920b`. `Soundness.lean` still red (as at HEAD, which also does not build it) — no commit made,
  nothing committable (red Soundness cannot be committed; no green files were touched).

## Tree state at stop

- `Soundness.lean`: EXACTLY as found (pre-existing uncommitted partial migration, untouched, red).
- `plan/eyg-g1-level-tagged-ty.md`: Phase 6 entry appended with the Session G21 finding.
- This progress note added. No `sorry`, no axiom change, no rule change, no statement weakened.
- Caveat 5 OPEN.
