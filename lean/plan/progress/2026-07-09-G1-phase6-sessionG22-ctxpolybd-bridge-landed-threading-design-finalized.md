---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G22". LANDED the carried-invariant keystone (CtxPolyBd +
  PolyAboveFV bridge, green in Typing.lean, committed 8110c393) that closes the *conceptual* poly-let
  gap diagnosed in G21. Then finalized the full runtime-judgment threading design and CONFIRMED the
  fix is architectural (a nonzero-ambient-level bound must be carried through HasTypeV.closure and the
  assign/arg stack frames, not just a context predicate), revising this task's "small additive" premise.
status: PARTIAL. One committed green increment (bridge lemma infra). Soundness.lean untouched (still the
  pre-existing uncommitted partial migration, 103 errors, both engines). Caveat 5 OPEN.
kind: progress
component: lean
---

# G1 Phase 6 (Session G22): CtxPolyBd bridge landed; full threading design finalized (architectural)

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake build`.
HEAD at start `095f51ad` confirmed; `grep -rn sorry Eyg/Types/*.lean` empty. Working tree at start:
pre-existing uncommitted `Soundness.lean` partial-migration diff + `.claude/`.

## Committed this session (8110c393, green in Typing.lean)

The carried-invariant infrastructure the poly-let preservation case needs, correct **independent of how
the runtime threads it**, so landed immediately:

- `CtxPolyBd Γ := ∀ b ∈ Γ, b.2.arity ≠ 0 → b.2.level ≠ 0 ∧ b.2.level ∈ b.2.body.levels` — every
  polymorphic binding sits at a nonzero level occurring among its body levels.
- `polyAboveFV_of_ctxPolyBd : CtxPolyBd Γ → CtxWfV ℓ Γ → PolyAboveFV ℓ Γ e` — the **bridge**. A
  looked-up poly binding's level is `≠ 0` (CtxPolyBd) and `< ℓ` hence `≠ ℓ` (CtxWfV at that level).
  This is exactly the previously-flagged-but-unbuilt `polyAboveFV_of_ctxWfV_nonzeroPoly`, now built.
- `ctxPolyBd_cons_genAtV` (needs `lvl ≠ 0`) / `ctxPolyBd_cons_mono` (vacuous) — preservation.

Green cone re-verified after the commit (Generation/Generalization/Substitution/Runtime/Machine all
build; Soundness unchanged at 103 errors).

## Finding: the fix is architectural, not "small additive" (revises the task premise)

`genAtV_closure_ready_value_node` (Substitution `:167`) takes `hℓ : lvl ≠ 0` as a **hard** precondition
— it flows into `hasType_subst`/`hasType_substAt_le`, both of which require `ℓ ≠ 0` structurally. That
`lvl` is the closure body's / stack frame's ambient level, not the machine state's, so `lvl ≠ 0` must
be **carried** through `HasTypeV.closure` and the `assign`/`arg` frames.

The `lvl = 0` branch is **not** separately dischargeable: `EnvWf`'s readiness clause permits args with
level-0 variables (`∀ l ∈ t.levels, l = 0 ∨ l = s.level`), so `0 ∈ defnTy.levels` is possible at
`lvl = 0`, making `genAtV 0 defnTy` have `arity ≠ 0` — precisely a `CtxPolyBd`-violating
poly-binding-at-level-0. Ruling it out needs "no reachable level-0 type variable," itself a carried
invariant bottoming out at a nonzero top-level ambient. So G21's "architectural strengthening of the
runtime typing judgments" diagnosis stands; this session makes it precise.

## Finalized threading design (next session executes deterministically)

Four field additions + discharge at construction sites:
- `EnvWf.cons`: `(hpoly : s.arity ≠ 0 → s.level ≠ 0 ∧ s.level ∈ s.body.levels)`. Then
  `EnvWf env Γ → CtxPolyBd Γ` is a derived projection. Mono cons trivial; `genAtV lvl` cons via
  `ctxPolyBd_cons_genAtV` (needs the frame's `1 ≤ lvl`).
- `HasTypeV.closure`: `(hlvl' : 1 ≤ lvl')`. Applied closures then run their body at nonzero ambient;
  created closures inherit it from `1 ≤ lvl ≤ lvl'`.
- `StackWf.assign` / `StackWf.arg` (+ `StackSegWf` mirrors): `(hlvl : 1 ≤ lvl)`.
- `MStateWf` E/V/wait: carry `1 ≤ lvl` in the E-case; preservation preserves it (same `lvl`, `lvl+1`
  from the `let_poly` body, or a closure's `lvl' ≥ 1`). `mStateWf_initial` gains `1 ≤ lvl`;
  `soundness`/`soundness_evalR` fix the top ambient to `1` and re-type the closed program at level `1`.

Poly-let case then closes: `inv_let` → `CtxWfV lvl Γ`; `EnvWf env Γ` → `CtxPolyBd Γ`; bridge →
`PolyAboveFV lvl Γ`; `1 ≤ lvl` → `lvl ≠ 0`; feed `genAtV_closure_ready_value_node`.

Green-file blast radius: `EnvWf`/`HasTypeV.closure`/`StackWf.assign`/`arg` defs in `Runtime.lean` (few
sanity examples bump `lvl' 0 → 1`), `stackWf_assign_inv`/`stackWf_arg_inv` inversions + `MStateWf`/
`mStateWf_initial` in `Machine.lean`. All heavy re-proof is in `Soundness.lean` (already red, two
engines, ~103 errors).

## Why the four-field threading was NOT begun this session

It ramifies across two inductive-definition files (`Runtime`/`Machine`) and both Soundness engines and
**cannot be validated end-to-end** until the entire ~103-error two-engine grind lands (one file — no
partial-Soundness build/commit possible). A committed half-shaped strengthening would risk churn if the
grind later demands a different field shape. So only the validated, shape-independent bridge lemma was
committed; the design above is recorded so the next session threads + grinds in one committable push.

## Validation gates

- No `sorry` in `Eyg/Types/*.lean` (checked). Green cone builds. `Soundness.lean` unchanged (103
  errors, as found). Axioms unchanged (no runtime-judgment change landed). Committed increment
  `8110c393` is green per-file (`lake build Eyg.Types.Typing`, and Machine transitively).

## Tree state at stop

- `Typing.lean`: +CtxPolyBd/bridge/preservation lemmas (committed `8110c393`).
- `plan/eyg-g1-level-tagged-ty.md`: Phase 6 entry appended with the Session G22 finding + design.
- This progress note added.
- `Soundness.lean`: EXACTLY as found (uncommitted partial migration, untouched, red).
- Caveat 5 OPEN.
