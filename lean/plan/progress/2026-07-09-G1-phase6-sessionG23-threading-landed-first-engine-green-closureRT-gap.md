---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G23". LANDED the finalized four-field (plus one discovered
  fifth) runtime-judgment threading (two green per-file commits) and migrated the ENTIRE FIRST Soundness
  engine to green except the two closure-application cases — including a MECHANICAL discharge of the
  Caveat-5 poly-let preservation obligation, exactly as the G22 design predicted. Surfaced a new,
  design-unaccounted gap (closure-body HasTypeRT re-establishment) that blocks both engines' closure-apply.
status: PARTIAL. Two committed green increments (threading). Soundness.lean uncommitted+red but greatly
  advanced (first engine complete bar closure-RT). Caveat 5 OPEN (poly-let preservation DISCHARGED;
  closure-body-RT is now the sole remaining gap).
kind: progress
component: lean
---

# G1 Phase 6 (Session G23): threading landed; first engine green bar closure-body-RT

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake build`.
HEAD at start `d86e253c`. `grep -rn sorry Eyg/Types/*.lean` empty throughout.

## Committed this session (two green per-file increments)

1. **Four-field threading** (`Runtime.lean`/`Machine.lean`/`Substitution.lean`):
   - `HasTypeV.closure`: `1 ≤ lvl'`.
   - `EnvWf.cons`: `hpoly (s.arity ≠ 0 → s.level ≠ 0 ∧ s.level ∈ s.body.levels)`; `ctxPolyBd_of_envWf`
     is the derived projection.
   - `StackSegWf.assign/.arg`, `StackWf.assign/.arg`: `1 ≤ lvl` (inversions expose it).
   - `StackWfV/StackWfE` Assign, `MStateWf.E`, `mStateWf_initial`: `1 ≤ lvl`.
   - `closure_typed_of_lambda`/`genAtV_closure_ready_value(_node)`: derive `1 ≤ lvl'` from `1 ≤ lvl`.
2. **Discovered fifth carried field + instantiateV convergence:** the `hpoly` obligation must ALSO ride
   in the `StackWfV/StackWfE` Assign clauses (the Assign-pop rebuilds `EnvWf.cons`, needs `hpoly`, and it
   is NOT derivable from readiness); helpers `schemePolyBd_genAtV`/`schemePolyBd_mono` (`Typing.lean`).
   `HasTypeV.partialBuiltin` moved to `s.instantiateV args` (matches `inv_builtin`; base not inspected by
   `BuiltinAppPreserves`).

Green per-file: Typing/Runtime/Substitution/Machine (+ transitive).

## Soundness.lean (uncommitted, red — first engine now green bar 2 cases)

Migrated to green: `weakenEffAux` (mis-binder'd `app`/`conv`/`let_poly` induction arms fixed),
`preservation_E` (now consumes `inv_var_rt`/`inv_app_rt`/`inv_let_rt`, `builtin_instantiate_arrow` at
`instantiateV`; **both `let` cases discharge — the Caveat-5 poly-let preservation is MECHANICALLY DONE**
via `genAtV_closure_ready_value_node (Nat.one_le_iff_ne_zero.mp hlvl) hng (polyAboveFV_of_ctxPolyBd
(ctxPolyBd_of_envWf henv) hcw) hcw henv`), `progress` (stale `mStateWf_E` destructure fixed — collapsed a
76-error cascade), `perform_walk` Assign/Arg, `preservation_V` Assign/Arg. Only the 2 closure-apply cases
(`preservation_V` ~874, ~1036) remain in the first engine.

## The blocking gap (NOT in the "finalized design")

`MStateWf.E` requires `HasTypeRT` of the control; a `reduceCall` closure step makes the closure **body**
`hbody` the new control, but `HasTypeV.closure` carries no `HasTypeRT` for it — and cannot, since closures
are born at lambda-eval where only `HasTypeRT.lam` (no body premise, by deliberate design) is available.
The `HasTypeRT` note (`Typing.lean` ~950) stipulates the body is "re-typed via `substAt` with ground args
at application, re-establishing `HasTypeRT`" — but that infrastructure does **not** exist: no
`HasTypeRT`-tracking companion of `hasType_subst`/`hasType_substAt_le`, and the env machine's closure-apply
uses `hbody` directly (env-extension ≠ substitution), so wiring a re-typing is itself non-trivial. Building
`hasTypeRT_subst` + rewriting the 4 closure-apply sites (2 engines × 2 cases) is the true remaining work —
NOT mechanical; arguably a runtime-judgment strengthening warranting sign-off.

## Second engine

`MStateWfB`/`StackWfB`/`StackWfEB`/`preservation_VB`/`_EB`/`progressB` (Soundness ~2400-3993) is a straight
mechanical repeat of the first-engine threading, blocked by the same closure-body-RT gap. Untouched.

## Validation gates

No `sorry` in `Eyg/Types/*.lean` (checked, every step). Green cone builds (`lake build Eyg.Types.Machine`
+ transitive). `Soundness.lean` uncommitted red (first engine complete bar closure-RT). No axioms landed.

## Tree state at stop

- `Typing.lean`/`Runtime.lean`/`Machine.lean`/`Substitution.lean`: threading + helpers (2 green commits).
- `Soundness.lean`: advanced first-engine migration (uncommitted, red).
- `plan/eyg-g1-level-tagged-ty.md`: Session G23 entry appended.
- This progress note added.
- Caveat 5 OPEN (poly-let preservation DISCHARGED; closure-body-RT is the sole remaining gap).
