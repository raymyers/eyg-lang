---
date: 2026-06-18
milestone: T7 — `TauKeepsRow` ELIMINATED (base-row preservation engine + full consumer re-thread)
status: DONE — `TauKeepsRow` removed; row-dependent soundness unconditional (modulo `BuiltinAppPreservesB`/`Fix*`)
---

# T7 RowEvolves — `TauKeepsRow` eliminated

Builds on `2026-06-18-T7-rowevolves.md` (the design). The **base-row preservation engine, the
effect-escape keystone, AND the full consumer re-thread are done** (6 commits). The false
`TauKeepsRow` hypothesis is **deleted** from the codebase; the row-dependent soundness results
(effect escape / divergence / suspension / reply-containing traces) are now **unconditional in
`TauKeepsRow`**, gated only on the *true, dischargeable* `BuiltinAppPreservesB` (+ the
pre-existing `Fix*`). All headline theorems axiom-clean; `lake build` 1771 + `lake exe spec`
104/104.

## Delivered (commits on `lean-cslib-subproject`)

1. **`StackWfB.conv` + B-inversion infra** — `StackWfB` gained a `conv` constructor (it must be
   closed under conversion like `StackWf`, since the dispatch frame-typing produces `conv`-wrapped
   stacks). `stackWfB_escape` extended with the conv case. Added `stackWfB_toStackWf` (forget
   `εbot`), the seven `stackWfB_*_inv` per-frame inversions (fold `conv`), `mStateWfB_E/_V`.
2. **Dispatch B-lemmas** — `stackSeg_toStackWfB`/`stackWfB_resume` (segment composition onto a
   base; **`StackSegWf` needs no B-version** — `εbot` lives only on the base), `preservation_E_B`,
   `fixed_reapply_preserves_B`, `resume_preserves_B`, `install_preserves_B`, `perform_walk_B`,
   `perform_preserves_B`, `reduceCall_perform_wait_B`, `preservation_perform_B`. All mechanical
   mirrors of the `StackWf` originals (segments verbatim; only the base threads `εbot`).
3. **`preservation_V_B`** — the `StackWfB` mirror of the big frame-step preservation, plus
   `preservation_tau_B`. The **only** non-mechanical case (builtin saturation) is isolated as the
   hypothesis **`BuiltinAppPreservesB`** — *true and dischargeable* (the successor always lands on
   `rest` or pushes the `fixed` frames; the per-arity drivers already construct successors on
   `rest`), and it **replaces the false `TauKeepsRow`** for the builtin tau-step. Escape boundary:
   `doPerformR_unhandled_noHandler`, `reducePerform_perform_noHandler` (`reduceCall_perform_wait_B`/
   `preservation_perform_B` now also report `noHandlerFor op kP`), and **`mStateWfB_perform_escape`**
   (an escaped well-typed perform lands `op ∈ εbot` via `stackWfB_escape`).
4. **`soundnessR_effect_B`** (keystone) + `soundness_evalR_effect_B` — effect safety over `evalR`
   **without `TauKeepsRow`**: the fuel induction threads the base row with `preservation_tau_B`
   (top row evolves across `Delimit`s, `εbot` invariant) and reads `op ∈ εbot` off
   `mStateWfB_perform_escape`. Axioms clean (`propext`/`Classical.choice`/`Quot.sound`);
   `lake build` 1771 + `lake exe spec` 104/104; no `sorry`, no new `axiom`s.

## Consumer re-thread — DONE (commit "remove TauKeepsRow")

All 15 `hkeep` consumers were swapped to `MStateWfB`+`hsatB` and `TauKeepsRow`/`preservation_keep_fix`/
the old `soundnessR_effect` deleted. Key new pieces:
- **`preservation_keep_B`** (tau→`preservation_tau_B`, perform→`preservation_perform_B`, reply→the
  world `ReplyContract εbot` reply, re-typed at the stack's expected reply type).
- The **reply subtlety** was resolved as predicted: `stackWfB_escape` strengthened to return the
  reply `TyEquiv` link (`∃ a' b', EffContains εbot op a' b' ∧ TyEquiv a a' ∧ TyEquiv b b'`), and
  **`noHandlerFor op k` baked into `MStateWfB`'s `wait` clause** (waits only arise from escaped
  performs — `preservation_perform_B`/`reduceCall_perform_wait_B` now establish it), so the reply
  case reflects `op ∈ εbot` and re-types the reply at `replyTy ≈ b ≈ b'`.
- **`mStateWfB_toMStateWf`** (forget `εbot`) lets the `MStateWf`-stated terminal lemmas
  (`reduce1Run_done_value_typed`, `progress_fix`) consume the base-row-tracked terminal state.

## Remaining: discharge `BuiltinAppPreservesB`

The single isolated hypothesis introduced this milestone (besides the pre-existing `Fix*`). The
`.tau` builtin-saturation base-row obligation. The non-`B` `BuiltinAppPreserves` is *proven*
(`builtinAppPreserves : FixPreserves → BuiltinAppPreserves`); the B-form re-runs the same T6b
per-arity machinery threading `εbot`, **and is a ~160-line mechanical mirror** with a clear
template:
- **`builtinApp_arity1_B`/`_arity2_B`** — copy `builtinApp_arity1/2` with `StackWf`→`StackWfB`,
  result `MStateWf`→`MStateWfB`, **drop the `.done value` clause** (only the `.tau` half is in
  `BuiltinAppPreservesB`). The successor is always `(.V value/partial, env, rest)` — same `rest` —
  so the input `hstB : StackWfB rest …` is reused verbatim; the value typing (`hrunTy`/
  `partialBuiltin`) is identical to the non-`B` driver.
- **`builtinAppPreservesB : FixPreservesB → BuiltinAppPreservesB`** — copy `builtinAppPreserves`'s
  `scheme_cases` dispatch (16 arms), calling `_arity{1,2}_B`; `partialFixed`→`fixed_reapply_preserves_B`;
  `fix`→`hfixB`. Define `FixPreservesB` like `FixPreserves` (the `fix`-creation `.tau`, `MStateWfB`).
- **Wire it like the non-`B` chain:** add `_B_fix` wrappers that take `FixPreserves`/`FixNoBadCrash`/
  `FixPreservesB` and discharge `BuiltinAppPreservesB` internally via `builtinAppPreservesB`, so the
  headline `soundness` ends up gated only on `Fix*` (matching the ε-free results). `FixPreservesB`
  is satisfiable for the pure-builder fragment exactly like `FixPreserves` (Open Question 3 fork
  for effectful builders).

## Verified this pass
- All 6 commits: `lake build` 1771 green, `lake exe spec` 104/104, axioms clean, no new `axiom`s.
- The `StackSegWf`-needs-no-B insight held: every dispatch B-lemma reused the segment machinery
  verbatim, only threading `εbot` on the base — kept the mirrors purely mechanical.
- `#print axioms soundness`/`_behaviorsR_diverges`/`_terminates_value`/`soundness_evalR` →
  `propext`/`Classical.choice`/`Quot.sound` only, with **no `TauKeepsRow`** in scope.
