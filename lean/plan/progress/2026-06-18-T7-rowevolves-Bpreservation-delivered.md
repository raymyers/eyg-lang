---
date: 2026-06-18
milestone: T7 — `TauKeepsRow` ELIMINATED + `BuiltinAppPreservesB` DISCHARGED (headline gated on `Fix*` only)
status: DONE — row-dependent soundness now depends only on the `Fix*` family (same as the ε-free results)
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

## `BuiltinAppPreservesB` — DISCHARGED (commit "discharge BuiltinAppPreservesB")

Done exactly per the template: `builtinApp_arity1_B`/`_arity2_B` (copy of the T6b drivers,
`StackWf`→`StackWfB`, `.tau` half only — the successor lands on the same `rest`, so the input
`StackWfB` is reused) + `builtinAppPreservesB : FixPreservesB → BuiltinAppPreservesB` (the 16-arm
`scheme_cases` dispatch; `partialFixed`→`fixed_reapply_preserves_B`; `fix`→`hfixB`). `FixPreservesB`
is isolated like `FixPreserves`. The headline `soundness`/`soundness_evalR`/`soundness_evalR_pure`
were re-pointed to take `FixPreserves`/`FixNoBadCrash`/`FixPreservesB` (discharging
`BuiltinAppPreservesB` internally via `builtinAppPreservesB`), so they are now gated on the **same
`Fix*` family as the ε-free results** — no `TauKeepsRow`, no standalone saturation hypothesis.

## Net result

`TauKeepsRow`, `BuiltinAppPreservesB`, **and `FixNoBadCrash`** are all gone from the headline.
`FixNoBadCrash` was discharged unconditionally (`fixNoBadCrash` — fix creation only `.tau`-steps,
never crashes). The headline `soundness`/`soundness_evalR`/`soundness_evalR_pure` now take **only
`FixPreserves` + `FixPreservesB`**.

## Why `FixPreserves`/`FixPreservesB` are a hard stop (machine-checked, 2026-06-18)

These are **not** mechanically dischargeable with the current type system — confirmed by a
machine-checked type mismatch (probe run this session). The fix scheme types the builder at latent
`q1` (the recursion effect; `Builtins.scheme "fix" = ((self →⟨q1⟩ self) →⟨q1⟩ self)`), and an
effectful program instantiates `q1 ≠ ∅`. But the only rule that types the successor `Partial fixed
[builder]` is `HasTypeV.partialFixed`, which **pins the builder pure**:

    partialFixed : HasTypeV builder (.fun (.fun D γ R) .empty (.fun D γ R)) → …

Converting `HasTypeV builder (.fun _ γ _)` to `HasTypeV builder (.fun _ .empty _)` is a **false
conversion** — Lean rejects it (`Type mismatch … expected … .fun Ty.empty …`), and rightly so:
no sound `HasTypeV` rule narrows a stored arrow's latent from `γ` to `∅` (that would claim an
effectful function is pure). So for an effectful builder the successor is simply **not typeable**.

Discharging the effectful case therefore requires one of (not a mechanical edit):
- **(i)** a new sound `partialFixed`-effectful typing rule — which needs the recursion's two effect
  rows (`q1` builder-construction vs. `q2` fixpoint-body, independent tyvars) related, i.e. the
  general **substitution-stable, row-variable-aware effect subsumption** of Open Question 3 (whose
  own machine-checked counterexample shows the naive `EffSub` is *not* substitution-stable — a real
  open problem, "the next foundational session"); or
- **(ii)** narrowing `Builtins.scheme "fix"` to pin `q1 = ∅` — sound but **analyzer-divergent**
  (rejects valid effectful recursion the reference `gleam_analysis` accepts), a user/design call.

This is the genuine research/decision boundary: every remaining mechanical avenue is exhausted, and
the residual obligation is provably blocked on either a new metatheory foundation or a design
decision that diverges from the reference analyzer.

## Verified this pass
- All 6 commits: `lake build` 1771 green, `lake exe spec` 104/104, axioms clean, no new `axiom`s.
- The `StackSegWf`-needs-no-B insight held: every dispatch B-lemma reused the segment machinery
  verbatim, only threading `εbot` on the base — kept the mirrors purely mechanical.
- `#print axioms soundness`/`_behaviorsR_diverges`/`_terminates_value`/`soundness_evalR` →
  `propext`/`Classical.choice`/`Quot.sound` only, with **no `TauKeepsRow`** in scope.
