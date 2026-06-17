---
date: 2026-06-17
milestone: T5 (Handle/Delimit)
status: ATTEMPT — reverted to green; sharpened scope (a new T7 ripple beyond the design note)
---

# T5 Handle/Delimit attempt — outcome (B): reverted, scope sharpened

This is another dry-run of the Handle slice (cf. the 5–6 in
`2026-06-16-T5-handle-design.md`). It **confirms the design note's plan is still
correct**, records the two edits that *did* land green, and — the new contribution —
**identifies a concrete additional blocker the design note did not scope**: adding
`StackWf.delimit` breaks the *exact-`ε`* `preservation_tau`/`preservation_keep_fix`,
which the **committed T7 effect-escape soundness depends on**. So "re-green" is bigger
than `soundness_value`; it also requires reworking the T7 effect layer.

## Confirmed still-present foundations (no work needed)
- `preservation` already returns `∃ ε', MStateWf s' τ ε'` (the T5e foundation — line 962).
- `StackSegWf` + `stackSeg_append`/`stackSeg_move` exist (Runtime/Machine), and the
  `kontTy`/`handlerTy`/`execTy`/`handleTy` abbrevs (Typing). The dynamics
  (`reduceDeep`/`doPerformR`/`move`/`Delimit`/`Resume`) are transparent (Reduction).

## What landed green this attempt (then reverted with everything else)
Steps 1–2 of the note's execution order compiled cleanly (`lake build
Eyg.Types.Generation` ✔):
- `HasType.handle` (Typing.lean) at `handleTy l lift reply tail ret`.
- `inv_handle` (Generation.lean) — mirror of `inv_perform`.
- `hasType_expr_form` Handle arm: `perform` → `iterate 17 … exact Or.inl ⟨_,rfl⟩`,
  new `handle` → `iterate 18 … exact ⟨_,rfl⟩`. (Statement gains `∨ (∃ l, e.expr =
  .Handle l)`.)

These are **correct and ready to re-apply**.

## ⚠ Why this can't be a small green increment
Adding `HasType.handle` alone (without the runtime/preservation side) **breaks
`Soundness.lean`** immediately: `progress`'s catch-all `| _ =>` arm refutes the
"untypeable expr" disjuncts via `hasType_expr_form … <;> simp at hh`, but `Handle l`
now *is* a typeable form, so its `simp at hh` no longer closes (the node is real, not
absurd). So `HasType.handle` forces the whole `progress`/`preservation` Handle cascade
in the same pass — no green intermediate exists. (Same wall the note's dry-runs hit.)

## ⚠ NEW finding (the real scope-expander): `StackWf.delimit` breaks the T7 exact-`ε` layer
The design note scoped "re-green `preservation`/`progress`/`soundness_value`", all of
which tolerate the `∃ ε'` row-output form. But the **committed T7 effect-safety layer**
threads the row **exactly**, and `Delimit` invalidates that:

- `preservation_tau` / `preservation_tau_fix` / `preservation_keep_fix` conclude
  `MStateWf (.run cfg') τ ε` with the **same `ε`** (lines 989, 1952, 1966). The
  `Delimit`-value-pop `( .V v, env, Delimit l h e :: rest ) ⟶ ( .V v, env, rest )` is a
  `.tau` step whose successor is well-typed only at the **discharged** row `tail`
  (`StackWf.delimit` types `rest` at `tail`), not at `ε = ⟨l:(lift,reply)|tail⟩`. So
  these exact-`ε` lemmas become **false** for that step.
- The code's own docstring on `preservation_keep_fix` already predicts this: *"Once
  `Handle`/`Delimit` lands, the row shrinks across a `Delimit` pop and this exact-`ε`
  form no longer holds — the ω-soundness below would then thread the per-step row
  instead."*
- **Consumers that then break:** `soundnessR_effect` (folds `preservation_tau_fix`
  across silent steps, ~line 1995) and `ωTr_all_wf` (folds `preservation_keep_fix` over
  the infinite run, ~line 2133) — i.e. the **effect-escape** and **divergence
  ω-effect-safety** headline results, plus `soundness_behaviorsR_diverges` /
  `_terminates_*` downstream.

The result is still *true* (a `Delimit`-pop only discharges a handled label `l`; an
escaping `perform op` has `op ≠ l`, so `op` stays in the shrunk row — membership is
preserved downward), but the **proof** must change from "thread one fixed `ε`" to
"thread a row that only ever shrinks, with `EffContains` preserved across the shrink".
That is the note's "heavier, rejected" alternative — rejected for `soundness_value`,
but **required** to keep T7 (and hence `lake build`) green.

## Full remaining cascade (unchanged from the note, plus the T7 item)
1. Runtime: move `StackSegWf` into the `HasTypeV`/`EnvWf` mutual block (because
   `partialResume` references it); add `partialHandleNil`/`partialHandleOne`/
   `partialResume`; **drop the `EnvWf henv Γ` premise from `StackSegWf.delimit`** (note
   §"Implementation findings"); re-prove `stackSeg_append` by `induction seg
   generalizing … ; cases hseg` (mutual inductives forbid `induction hseg`); add
   `conv`/`canonical_arrow` arms.
2. Machine: `StackWf.delimit` (NO `EnvWf`) + `StackWf.conv`; six per-frame inversion
   lemmas folding `conv`; the mixed `StackSegWf seg ++ StackWf k → StackWf` append
   (`stackWf_resume`).
3. Soundness (the bulk): convert the four `cases hst` sites (`preservation_V`,
   `reduce1Run_done_value_typed`, `progress`, `preservation_perform`) to `cases kont` +
   inversion-lemma form; add the `delimit`/`handle`/`resume` cases; isolate the
   handled-`perform` dispatch behind `HandledPerformPreserves` (like
   `BuiltinAppPreserves`). `preservation_V` already needs `∃ ε'`.
4. **NEW — T7 rework:** replace exact-`ε` threading in `soundnessR_effect` and
   `ωTr_all_wf` with a row-shrinking variant (define `RowShrinks ε ε' := ε' is ε with
   some discharged-label prefix removed`, or just thread the per-state row from
   `progress`'s effect-escape witness, which already names its own `ε`). Re-green the
   `BehaviorsR` effect-safety + divergence theorems.

## Concrete next move
Do it as **one atomic branch** (no green intermediate). Order: Runtime mutual-block
restructure → Machine `delimit`/`conv`/inversion lemmas → the four Soundness theorems
(`∃ε'`, inversion form, isolated dispatch) → **then** the T7 row-shrinking rework. Budget
the T7 item explicitly; it is new scope this dry-run surfaced. Everything in steps 1–3 is
mechanical-but-voluminous (the note's repeated finding); step 4 is the one genuinely new
proof obligation (downward `EffContains` across a shrink), of moderate difficulty.

## Verification of this revert
`git status` clean; `lake build` ✔ (`Build completed successfully (1764 jobs)`). No code
changed; only this note added.
