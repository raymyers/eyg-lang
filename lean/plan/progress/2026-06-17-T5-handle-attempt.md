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

---

# ⚙ 2nd execution pass (2026-06-17, later): ALL infrastructure (steps 1–3) built green

This pass executed the full cascade and got **steps 1, 2, and 3 to compile green**
(per-module: `Generation`, `Runtime`, `Machine` all ✔), then reverted because the
**step-3-into-Soundness** boundary (the four-theorem refactor + step-4 T7 rework) is the
atomic bulk and could not be finished green in one pass. **The infrastructure is saved as
a re-appliable patch: `plan/progress/2026-06-17-T5-handle-infra.patch`** (389 lines; `git
apply` it from the `lean/` dir to restore steps 1–3 instantly).

## ✅ What now COMPILES (verified per-module, in the patch)
- **Step 1** — `HasType.handle` (Typing); `inv_handle` + `hasType_expr_form` Handle arm
  (`perform` → `Or.inl ⟨_,rfl⟩`, `handle` → `iterate 18`; statement gains `∨ ∃ l, .Handle l`).
- **Step 2** — `Runtime` mutual-block restructure: `StackSegWf` **moved into** the
  `HasTypeV`/`EnvWf` mutual block (its `delimit` frame **drops `EnvWf`**); `stackSeg_append`
  re-proved by `induction seg generalizing σin εin; cases hseg`; new `HasTypeV` constructors
  `partialHandleNil`/`partialHandleOne`/`partialResume` (the last stores `StackSegWf
  acc.reverse reply εtop ret tail` + `TyEquiv (kontTy reply tail ret) τ`); their `conv` +
  `canonical_arrow` arms.
- **Step 3** — `Machine`: `StackWf.delimit` (no `EnvWf`) + **`StackWf.conv`** constructor;
  the old uniform `stackWf_append`/`stackWf_move`/`stackSeg_move` **deleted**, replaced by
  `stackSeg_toStackWf` (`StackSegWf seg ++ StackWf k → StackWf`, by `induction seg; cases
  hseg` — non-delimit frames use `Ty.effWeaken_refl _`) and `stackWf_resume`.
  **THE KEY RESULT: the six conv-folding inversion lemmas COMPILE** —
  `stackWf_{trace,assign,arg,applyf,callwith,delimit}_inv`, each proved by `generalize hs :
  (frame::rest) = s at h; induction h with | <frame> => cases hs; … | conv _ hσ hε ih => …
  (hσ.symm.trans …) | _ => simp at hs`. This was "the one real design addition left" (note
  above) and is now **proven to work** — the conv case folds via `TyEquiv.trans`, exactly as
  designed. The inversion lemmas expose `TyEquiv σ <input> ∧ TyEquiv ε ε0 ∧ <frame data at
  ε0>` (the `arg`/`callwith`/`delimit` inputs are the structured arrow/effectExtend; `trace`
  folds conv straight into its result).

## ⛔ Precise stall point: the Soundness cascade (45 errors) + T7 rework
`lake build Eyg.Types.Soundness` after the patch = **45 errors**, all expected and mapped:
- `weakenEffAux` (line ~52): `induction h` needs `| handle => exact fun _ _ => HasType.handle`.
- `stackWf_doPerformR_unhandled` (~131): now **FALSE** (typed stacks may carry a `Delimit`)
  — delete; replace with the **dispatch**: a lemma that `doPerformR … = .error unhandled →
  ∃ a b, EffContains ε op a b` (effect safety — induct on `StackWf`, walking past a
  `Delimit l' ` with `l' ≠ op` keeps `op` in the row via `EffContains.tail`), and the
  handled `.ok` branch isolated behind `HandledPerformPreserves` (a `def … : Prop` threaded
  like `BuiltinAppPreserves`). **This is §5 of the design note — the one genuinely hard proof.**
- The four `cases hst` theorems — `preservation_V` (~527), `reduce1Run_done_value_typed`
  (~?), `progress` (~930/1029), `preservation_perform` (~?) — convert `cases hst` → `cases
  kont` + the inversion lemmas, threading the exposed `TyEquiv` equivs (`hv.conv hσ.symm`,
  `HasType.conv`, `StackWf.conv` on `rest`). Each gains: `delimit`-pop (`.tau`, types at row
  `tail`, needs `∃ε'`), and the new `HasTypeV` cases at the `cases hf/hv/hw` sites
  (`partialHandleNil` accumulate → `partialHandleOne`; `partialHandleOne` → `reduceDeep`
  pushes `Apply exec :: Delimit :: rest` via `StackWf.applyf` + `StackWf.delimit`;
  `partialResume` → `stackWf_resume` + `StackWf.conv` to align the base stack's `(ret,tail)`
  with the frame's `(retTy,ε)`; handled-`partialPerformNil` → `HandledPerformPreserves`).
  The `cases expr` in `preservation_E`/`progress` also need an explicit `Handle l` eval arm
  (produces `partialHandleNil`) before the `| _ =>` catch-all, and the `rcases
  hasType_expr_form` patterns gain one `| ⟨_, h⟩`.
- **Step 4 (T7)**: `preservation_tau`/`preservation_keep_fix` become row-output; rework
  `soundnessR_effect` + `ωTr_all_wf` to thread the per-state row (read off `progress`'s
  effect-escape witness) instead of a fixed `ε`. Re-green `soundness_behaviorsR_*`.

## Assessment
The novel/risky metatheory (the `conv` inversion-closure) is **done and compiles** — that
was the genuine unknown across the prior 6 dry-runs. What remains is large but
**mechanical-but-voluminous** (the four-theorem refactor) plus the **two isolated/bounded
proofs** (`HandledPerformPreserves` as a hypothesis; the unhandled-effect-safety induction;
the T7 row-threading). Next pass: `git apply` the patch, then grind the Soundness cascade
top-to-bottom — it is now a finite, fully-mapped edit list with no remaining design unknowns.

## 3rd-pass refinement (2026-06-17): the exact Soundness-grind recipe + new helper lemmas

A third fork re-applied the infra patch (confirmed: `git apply` clean, `lake build
Eyg.Types.Machine` green — the six conv-folding inversion lemmas + `StackWf.delimit/conv`
all compile), then mapped the 45 Soundness errors into a concrete edit list. Reverted to
green (the four-theorem refactor is too voluminous for one pass). Findings that make the
next pass faster:

**Trivially correct, apply first:**
- `weakenEffAux` (the `induction h` over `HasType`): add `| handle => exact fun _ _ =>
  HasType.handle` next to the `perform` arm. (Verified.)

**Three small helper lemmas the perform-dispatch needs (none exist yet):**
1. `doPerformR_error_form` (purely structural, NO typing): `∀ k acc e, doPerformR label
   arg env k acc = .error e → e = .UnhandledEffect label arg`. Induction on `k`: the only
   `.error` is the `[]` base case; the matching-`Delimit` arm is `.ok`, every other frame
   recurses. This *replaces* the role of the now-false `stackWf_doPerformR_unhandled` for
   recovering `op = label`.
2. `reducePerform_perform_inv`: `reducePerform label arg env k = .perform op lift envP kP →
   op = label ∧ lift = arg ∧ envP = env ∧ kP = k`. Unfold `reducePerform`; `split` on
   `doPerformR …`; `.ok`→`.tau`≠`.perform`; `.error (.UnhandledEffect …)`→ inject (use
   lemma 1 to pin the fields = `label`/`arg`); `.error other`→ excluded by lemma 1.
3. `mStateWf_wait_conv`: `MStateWf (.wait op e k) τ ε0 → TyEquiv ε ε0 → MStateWf (.wait op
   e k) τ ε` — convert the inversion-lemma's `ε0` (with `TyEquiv ε ε0`) back to the outer
   `ε`. `EffContains` moves via `tyEquiv_effContains`; the stack via `StackWf.conv`. Needed
   wherever a frame-inversion lemma is used under a `.wait`-producing step
   (`reduceCall_perform_wait`, `preservation_perform`).

**Per-consumer perform dispatch (replacing the 7 `stackWf_doPerformR_unhandled` uses):**
- `reduceCall_perform_wait` (`cases hf`): the three NEW value arms are all **absurd** —
  `partialHandleNil`/`partialHandleOne` reduce via `reduceDeep`/accumulate to `.tau`,
  `partialResume` to `.tau` (`reduceCall … = .tau`, so `… = .perform` is `by simp
  [reduceCall, reduceDeep]`-absurd). The `partialPerformNil` arm: drop
  `stackWf_doPerformR_unhandled`; `simp only [reduceCall, reducePerform] at h`; `split at
  h` (3 arms: two absurd, the `UnhandledEffect` arm injects via lemma 1 then builds the
  `wait` as today).
- `preservation_perform` (`cases kont` form): the `Delimit` frame arm → `reduceApply` of a
  `Delimit` is `.tau (.V v, env, rest)` ≠ `.perform` → absurd. `Apply`/`CallWith` →
  `stackWf_{applyf,callwith}_inv` + `reduceCall_perform_wait` + `mStateWf_wait_conv` (to
  move `ε0`→`ε`). Trace/Assign/Arg → `.tau`-absurd.
- `preservation_V` (`cases kont` form): the perform-partial sub-case under `Apply`/`CallWith`
  now reaches a `.tau` step ONLY when **handled** → isolate behind `HandledPerformPreserves`
  (the perform partial applied, `doPerformR` returns `.ok`). The `Delimit`-frame arm is the
  **delimit-pop** (`.V v` meets `Delimit` → `.tau (.V v, env, rest)`), well-typed at row
  `tail` from `stackWf_delimit_inv` → supply `∃ε'` with `ε' := tail`.
- `progress` (`cases kont` form): perform-partial → `cases hdp : doPerformR …`: `.ok` →
  `Or.inl` (it `.tau`-steps, exhibit it); `.error` → the effect-escape disjunct, `op ∈ ε`
  from `perform_op_mem_ambient` (independent of `doPerformR`) + lemma 1 to name `op`.
  `Delimit`-frame → `Or.inl` (`.tau` pop).
- `reduce1Run_done_value_typed` (`cases kont` form): every new step (perform handled/escape,
  delimit-pop, reduceDeep, resume) is `.tau`/`.perform`, never `.done (.value _)` → all
  **absurd** (`split`/`simp`).

**`progress`/`preservation_E` also** need a `Handle l` arm in their `cases expr` (evals to
`partialHandleNil`, a `.tau`) before the `| _ =>` catch-all, and one extra `| ⟨_, h⟩` in the
`rcases hasType_expr_form` patterns (the new `Handle` disjunct).

**Order for the next pass:** lemmas 1–3 + `weakenEffAux` (cheap, do first) → convert
`preservation_perform` (smallest, validates the `cases kont`+inversion pattern) →
`reduce1Run_done_value_typed` (mostly absurd arms) → `progress` → `preservation_V` (biggest)
→ T7 rework. Build per-theorem. `HandledPerformPreserves` stays an isolated hypothesis
threaded like `BuiltinAppPreserves`.
