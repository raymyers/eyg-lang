---
date: 2026-06-18
milestone: T7 — discharge `TauKeepsRow` (base-row preservation engine + effect-escape keystone DELIVERED)
status: KEYSTONE DELIVERED — full consumer re-thread (remove `TauKeepsRow`) remains
---

# T7 RowEvolves — base-row preservation + `soundnessR_effect_B` delivered

Builds on `2026-06-18-T7-rowevolves.md` (the design). The **base-row preservation engine and
the effect-escape keystone are now proved and on the branch** (4 commits). The honest
effect-escape soundness (`op` escapes ⇒ `op ∈ ε_init`) holds **without `TauKeepsRow`**, modulo
only the dischargeable `BuiltinAppPreservesB`. What remains is the *mechanical-but-voluminous*
re-thread of the ~15 `hkeep`-gated consumers to actually delete `TauKeepsRow`.

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

## Remaining: re-thread the 15 `hkeep` consumers, then delete `TauKeepsRow`

`TauKeepsRow` is still *defined* and taken by 15 theorems (grep `(hkeep : TauKeepsRow`):
`preservation_keep_fix`, `soundnessR_effect` (superseded by `_B`), `soundness_evalR`,
`pure_no_perform_evalR`, `soundness_evalR_pure`, `soundness_behaviorsR_suspended`, `ωTr_all_wf`,
`ωTr_effect_safe`, `soundness_behaviorsR_diverges`, `mTr_terminal_wf`,
`soundness_behaviorsR_terminates_value`/`_noBadCrash`, `pure_no_suspend_behaviorsR`,
`pure_no_perform_diverges`, `soundness` (headline). Each must swap `MStateWf`+`hkeep` for
`MStateWfB`+`hsatB`, concluding `op ∈ εbot` off the escape instead of `op ∈ ε` off `hkeep`.

**Two sub-cases, by difficulty:**

- **`evalR`-level (no reply) — easy.** `soundness_evalR`/`pure_no_perform_evalR`/`soundness_evalR_pure`
  only see `tau`+`perform` (closed `evalR` never replies). Redirect their effect arm to
  `soundnessR_effect_B` (start from `mStateWfB_initial`); thread `hsatB` instead of `hkeep`. The
  value/no-bad-crash arms are already unconditional (`FixPreserves`/`FixNoBadCrash`). Mechanical.

- **`BehaviorsR`-level with reply (divergence / mTr / suspended) — one subtlety.** `ωTr_all_wf`/
  `mTr_terminal_wf` fold `preservation_keep_fix` over traces that contain `reply` labels, so they
  need a **`preservation_keep_B`** (tau→`preservation_tau_B`, perform→`(preservation_perform_B …).1`,
  **reply→a `ReplyContractB`**). The reply case is the only real design point:
  - the `wait` is typed with **`εtop`'s** op-membership reply `b` (stack expects `replyTy ≈ b`),
    but the world's reply contract is naturally about the **declared `εbot`** (`= ε_init`).
  - so the reply value typed at `εbot`'s reply `b''` must be re-typed at `replyTy ≈ b`. This needs
    **`b ≈ b''`**, i.e. the `εtop→εbot` membership transfer must carry the reply **`TyEquiv`**.
  - **Action:** strengthen `stackWfB_escape` to return `∃ a' b', EffContains εbot op a' b' ∧
    TyEquiv a a' ∧ TyEquiv b b'` (the proof already has these links — `tyEquiv_effContains_mp`
    returns them; they are currently dropped with `_`). Then `ReplyContractB εbot` + the link
    types the reply at `replyTy`. With `preservation_keep_B`, mirror `ωTr_all_wf`/`ωTr_effect_safe`/
    `soundness_behaviorsR_diverges`/`mTr_terminal_wf`/`_terminates_*`/`_suspended`/`pure_*` as `_B`.

Finally delete `TauKeepsRow`/`preservation_keep_fix` and point `soundness` at the `_B` chain. Net:
the row-dependent effect-safety / divergence / suspension results become unconditional in
`TauKeepsRow` (gated only on `BuiltinAppPreservesB` + `Fix*`, both true & dischargeable).

## Then: discharge `BuiltinAppPreservesB`

The `.tau` builtin-saturation base-row obligation. The non-`B` `BuiltinAppPreserves` is *proven*
(`builtinAppPreserves : FixPreserves → BuiltinAppPreserves`); the B-form re-runs the same T6b
per-arity machinery (`builtinApp_arity1/2`, `scheme_cases`, the saturate/accumulate split)
threading `εbot` — the successor lands on `rest` (general builtins) or pushes `fixed` frames, so
`εbot` is preserved structurally. Mechanical; isolate `FixPreservesB` like `FixPreserves`.

## Verified this pass
- All 4 commits: `lake build` 1771 green, `lake exe spec` 104/104, axioms clean, no new `axiom`s.
- The `StackSegWf`-needs-no-B insight held: every dispatch B-lemma reused the segment machinery
  verbatim, only threading `εbot` on the base — kept the mirrors purely mechanical.
