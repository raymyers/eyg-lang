---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G20". EXECUTION session for the G19 corrected
  inline-strict `let_poly` reshape. Result: the reshape LANDED and is committed across the entire
  non-Soundness `HasType` cone (Typing/Generation/Generalization/Machine/Runtime/Substitution all
  per-file green, no `sorry`). The strict-sublevel discipline discharges the closure-readiness
  wrapper's `NoGenAt lvl h` premise FOR FREE (`noGenAt_letpoly_defn`), exactly as the corrected design
  predicted, and rejects nothing currently valid. The `Soundness.lean` grind is NOT done: it is a broad
  partial level-native + RT migration (103 errors, mostly pre-existing and unrelated to `let_poly`),
  orthogonal to and larger than the authorized reshape. Caveat 5 OPEN.
status: SHIPPED (reshape) + Soundness migration deferred. Soundness.lean left EXACTLY as found
  (pre-existing 27/26 partial-migration diff untouched, still red). Had explicit user authorization for
  the `HasType.let_poly` change; the corrected (inline-strict) form was executed and committed.
kind: progress
component: lean
---

# G1 Phase 6 (Session G20): the inline-strict `let_poly` reshape landed (non-Soundness cone green, committed)

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep/Edit +
`lake build`/`lake env lean`. **Explicit user authorization** covered the `HasType.let_poly` change
(the header-fence deferral every prior session avoided), specifically the G19 corrected inline-strict
realization.

## Key discovery that unblocked a committable checkpoint

G19 asserted the reshape was "all-or-nothing with NO committable per-file-green checkpoint short of the
full Soundness re-green." **That premise was wrong given the current tree state:** the *committed* HEAD
`f1156078` `Soundness.lean` **already does not build** (checked by stashing the working diff and
building the committed version — same level-native signature errors). So Soundness was already red at
HEAD; reshaping the non-Soundness cone and committing it (excluding Soundness) introduces **no new red
state** and IS a valid checkpoint. This is what made shipping possible this session.

## What shipped (one commit, after `f1156078`)

1. **`HasType.let_poly` reshaped** — dropped the opaque defn premise
   `hdefn : HasType lvl Γ ⟨.Lambda lx lbody, la⟩ defnTy ε`; inlined `lvl'`, `argTy`, `εb`, `retTy`,
   `hstrict : lvl < lvl'` (**strict**), `hfv : ∀ l ∈ argTy.levels, l < lvl'`,
   `hbodydefn : HasType lvl' ((lx,.mono argTy)::Γ) lbody retTy εb`, then `hcw`, `hbody` (body binding
   `genAtV lvl (.fun argTy εb retTy)`). `defnTy` is now `.fun argTy εb retTy`.
2. **Two helpers** (placed right after the inductive / after `noGenAt_of_lt`):
   - `HasType.letpoly_defn hstrict hfv hbodydefn := HasType.lam (le_of_lt hstrict) hfv hbodydefn`
     rebuilds the lam-node derivation for inversion sites.
   - `noGenAt_letpoly_defn hstrict hfv hbodydefn := NoGenAt.lam (le_of_lt hstrict) hfv
     (noGenAt_of_lt hbodydefn hstrict)` — `NoGenAt lvl` of that node **for free** (the payoff:
     `noGenAt_of_lt hbodydefn hstrict` fires because `lvl < lvl'`).
3. **Companion derivation-indexed inductives** `NoGenAt`/`HasTypeRT`/`LevelsBelow` `let_poly` arms
   reshaped to reference the new constructor. **Gotcha:** with `hdefn` gone, the Lambda annotation `la`
   became an unconstrained autoImplicit → "failed to infer type of binder `la`"; fixed by pinning it
   via `(la := la)` in the `HasType.let_poly` application inside each arm.
4. **Every consumer updated** (mechanical, arm-for-arm): `hasType_subst` (reconstruct the defn-lam-body
   IH via `polyAboveFV_sub`+`polyAboveFV_bind`, `hfv'` via `mem_levels_substAt`, `simp only [Ty.substAt]
   at hbodyIH`), `hasType_substAt_le` (same but `mem_levels_substAt_strong`, `le_of_lt (lt_trans …)`),
   `noGenAt_of_lt` (`ihd (lt_trans hlt hstrict)`), `inv_let_rt` (returns `NoGenAt lvl hdefn` too),
   `hasType_ctxConv` (defn-body IH extends `Δ` by `(lx,.mono argTy)`), `hasTypeRT_ctxConv`,
   `LevelsBelow.mono`, `exists_levelsBelow`, `hasType_fullRaise` (`hstrict' := by omega`, defn-body via
   `ihdefn (by omega : t ≤ lvl')` + `raiseScheme_U_mono`).
5. **`inv_let` (Generation) + `inv_let_rt` now hand `NoGenAt lvl hdefn` for free** — the exact premise
   `genAtV_closure_ready_value_node` (Substitution:167, unchanged) takes as a plain hypothesis. This is
   the whole point: the Soundness `let_poly` preservation site gets `NoGenAt` from inversion with no
   external witness and no mutual induction.
6. **Examples:** the real whole-program derivations (`let a=\x.x in let c=\z.z in c`, and the
   referencing `\w. a w` variant) reconstructed with the strict constructor (they already descended
   strictly, `lvl'=lvl+1`). The **residual-corner witnesses** (`advPerfBody`/`advDefnH`/`advH_defn`/
   `advPerf_body1`/`advPerf_lvl1`/`advPerf_body2`/`advPerf_lvl2` + their `NoGenAt` lemmas) — which
   deliberately built an inner `let_poly` with a **non-strict** (`lvl'=lvl`) defn lambda to characterize
   the "residual corner" — are now **unconstructable by design** (that corner is exactly what strict
   forbids), so they were **removed** (private, unreferenced exploration scaffolding; a replacement
   comment records why). `advH_ctxwf` was kept (used by `esc*`). The `esc*` witnesses use the
   already-strict `escH_defn` (`lvl'=n+1`) and were reconstructed via the new constructor (`escBodyAt`).

**Per-file green + committed:** `Typing`, `Generation`, `Generalization`, `Machine`, `Runtime`,
`Substitution` all build (only pre-existing simp-arg warnings); `grep sorry` empty.

## Design confirmation (the corrected G19 recipe held)

`noGenAt_letpoly_defn` discharges the wrapper's `NoGenAt lvl h` with **no** external witness and **no**
induction-induction — precisely the G19 prediction. The strict rule **rejected nothing currently
valid**: every real construction site (Typing whole-programs, Generalization sanity examples) already
descended strictly; only the deliberately-non-strict *meta-witnesses* were lost, and those exist solely
to document the gap the reshape closes. Effect/result-only "residual" cases (`advPerf`, `defnPerf`) are
freely re-typable at `lvl'=lvl+1`, so no real program is excluded.

## What remains — and why it is NOT the reshape

`Soundness.lean` is **red (103 errors)** but this is a **broad partial level-native + `HasTypeRT`
migration**, mostly PRE-EXISTING and unrelated to `let_poly`: lines 34–247 (e.g. `MStateWf.run`
mismatch, `hvty.conv` field-not-found, `effWeaken_trans` arity, conv-as-function) are **byte-identical**
to the errors present before this session's reshape (captured at session start). Completing Soundness =
finishing that whole level-native migration (the ~10-session live-LSP wall), which is orthogonal to and
much larger than the authorized reshape. The `let_poly`-specific Soundness sites the next session must
rewire to the new shape: `:72` (`effWeaken` reconstructs `HasType.let_poly`), `:226`/`:243` (the
`inv_let` poly consumer + `genAtV_closure_ready_value_node` call — now feed it the free `NoGenAt`),
`:2953` (a second `inv_let` consumer). Per the task's standing instruction, `Soundness.lean` was **not
edited** this session (its pre-existing 27/26 partial-migration diff is untouched, still uncommitted).

## Validation gates

- Non-Soundness Types modules: `lake build` green, no `sorry`. Committed.
- Whole-project `lake build` / `lake exe spec` / axioms: NOT applicable yet (Soundness red — as it was
  at HEAD `f1156078`, which also does not build Soundness). No red Soundness commit was made.

## Tree state at stop

- New commit (after `f1156078`) with `Typing.lean`, `Generation.lean`, `Generalization.lean` reshaped
  and per-file green; plus this note + the plan Phase 6/7 update.
- `Soundness.lean`: EXACTLY as found (pre-existing uncommitted partial migration, untouched, still red).
- No `sorry` anywhere in `Eyg/Types/*.lean`. Axioms unchanged. Caveat 5 OPEN — but the authorized
  `let_poly` reshape (the last-identified conceptual blocker) is DONE; the sole remaining work is the
  mechanical level-native Soundness migration.
