---
date: 2026-06-17
milestone: T5 (Handle/Delimit) — discharging the isolated obligations
status: PARTIAL — exact-row content banked (resume/install); general discharge needs a design step
---

# T5 Handle obligations — discharge attempt

Goal: turn `HandlerObligations` (`perform`/`install`/`resume`) and `TauKeepsRow` from
assumed hypotheses into theorems. Outcome: **the exact-row proof content for `resume` and
`install` is banked (green)**, plus a precise diagnosis of why the *general* obligations
are not directly provable. `perform` (the hard dispatch) and the `TauKeepsRow → RowEvolves`
rework are left for the follow-up, now sharply scoped.

## ✅ Banked this pass (green, `lake build` 1771 jobs, `lake exe spec` 104/104)

Two standalone lemmas in `Eyg/Types/Soundness.lean` (just before `preservation_V`):

- **`resume_preserves_exact`** — the `Resume` dispatch (`reduceCall (Resume acc iEnv) v →
  .V v, move acc rest`) preserves typing, *under an exact-row hypothesis* `TyEquiv εf ε`.
  Proof: `stackWf_resume hseg (StackWf.conv hrest …)` — the captured segment `acc.reverse`
  (`reply ⇒ ret`) composes onto `rest`, after converting `rest` to the segment's output
  endpoint `(ret, tail)` (possible because exact ⇒ `ε ≈ tail`).
- **`install_preserves_exact`** — the `reduceDeep` handler-install (`Handle l [handler]`
  applied to exec → `Apply exec :: Delimit l handler :: rest`) preserves typing, under
  `TyEquiv εf ε`. Proof: `StackWf.applyf … (StackWf.delimit hhandler (StackWf.conv hrest …))`
  at ambient `⟨l:(lift,reply)|tail⟩`; the unit control value is `hasTypeV_unit`.

These are the genuine proof content of two of the three handler dispatches.

## ⚠ Diagnosis — why the *general* `HandlerObligations` fields aren't directly provable

Each field quantifies over a **general** `Ty.EffWeaken εf ε` (`= TyEquiv εf ε ∨ TyEquiv εf
.empty`). But the discharge needs the **exact** row: the proof requires `TyEquiv ε tail`
(convert `rest : StackWf rest retTy ε τ` to the handled endpoint `(ret, tail)`), and
`tail ≈ εf`, so it needs `εf ≈ ε`. The **weakened** disjunct (`εf ≈ ∅`, `ε` arbitrary)
gives `tail ≈ ∅` but leaves `ε ≁ tail` — unprovable as stated.

Semantically: a weakened handle (`handle(l) h e` used at ambient `ε ⊋ tail`) means the
continuation `rest` after the handle runs at the *bigger* ambient `ε`, not at `tail`. But
`StackWf.delimit` rigidly types `rest` at the discharged `tail`. So the current
`StackWf.delimit` only fits the **exact** (`ε = tail`) case.

These are only *reachable* with exact rows (a `Resume` is applied at the handler's
discharged row; an exec runs at exactly its declared row), so the obligations as stated
are *too general* — provable only on the reachable (exact) fragment. `preservation_V`
passes the frame's general `hw` (from `stackWf_applyf_inv`), so it cannot supply exactness
locally.

## Remaining (sharply scoped follow-up)

1. **Wire `resume`/`install` in.** Two routes:
   - *(a) exactness invariant* — strengthen `MStateWf`/`StackWf` so handler-installed
     frames (the `CallWith resume`, the exec `Apply`) carry **exact** ambient rows, letting
     `preservation_V` pass `TyEquiv εf ε` to the now-exact obligations. Invasive (a new
     stack invariant), but localized.
   - *(b) generalized `StackWf.delimit`* — discharge `l` from the **ambient** `ε` (input row
     `⟨l:(lift,reply)|ε'⟩`, `rest` at `ε'`, with `tail ⊑ ε'`) rather than a fixed `tail`.
     Then weakened handles type directly and `resume`/`install` generalize. This is the
     "effect-weakening-through-`Delimit`" treatment the delivery note flagged; it also
     subsumes the row-subsumption story (Open Question 3).
   Route (b) is the cleaner end state (it makes the obligations *true as stated*).
2. **`perform`** — the hard dispatch (design §5): induction on the `doPerformR` stack-walk
   to the matching `Delimit`, typing the handler call (`handler arg resume`, `resume` via
   `stackWf_resume`). Independent of (1); the genuine novel proof.
3. **`TauKeepsRow → RowEvolves`** — replace the (false-in-general) `TauKeepsRow` gate with a
   row-evolution relation + downward `EffContains` reflection across `Delimit` discharges,
   making the effect-escape/divergence results unconditional. Depends on the `Delimit` row
   treatment from (1b).

Net: the `ε`-free value/no-bad-crash soundness remains unconditional for the full language;
this pass banks the exact-row dispatch proofs and pins the remaining work to the
`StackWf.delimit`-generalization design choice (1b), which unlocks (1), (3), and most of (2).
