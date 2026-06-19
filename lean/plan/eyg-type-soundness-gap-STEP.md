Perform these steps:

PLAN is `lean/plan/eyg-type-soundness-gaps.md` (closing Caveats 4 & 5 of
`lean/plan/report/type-soundness-report.md`).

* Study PLAN and pick a next task.
* Check for pending git changes, your choice to finish them or reset.
* Attempt to complete a tested task slice.
  * If success: update PLAN and commit.
  * If failed: record in `lean/plan/progress/*.md` and reference in PLAN, commit only that plan and progress change.

# The fork: prove OR refute

Each milestone (G1 nested let-polymorphism, G2 effectful-builder `fix`) is **done** by *either*:
  1. **Proving soundness** — the headline `soundness`/`soundness_evalR` covers the feature with the
     restriction removed, axioms `propext`/`Classical.choice`/`Quot.sound` only, no `sorry`,
     `lake build` + `lake exe spec` 104/104.
  2. **A machine-checked counterexample** — a closed Lean term well-typed by the un-restricted
     reference rule that reduces (under `Reduce`/`evalR`) to a bad crash (`Reason.IsBad`) or an
     out-of-row effect. Model it on `generalizes_subst_false`/`cex_pos`/`cex_neg`
     (`Eyg/Types/Generalization.lean`) and the base-type-`fix` finding
     (`progress/2026-06-17-fix-base-type-unsoundness.md`); confirm reference-analyzer acceptance via
     nix `gleam` where relevant. A counterexample is a real result — record it and update the report.

Don't chase a proof past the point where a counterexample is the likelier truth, and don't chase a
counterexample when the proof obligation is just bookkeeping. G1 is expected to prove; G2 is the one
that might refute.

# Tech Guidelines

This is a Lean project run with Nix.

The substitution-stable foundations are already landed — reuse them, don't re-derive:
  * G1: `generalizesAt_subst`, `genAt`, `LevelMap`/`LevelMap.mono`, `CtxWf` (`Eyg/Types/Generalization.lean`).
  * G2: `EffWeaken`/`subst_effWeaken` (the empty-only weakening) and `EffSub` (membership, NOT
    substitution-stable — that's the thing G2 must fix) in `Eyg/Types/{Ty,Scheme,EffSub}.lean`.

Sometimes agents get caught up spinning their wheels with proofs about the built-ins. Don't get stuck
in rabbit holes. Bail and leave progress notes if you need to, set yourself up for success next time.

The Lean code is a port of the Gleam EYG interpreter. Generally, the Gleam version should be
considered authoritative. Its type analyzer may be useful in understanding the rules:
`packages/gleam_analysis`. The `fix` scheme lives at `contextual.gleam:530`.
