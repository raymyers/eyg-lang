---
name: eyg-type-soundness2-gaps-plan
description: Close the two soundness-coverage gaps (Caveats 4 & 5 of the type-soundness report) — effectful-builder `fix` and nested let-polymorphism — by either proving soundness for the full feature or producing a machine-checked counterexample.
date: 2026-06-19
---

# EYG Type Soundness — Closing the Coverage Gaps (Caveats 4 & 5)

## Goal

The headline soundness theorem (`Eyg.Types.soundness`, axioms clean, no `sorry`) is
**unconditional but under-approximating**: it holds for a *fragment* of the language. Two
restrictions in `lean/plan/report/type-soundness-report.md` are genuine coverage gaps — the
theorem says nothing about programs that use these features:

- **Caveat 5 — nested let-polymorphism.** `HasType.let_poly` requires `Tree.Node.noLet lbody`
  (`Typing.lean:103`): a generalized lambda's body may contain no `let`. Rank-1 / combinator
  polymorphism works; *nested* let-generalization is unproven.
- **Caveat 4 — effectful-builder `fix`.** `Builtins.scheme "fix"` is pinned to a `∅`-latent
  (pure) builder; `FixPreserves`/`FixPreservesB` are proved only there. Recursion whose
  builder performs effects (`q1 ≠ ∅`) is unproven — and the reference analyzer accepts it.

### The deliverable for each gap (the fork)

For each milestone, **either outcome counts as resolving it**:

1. **Prove soundness** — extend the typing judgment + preservation engines so the headline
   `soundness`/`soundness_evalR` cover the feature *without* the restriction (still axiom-clean,
   no `sorry`).
2. **Find a counterexample** — a machine-checked Lean term that is well-typed by the
   (un-restricted) reference rule yet reduces under `Reduce`/`evalR` to a *bad* crash
   (`Reason.IsBad`) or an out-of-row effect. This is "done for now": it proves the restriction
   is **load-bearing**, not a proof-engineering artifact, and converts the caveat from "gap" to
   "known unsoundness of the source language" (as already happened for base-type `fix`, Open
   Question 4 — see `progress/2026-06-17-fix-base-type-unsoundness.md` for the template).

A counterexample is recorded the way `generalizes_subst_false` / `cex_pos` / `cex_neg`
(`Generalization.lean:507-550`) and the base-type-`fix` finding already are: a closed Lean proof
in-repo + a progress note + a one-line plan update.

## What is already landed (do not re-derive)

**For Caveat 5 (the substitution-stable level-indexed machinery is built and green):**
- `Scheme.genAt n d`, `Ty.genArity`, `Ty.reindexGen`, `genArity_spec` — computed generalization.
- `Ty.LevelMap n σ` + `Ty.LevelMap.mono` (`Generalization.lean:218,228`) — the ambient-into-ambient
  substitution class, automatically valid at every deeper level (kills the "re-level on descent" crux).
- `genAt_substScheme`, `genArity_subst` (`:342,:305`) — the `subst`/`shift` commutation.
- **`generalizesAt_subst`** (`:371`) — `GeneralizesAt` *is* substitution-stable for level-maps. **This
  is the lemma the naive `Generalizes` lacked.**
- `genAt_generalizesAt`, `genAt_generalizes`, `generalizesAt_to_generalizes`, `generalizesAt_mono`.
- `generalizes_subst_false` + `cex_pos`/`cex_neg` — machine-checked proof the *easy* route fails.
- `CtxWf n Γ` (+ `mono`/`cons`/`substCtx`/`fixed`) and `Scheme.freeVars` metatheory (`Scheme.lean`).
- The blocker write-ups: `progress/2026-06-18-T6-let_poly-level-redesign-design.md`,
  `…-instantiation-levelmap-gap.md`, `…-cascade-attempt.md` (+ WIP patch
  `progress/2026-06-18-T6-let_poly-cascade-WIP.patch`).

**For Caveat 4 (the empty-restricted weakening is built; the general one is not):**
- `Ty.EffWeaken εf ε := TyEquiv εf ε ∨ TyEquiv εf .empty` + `subst_effWeaken` (`Ty.lean:150`,
  `Scheme.lean:89`) — the substitution-stable but *empty-only* weakening, premise of `HasType.app`.
- `Ty.EffSub` (membership subrow) + `effSub_refl/trans/empty`, `tyEquiv_effSub`, `effSub_extend`,
  `effContains_mono`, `effContains_extend_inv` (`EffSub.lean`) — **but bare `EffSub` is NOT
  substitution-stable** (the `EffSub (var 0) .empty` vs. its `σ`-image gap, `Ty.lean:138`).
- `HasTypeV.partialFixed` (arrow-fixpoint, pure builder) + `fixed`-re-application preservation
  (`progress/2026-06-17-T6b-partialFixed-reapplication.md`).
- The convergence finding (`eyg-type-soundness.md` Open Question 3): general row subsumption
  `tail ⊑ ε` is the *single* foundation gating effectful `fix`, the exact Handle dispatch, and
  T7 row-evolution.

---

## Milestone G1 — Nested let-polymorphism (Caveat 5)

**Hypothesis:** ~90% proof engineering. The math (value-restricted HM with de Bruijn levels) is
standard and the substitution-stable core (`generalizesAt_subst`) is already proved. The gap is
threading a level through the judgment and re-greening both preservation engines.

**Deliverable:** drop `Tree.Node.noLet` from `HasType.let_poly`; re-green
`preservation`/`progress`/`soundness*`; a nested-polymorphism sanity `example` types.

- [ ] **Decide the level carrier (item-1 fork, revisited).** Confirm or revise the
      `progress/2026-06-18-T6-let_poly-levelmap-mono-and-wfbelow-decision.md` decision: a light
      `WfLevel n` inductive over derivations supplying the gate `n ≤ n_node`, vs. a full
      `HasTypeAt n` level-indexed judgment. Record the choice + blast radius in a progress note.
- [ ] **Re-state `hasType_subst` with the `LevelMap n σ` premise.** The `let_poly` arm discharges
      via `generalizesAt_subst` + `genAt_substScheme` + `ctxWf_substCtx`; non-`let_poly` arms
      thread `LevelMap.mono`. (The `noLet`-vacuous arm is *removed*.) This is the wall the
      restricted route sidestepped — the substitution-stable `generalizesAt_subst` is what makes
      it tractable now.
- [ ] **Pin the `let_poly` rule's scheme to `genAt n defnTy`** (drop `noLet`); add the level
      carrier premise; update `inv_let`, `hasType_ctxConv` (`generalizes_ctxConv` arm),
      `hasType_expr_form`.
- [ ] **Readiness keystone for nested bodies.** Re-prove `genAt_closure_ready` / the `Assign`-pop
      readiness `∀ args, HasTypeV (Closure …) (s.instantiate args)` when the generalized body
      itself contains `let_poly`. **This is the genuine crux** — the
      `instantiation-vs-LevelMap` gap (`progress/2026-06-18-T6-let_poly-instantiation-levelmap-gap.md`)
      says the instantiation witness `σ_args` is a *down-shift*, not a `LevelMap`. Resolve via the
      level discipline (re-levelled body typing on descent) **or** surface a counterexample here.
- [ ] **Re-green both engines.** Thread the (constant, light) level invariant through `MStateWf`,
      `StackWfV`/`StackWfE` and the B-mirror `StackWfVB`/`StackWfEB`; the value-coupling shape is
      unchanged from the restricted delivery. `lake build` + `lake exe spec` 104/104, axioms clean.
- [ ] **Sanity example** typing a *nested* polymorphic let (e.g.
      `let pair = \x. (let dup = \y. cons y (cons y tail) in dup x) in …`) at the expected type —
      a term the current `noLet` rule rejects.
- [ ] **(Fork branch) Counterexample search.** If the readiness keystone stalls, hunt the failure
      directly: a closed term where a nested generalized binding instantiates at two incompatible
      types and the runtime closure cannot satisfy both → a `Reason.IsBad` crash or wrong-type
      value under `evalR`. Machine-check it (the `generalizes_subst_false` style) and record as
      DONE. *(Prior: HM let-poly is sound, so expect this branch to fail — but a CBV/effect
      interaction could surprise; the value restriction is what makes it sound, so probe a
      non-value generalized binding if any path admits one.)*

> **✅ G2 DONE (2026-06-19) — the fork REFUTES.** Effectful-builder `fix` is **unsound**, not
> a proof-engineering gap. Machine-checked counterexample
> (`progress/2026-06-19-G2-effectful-fix-unsoundness.md`, `Eyg/Types/CexEffectfulFix.lean`): a
> closed program the reference analyzer types as pure `Integer` (`#(Ok(Nil), "Integer", "")`)
> performs an **unhandled / out-of-row `Log`** under both the reference interpreter and the Lean
> `eval`/`evalR`. Root cause: the runtime re-runs the builder on every recursive self-application
> (`do_fixed`), so a builder's *construction* effects re-fire at each call, outside any handler
> installed at `fix`-creation. This **justifies the Lean pure-builder pin** (`q1 = ∅`) as
> load-bearing — the same shape as the base-type-`fix` finding (Open Question 4). The `EffSub'` /
> un-pinning bullets below are therefore **moot for soundness** (there is no sound effectful-`fix`
> to track); kept only as a record of the original plan. A genuine fix is source-language-side
> (pin `q1=∅` in `contextual.gleam`, or make the recursive binding lazy).

## Milestone G2 — Effectful-builder `fix` + general row subsumption (Caveat 4)

**Hypothesis:** ~60% proof engineering / genuinely open. `fix` was already unsound once
(base-type, Open Question 4), the required subsumption relation does **not** exist yet, and the
membership `EffSub` repeats the same substitution-stability failure that bit let-poly. This is the
milestone most likely to surface a real language issue.

**Deliverable:** un-pin `Builtins.scheme "fix"` from the pure builder (allow `q1 ≠ ∅`); discharge
`FixPreserves`/`FixPreservesB` for effectful builders so the headline soundness covers them — **or**
a counterexample showing effectful-builder `fix` is unsound as the analyzer types it.

- [ ] **Build the substitution-stable, row-variable-aware subrow `EffSub'`** (Open Question 3's
      "single highest-leverage foundation"). The membership `EffSub` is **not** substitution-stable
      (`Ty.lean:138`) and `EffWeaken` is empty-only. Design a relation that (a) allows `tail ⊑ ε`
      with a row tail variable, (b) survives `subst` (state and prove `subst_effSub'`), (c) implies
      `EffContains` monotonicity (so effect safety survives weakening by construction). Land it
      additively in `Eyg/Types/EffSub.lean`, green + axiom-clean, like the `EffWeaken` foundation.
- [ ] **Generalize `HasType.app` / `StackWf.arg/applyf/callwith`** from `EffWeaken` to `EffSub'`;
      re-prove `weakenEff` admissible and `inv_app`; thread `subst_effSub'` through `hasType_subst`.
      (Mirrors the delivered `EffWeaken` consuming slice — same 5-site shape.)
- [ ] **Un-pin the `fix` scheme.** Restore `Builtins.scheme "fix"`'s builder latent to a row
      variable `q1` (matching `contextual.gleam:530`, keeping the arrow-fixpoint hardening from
      Open Question 4). Keep the strict-under-application `PartialBuiltinWf` invariant.
- [ ] **Discharge `FixPreserves`/`FixPreservesB` for effectful builders.** The `fixed`
      re-application `builder (fix builder) arg` now applies an *effectful* builder under the
      recursion ambient: re-prove `fixed_reapply_preserves` weakening the builder's latent `q1`
      into the ambient via `EffSub'` instead of `effWeaken_empty`. Generalize `HasTypeV.partialFixed`
      off the pure-builder pin.
- [ ] **Re-green the headline.** `fixPreserves`/`fixPreservesB` proved for the general scheme;
      `soundness`/`soundness_evalR`/`soundness_evalR_pure` still take only `HasType [] prog τ ε`,
      axioms clean, no `sorry`, `lake build` + spec 104/104.
- [ ] **(Bonus, same foundation) Discharge the Handle dispatch under general rows.** Per the Open
      Question 3 convergence note, `EffSub'` + a generalized `StackWf.delimit` (`tail ⊑ ε`) also
      lets `resume_preserves_exact`/`install_preserves_exact` be wired in unconditionally — fold in
      if cheap once `EffSub'` exists. *(Optional within G2; tracks the same relation.)*
- [ ] **(Fork branch) Counterexample search.** Probe the CBV-`fix`-with-effects failure mode: a
      closed program where an effectful builder's recursive knot lets a `perform` escape the
      declared row, or where the `fixed` partial inhabits a non-arrow under an effect row →
      `Reason.IsBad` / out-of-row effect under `evalR`. Confirm against the reference analyzer
      (nix `gleam`, the Open Question 4 method: run `j.infer`, show it accepts) + machine-check the
      `Reduce` crash. Record as DONE — this would extend the base-type-`fix` unsoundness story to
      effectful builders and justify keeping the pure-builder pin (or hardening the analyzer again).

---

## Definition of done

- [ ] **G1 (Caveat 5):** either `HasType.let_poly` carries no `noLet` restriction and the headline
      soundness covers nested let-polymorphism (axioms clean, spec 104/104), **or** a machine-checked
      counterexample shows it unsound and the restriction is justified in-plan.
- [x] **G2 (Caveat 4):** DONE by counterexample — machine-checked + reference-analyzer-confirmed
      that effectful-builder `fix` is unsound (`progress/2026-06-19-G2-effectful-fix-unsoundness.md`,
      `Eyg/Types/CexEffectfulFix.lean`). The pure-builder pin is justified as load-bearing.
- [ ] The type-soundness report (`lean/plan/report/type-soundness-report.md`) is updated: each
      resolved caveat is either struck (proven) or re-classified from "coverage gap" to "known
      source-language unsoundness" (counterexample), with the in-repo proof referenced.
- [ ] No regression: all existing headline theorems remain `propext`/`Classical.choice`/`Quot.sound`
      only, zero `sorry`.

## Notes on the two outcomes

- **Common root.** Both gaps trace to relations that are not stable under type substitution
  (`Generalizes`, bare `EffSub`). G1's repair (`generalizesAt_subst`) is the proof that the
  level-indexed reformulation fixes it; G2 needs the *same move* for effect rows (`EffSub'`). A win
  in G1 is direct evidence the G2 route is sound proof engineering rather than a dead end.
- **A counterexample is a real result.** Per the prompt, finding one is "done for now." The
  base-type-`fix` precedent (Open Question 4) shows the value: it converted a silent unsoundness into
  an explicit, analyzer-level fix. The same standard applies here — a counterexample *strengthens* the
  overall soundness story by precisely delimiting what is and isn't safe.
