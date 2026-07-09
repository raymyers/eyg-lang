---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G14". Answers the task's central "is the narrow version
  sufficient?" question. Finding: NO — the actual `let_poly` preservation call site genuinely needs the
  general normalization. But it sharpens the target: the correct packaging is *proof irrelevance*
  (route (a), G7/G8) over an EXISTENCE statement (`hasType_strictify`) with `lvl`/`Γ`/`τ`/`ε` held FIXED
  — strictly weaker than the functorial `hasType_raise` (raise `lvl`+`Γ`+`τ`+`ε` together) that G9–G13
  pursued and that carries the two-modes conflict. This is a re-attack the prior sessions did not try.
status: PARTIAL (investigation only). No code changes this session — no LSP (canary failed), and a blind
  batch-`lake env lean` mutual induction is too risky; Soundness.lean left EXACTLY as found (pre-existing
  uncommitted 53-line partial migration, untouched). Caveat 5 OPEN. Full green NOT reached. No commit.
kind: progress
component: lean (analysis; Eyg/Types/Substitution.lean + Typing.lean + Soundness.lean call site)
---

# G1 Phase 6 (Session G14): the narrow version is insufficient; `hasType_strictify` (existence + proof irrelevance) is the real, sharper target

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake env lean`
only. This session did the "genuinely investigate whether the narrow version suffices" step the task
prioritized, tracing the ACTUAL `Soundness.lean` call site rather than the maximal-generality raise
theorem the last several sessions built toward.

## What the actual call site actually needs (Soundness.lean:243, the `let_poly` preservation case)

**`genAtV_closure_ready_value_node` (Substitution.lean:167) is already fully proven** and — importantly
— does **not** consume any raise/relabel theorem. It reaches closure readiness via the `NoGenAt`/
`inv_lambda_noGenAt` + non-strict keystone `genAtV_instantiate_lam_ready_le` route (G1/G2 lineage), not
the raise route (G9–G13). Its explicit premises, at the call site's `hdefn : HasType lvl Γ ⟨.Lambda lx
lbody, la⟩ defnTy ε`, `hcw : CtxWfV lvl Γ`, `henv : EnvWf env Γ`, are exactly three still-open facts:

1. **`hlvl0 : lvl ≠ 0`** — EASY. Enter `soundness`/`soundness_evalR` at ambient level `≥ 1` (levels only
   increase under reduction), i.e. thread `1 ≤ lvl` through `MStateWf`. Not the crux.
2. **`hΓpa : PolyAboveFV lvl Γ ⟨.Lambda lx lbody, la⟩`** — MOSTLY EASY. `PolyAboveFV lvl Γ e` demands, per
   binding `s` that `e` looks up, `s.arity = 0 ∨ (s.level ≠ 0 ∧ s.level ≠ lvl)`. From `hcw : CtxWfV lvl Γ`
   (= every binding-body level `< lvl`): a poly binding `genAtV k d` with `arity ≠ 0` has `k ∈ d.levels =
   s.body.levels`, so `k < lvl` ⇒ `s.level ≠ lvl` ✓. The only residual is `s.level ≠ 0` when a binding is
   `genAtV 0` with `arity ≠ 0` — ruled out once all gen levels are `≥ 1`, which follows from the same
   "ambient `≥ 1` everywhere" invariant as (1). A new additive lemma `polyAboveFV_of_ctxWfV` (CtxWfV +
   gen-levels-`≥ 1`) discharges it; the gen-levels-`≥ 1` side must be threaded via the machine invariant.
   Not the crux.
3. **`hng : NoGenAt lvl hdefn`** — **THE CRUX** (the call site currently mis-passes `hdefn` itself into
   this slot; that is part of the incomplete migration, not a real discharge).

## Why `NoGenAt lvl hdefn` is genuinely the general problem (narrow answer: NO)

- `noGenAt_of_lt` yields `NoGenAt ℓ h` only for `ℓ < (root level of h)`. Here root level `= lvl`, `ℓ =
  lvl` ⇒ needs `lvl < lvl`, false. The generalization level and the defn's typing level coincide by
  construction (`HasType.let_poly` types the defn at the *same* ambient `lvl` it generalizes at).
- Via `inv_lambda_noGenAt`, `NoGenAt lvl hdefn` reduces to `NoGenAt lvl hbody`, where `hbody` is the
  lambda body at stored sublevel `lvl'` with `lvl ≤ lvl'` (`HasType.lam` uses **non-strict** `lvl ≤
  lvl'`). If `lvl' > lvl` strict: **free** via `noGenAt_of_lt`. If `lvl' = lvl`: an inner `let_poly` in
  the body can generalize at exactly `lvl`, and `NoGenAt lvl` genuinely fails there (confirmed against
  `hasType_substAt_le`'s `let_poly` arm, which needs `ℓ ≠ inner-gen-level` = `lvl ≠ lvl` — false).
- The declarative system PERMITS `lvl' = lvl`, and `soundness`/`soundness_evalR` quantify over **all**
  derivations `h` (and `hrt`), so preservation must handle the `lvl' = lvl` case. The task's suggested
  "raise past one binder, context already `CtxWfV`" narrowing does **not** sidestep this: it *is* the
  G13 two-modes conflict — the level-`lvl` tags that are the outer lambda's own generalization variables
  must STAY at `lvl` while an inner same-level `let_poly`'s gen variables must MOVE, and they are
  tag-indistinguishable. So **the narrow version is not sufficient for the (single) real call site.**

## The sharper, correct target this session isolates: `hasType_strictify` (existence + proof irrelevance)

`HasType : Nat → Ctx → Node → Ty → Ty → Prop` is a **Prop** (verified: `advPerf_lvl1_noGenAt :=
advPerf_lvl2_noGenAt` at Typing.lean:1811 already relies on it). Hence any two derivations of the SAME
judgment are equal by proof irrelevance, and `NoGenAt lvl (runtime hdefn) = NoGenAt lvl hdefn'` for any
`hdefn'` proving the same judgment. It therefore **suffices** to prove the EXISTENCE of a level-strict
("canonical") derivation of the identical judgment:

```
inductive StrictSub : {lvl Γ e τ ε} → HasType lvl Γ e τ ε → Prop     -- NoGenAt/LevelsBelow-shaped
  -- lam/let_/let_poly arms additionally record `lvl < lvl'` (strict) and recurse; atoms are leaves
theorem hasType_strictify (h : HasType lvl Γ e τ ε) : ∃ h' : HasType lvl Γ e τ ε, StrictSub h'
-- then: StrictSub h' → ∀ ℓ ≤ lvl, NoGenAt ℓ h'   (a `noGenAt_of_lt`-style descent)
-- then: NoGenAt lvl hdefn := (proof irrelevance) ▸ (that NoGenAt on the strictified hdefn')
```

**Why this is strictly weaker than the functorial `hasType_raise` G9–G13 pursued (and a genuine
re-attack):** `hasType_strictify` holds `lvl`, `Γ`, `τ`, `ε` all **FIXED** — only the internal stored
sublevels (`lvl'` in each lam/let_/let_poly) are re-chosen strictly increasing. The G13 two-modes
conflict was **specifically** about the shared, mode-independent `raiseCtx`/`raiseScheme` context-raise
operation on a raised-`Γ` — which does not appear here at all (the context is unchanged). The prior
sessions only ever attempted the functorial raise-`lvl`+`Γ`+`τ`+`ε` statement; the judgment-fixed
existence statement + proof irrelevance (route (a), the G7/G8 line) was demonstrated on individual
witnesses (`advPerf`, `escLam`) but never lifted to a general theorem. That lift is the recommended
next move.

**Residual risk (honest):** the construction of `hdefn'` must, at each `let_poly`, choose a fresh gen
level strictly above the ambient and re-derive its body, re-instantiating uses (G8: re-instantiation
reproduces the same `retTy`, so escaped inner-gen variables are reproducible). The one configuration
that could still bite is **two `let_poly`s forced to the same level whose generalized variables
intertwine in a shared type** (the depth-≥2 cross-level case). Whether that is actually constructible —
vs. always separable by assigning distinct fresh levels in a bottom-up (innermost-first) or top-down
recursion — is the open question that decides whether `hasType_strictify` falls to a clean fresh-level
mutual induction or genuinely re-hits a wall. This wants live LSP goal-state to build arm-by-arm; it is
NOT safely buildable blind under 40 s batch `lake env lean` cycles.

## Existing infrastructure inventory (what is already green and reusable)

- `NoGenAt` (Typing.lean:511), `noGenAt_of_lt` (768, `ℓ < lvl ⇒ NoGenAt ℓ`), `inv_lambda_noGenAt` (742).
- `LevelsBelow` (1202) + `exists_levelsBelow` (1302, every derivation is bounded by some `N`) —
  the finite-level-cap tool a fresh-level construction picks its offset from.
- `HasTypeRT` (832) is wired into `MStateWf.E` (Machine.lean:406) but does **not** help here: its `lam`
  and `let_poly` arms carry **no** body premise, so it says nothing about a defn lambda's internals.
- `genAtV_closure_ready_value_node` (Substitution.lean:167) — the consumer, already proven, awaiting the
  three premises above.
- The functorial-raise partials `raiseScheme`/`raiseCtx`/`raiseCtx_fix`/`raiseScheme_genAtV_instantiateV`
  (Typing.lean:1366–1424) and `Ty.raiseTy`/`raiseTy_eq_substAt_of_single` (Scheme.lean, `ddaf2e35`) —
  built for the functorial statement; `hasType_strictify` likely does **not** need `raiseCtx` at all
  (Γ fixed), which is precisely why it dodges the G13 obstruction.

## Tree state at stop

- HEAD unchanged at `e1e7a742`. **No commit this session** (no per-file-green increment produced;
  Soundness.lean deliberately untouched to honor the no-red-commit rule). Working tree:
  `Eyg/Types/Soundness.lean` still the pre-existing uncommitted 53-line partial migration (untouched),
  plus this note + the plan update. Untracked `.claude/`.
- `grep -rn sorry Eyg/Types/*.lean`: none. Whole-project `lake build` still fails only on Soundness.lean
  (its migration is incomplete: `mStateWf_E` must expose the `HasTypeRT hty` witness `MStateWf.E` now
  carries, and the whole file must be re-threaded to level-tagged + `genAtV`/`instantiateV` + RT). Caveat
  5 OPEN.

## Recommended next step (with LSP)

Build `StrictSub` + `hasType_strictify` (judgment-fixed existence) by structural recursion on `h`,
picking fresh gen levels via `exists_levelsBelow`; derive `NoGenAt lvl hdefn` by proof irrelevance from
`StrictSub` on the strictified same-judgment derivation. Concentrate first on the two-same-level-let_poly
/ escaping-var arm — if a bottom-up fresh-level assignment separates them cleanly (as G8's
re-instantiation argument suggests), the whole `NoGenAt lvl` crux collapses and the raise/relabel
functorial machinery (and its two-modes conflict) is never needed. Then discharge `hlvl0` (enter at
ambient `≥ 1`) and `hΓpa` (`polyAboveFV_of_ctxWfV`), wire the corrected
`genAtV_closure_ready_value_node hlvl0 hng hΓpa hcw henv args hargs` call, and grind the residual
Soundness.lean migration (starting with `mStateWf_E` exposing `HasTypeRT hty`).
