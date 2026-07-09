---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phases 4-5 "Session A": promoted the level-native judgment to be the real `HasType`/`HasTypeV`/`EnvWf`, re-greened every non-Soundness file. DELIBERATE, AUTHORIZED exception to the green-at-every-commit rule — `Soundness.lean` intentionally left RED, deferred to Session B (Phase 6).
status: LANDED (Soundness red by design). All 7 target files + CexEffectfulFix + LevelTagSpike build clean per-file; only `Soundness.lean` fails to compile (mechanical arity/shape breakage, characterized below). No `sorry`, no new axioms.
kind: progress
component: lean (Scheme, Typing, Generation, Substitution, Generalization, Runtime, Machine; prototype files deleted)
---

# G1 Phases 4-5 (Session A): `HasType` is now level-native; Soundness deferred

## DELIBERATE, TEMPORARY exception to the plan's normal rule

Every prior session required a fully green whole-project `lake build` (including `Soundness.lean`)
before any commit. **This commit is a pre-authorized exception.** The change (making `HasType`
level-parameterized) changes the arity/shape of the core judgment, which breaks `Soundness.lean`
(4278 lines, Phase 6) wholesale — and `lakefile.toml`'s `globs = ["Eyg.*"]` builds `Soundness` as part
of the default target, so there is **no green-except-Soundness committable state** any other way for a
change of this scope. The commit is therefore explicitly **NOT green**; it is a coherent worktree
checkpoint with every file *except* `Soundness.lean` building clean per-file. Session B (Phase 6) must
restore full green before its own commit.

## What was promoted (Phases 4-5)

The level-native judgment prototyped additively in `TypingAtV.lean`/`RuntimeAtV.lean` (Phase 3b) is now
**the real judgment**:

- **`HasType`** (`Typing.lean`) is now `HasType (lvl : Nat) : Ctx → Tree.Node m → Ty → Ty → Prop`
  (was un-indexed). `let_poly` generalizes at **exactly `lvl`** via `Scheme.genAtV lvl` / `CtxWfV lvl`,
  types its body at `lvl + 1`, and carries **no `noLambdaLet`** (nested `Let`-binds-`Lambda` accepted).
  `lam`/`let_` store an explicit sublevel `lvl'` with `lvl ≤ lvl'` + `∀ l ∈ argTy.levels, l < lvl'`.
  `var`/`builtin` instantiate via `Scheme.instantiateV`. The old magnitude `HasType` is deleted.
- **`hasType_subst`** (`Typing.lean`) is the instantiation-direction lemma (ex-`hasTypeAtV_substAt`):
  re-type under an outer `substAt ℓ σ` (`ℓ ≠ 0`, `ℓ < lvl`, `σ` levels `≤ ℓ`, `PolyAbove ℓ Γ`), with a
  non-vacuous `let_poly` arm for arbitrarily deep nesting. `genAtV_instantiate_lam_ready` (term-level
  readiness keystone) is likewise in `Typing.lean`.
- **`HasTypeV`/`EnvWf`** (`Runtime.lean`) keep their **arities** — the key blast-radius reduction: the
  ambient level is an **existential field** of `closure` (and of `StackSegWf.assign`/`arg`,
  `StackWf.assign`/`arg`), NOT an index. So the ~256-site "HasTypeV → HasTypeVAt" migration the Phase-4
  scoping note projected collapsed to: (a) `HasTypeV.closure` now stores the lambda's `lvl'`+freshness
  +body derivation at the level-native `HasType` (arrow components kept so canonical forms are
  unchanged); (b) `EnvWf.cons` readiness is `∀ args, (∀ t∈args, ∀ l∈t.levels, l ≤ s.level) →
  HasTypeV v (s.instantiateV args)` (conditional, level-native); (c) a handful of positional `@`
  patterns / inversion tuples gained one field. Every canonical-forms / conv / stackSeg lemma is
  otherwise untouched.
- **Readiness keystone** `genAtV_closure_ready_value` ported into `Substitution.lean` (real
  `HasTypeV`/`EnvWf`), discharging the `EnvWf.cons` obligation with no `noLambdaLet`. The magnitude
  `generalizes_closure_ready`/`genAt_closure_ready`/`closure_typed_of_lambda_subst`/`hasType_substLM_letPoly`
  are removed (superseded) — noted inline in `Generalization.lean`/`Substitution.lean`.
- **Infrastructure relocated upstream** (prerequisite, committed separately as the fully-green
  `e8a99f74`): `Scheme.ext'` + the `Ty`/`Scheme`/`Builtins`-level `substAt`/`genAtV` commutation lemmas
  moved from `TypingAtV.lean` into `Scheme.lean`. `CtxWfV`/`substCtxAt`/`PolyAbove` + helpers moved into
  `Typing.lean`; `Ty.levels_tyEquiv` added. Prototype files `TypingAt.lean`/`TypingAtV.lean`/
  `RuntimeAtV.lean` **deleted** (content promoted) and dropped from `Eyg.lean`.

## Green per-file (verified `lake build Eyg.Types.<F>`, exit 0, 0 errors)

`Scheme`, `Typing`, `Generation`, `Substitution`, `Generalization`, `Runtime`, `Machine`,
`CexEffectfulFix`, `LevelTagSpike`. No `sorry` in any. Axioms of the promoted keystones
(`hasType_subst`, `genAtV_closure_ready_value`, `genAtV_instantiate_lam_ready`) =
`[propext, Classical.choice, Quot.sound]`; no custom axioms introduced.

## Soundness.lean — the remaining work (Session B / Phase 6)

`lake build` fails ONLY in `Soundness.lean` (101 errors reported before the error-cap; more exist past
the cap). All mechanical, no open mathematics. Error-kind histogram:

- 36  Application type mismatch (HasType/inversion-tuple shapes changed: `lam`/`let_` gained
      `lvl'`/`hle`/`hfv`; `let_poly` dropped `n`/`noLambdaLet`, uses `genAtV`/`CtxWfV`; `inv_lambda`
      now returns `⟨lvl', argTy, εb, retTy, hle, hfv, hbody, heq⟩`; `inv_let` returns level-native
      mono/poly tuples; `HasTypeV.closure`/`EnvWf.cons`/`StackWf(Seg).assign|arg` gained a `lvl` field).
- 30  Function expected at (uses of `HasType Γ e τ ε` now need the extra `lvl` argument:
      `HasType lvl Γ e τ ε`).
- 13  Unknown identifier (removed: `generalizes_closure_ready`, `genAt_closure_ready`,
      `hasType_substLM_letPoly`, and `HasType.let_poly`'s old `n`/`noLambdaLet` fields / `inv_let`'s old
      `n` witness).
- 11  Type mismatch; 6  "not an inductive datatype" (`cases`/`induction` on old-shape derivations);
      2  simplification type mismatch; 1  invalid equality proof; 1  invalid field projection.

**Session B plan (Phase 6):** thread `lvl` through the 19 inversion-lemma consumers and the case
matches; re-prove the two `let_poly` preservation cases (`~:242`, `~:2967`) via the ported
`genAtV_closure_ready_value` (feeding it the `lam`-component derivation + `CtxWfV`/`PolyAbove`, obtained
from the new `inv_let` poly branch); adjust the `soundness`/`soundness_evalR` *statements* to type at a
nonzero ambient level (the keystone needs `ℓ ≠ 0`; top-level generalization must live at level `≥ 1` —
this is why the new sanity examples in `Typing`/`Generalization` type at ambient level `1`). Permitted
to adjust statements; axiom set must return to `[propext, Classical.choice, Quot.sound]`. Only commit
once fully green.

## Definition-of-done for Session A (met)

All non-Soundness files green per-file; no `sorry`; no new axioms; prototype files retired. The commit
message says prominently "Soundness.lean intentionally left red". This note is the authorization record.
