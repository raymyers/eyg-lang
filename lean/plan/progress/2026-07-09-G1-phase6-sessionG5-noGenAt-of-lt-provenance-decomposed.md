---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G5". NoGenAt-provenance question DECOMPOSED and the
  previous session's leading hypothesis (strengthen HasTypeRT with NoGenAt lvl hdefn) REFUTED with a
  concrete well-typed witness. One green additive commit: noGenAt_of_lt (level-monotone NoGenAt).
status: PARTIAL. One green additive commit (8339200d, Typing.lean). Soundness.lean left exactly as
  found (uncommitted partial migration, untouched — only Read). Caveat 5 OPEN. Full green NOT reached
  and confirmed NOT blind-reachable: the residual let_poly-provenance corner needs a genuine new
  runtime invariant / level-normalization theorem, not mechanical grind.
kind: progress
component: lean (Eyg/Types/Typing.lean)
---

# G1 Phase 6 (Session G5): NoGenAt provenance decomposed; same-lvl HasTypeRT route refuted

No LSP/MCP this session (canary failed: Read/Grep/Edit + `lake build`/`lake env lean` only).

## The task's central question, resolved on the merits

The `let_poly` preservation site (`Soundness.lean:243`) calls
`genAtV_closure_ready_value_node hlvl0 hdefn hΓpa hcw henv args hargs` and needs `NoGenAt lvl hdefn`
where `hdefn : HasType lvl Γ ⟨.Lambda lx lbody, la⟩ defnTy ε` is at **exactly** the let_poly's ambient
level `lvl` (confirmed: `lvl` comes straight from `mStateWf_E`, and we generalize `genAtV lvl defnTy`).
Inside the wrapper, `inv_lambda_noGenAt` reduces this to `NoGenAt lvl hbody`, where
`hbody : HasType lvl' ((x,.mono argTy)::Γ) lbody retTy εb` with `lvl ≤ lvl'`.

### Route A — "strengthen HasTypeRT to carry `NoGenAt lvl hdefn`" (prev session's lead): REFUTED
`NoGenAt lvl hdefn` is **not** universally true for well-typed runtime let_poly controls, so bundling
it into `HasTypeRT.let_poly` would newly *reject* legitimate programs — narrowing soundness coverage.
Witness (a valid `HasType` derivation): a value-restricted defn-lambda whose body is at sublevel
`lvl' = lvl` and which contains **both** a level-`lvl` instantiation arg (making `defnTy` mention `lvl`,
`arity ≠ 0`) **and** an inner `let_poly` generalizing at exactly `lvl` (e.g.
`\x. pair (g[a := .var lvl 0]) (let h = \y.y in h)` with `g` a lower let-bound polymorphic binding).
For this `hbody`, `NoGenAt lvl` is false (its inner `let_poly` arm needs `lvl ≠ lvl`). Crucially the
CURRENT (un-strengthened) `HasTypeRT` still *accepts* this program — `HasTypeRT.let_poly`/`.lam` do
**not** recurse into the defn-lambda body — so adding the field is a strict narrowing, not free.
NB the Phase-7 *target* program `let f = \x.(let g=\y.y in g x) in ...` is **not** a counterexample:
there `defnTy = argTy → argTy` is ground (`arity 0`), so the wrapper never needs `NoGenAt` for it (see
the arity-0 branch below). The counterexample is the strictly harder "level-`lvl` var injected into the
lambda body by an internal instantiation" shape.

### The correct decomposition of the wrapper's `NoGenAt lvl hbody` need
1. **`arity 0`** (`lvl ∉ defnTy.levels`): `(genAtV lvl defnTy).instantiateV args = defnTy`, so the
   closure typing is `closure_typed_of_lambda henv h` directly — **no `NoGenAt` at all**. This covers
   every nested-generalizable-let whose generalized type is ground at `lvl` (incl. the Phase-7 target).
2. **`lvl' > lvl`** (body sublevel strictly above the gen level): `NoGenAt lvl hbody` holds **for free**
   by level-monotonicity — the new `noGenAt_of_lt` lemma. No external witness.
3. **Residual — `arity ≠ 0 ∧ lvl' = lvl`**: genuinely needs a real `NoGenAt lvl hbody`. Two sub-shapes:
   - benign (`defnPerf`, `\x. perform "op" x`: `arity ≠ 0` via a generalizable effect tail `μ` at
     level 1, `lvl'=lvl=1`, body has **no** `let_poly`): `NoGenAt` holds and IS derivable — the existing
     wrapper already handles it *given* the witness.
   - pathological (the Route-A counterexample): `NoGenAt lvl hbody` is **false**, and no combination of
     the wrapper's other hypotheses (`CtxWfV`/`PolyAboveFV`/`EnvWf`/`hargs`) recovers it. This is the
     true open frontier.

## Landed + committed — `noGenAt_of_lt` (commit `8339200d`, Typing.lean)
```
theorem noGenAt_of_lt {ℓ : Nat} :
    ∀ {lvl Γ e τ ε} (h : HasType lvl Γ e τ ε), ℓ < lvl → NoGenAt ℓ h
```
Clean 21-arm induction on `h` (ambient level only increases on descent: `lam`/`let_` recurse into the
`lvl' ≥ lvl` body, `let_poly` bumps to `lvl+1` and supplies its own `lvl ≠ ℓ` from `ℓ < lvl`, `app`/
`conv` keep the level). Non-narrowing, per-file green, axioms `[propext]` only, no `sorry`. This is the
exact tool that discharges wrapper-need case 2 with no external witness; any full resolution of the
residual builds on it.

## Why full Soundness green is NOT blind-reachable (independently confirmed, not "ran out of time")
- The `let_poly` preservation case cannot be made to compile: the wrapper's `hng : NoGenAt lvl hdefn`
  is *unsatisfiable from the site's data* in the pathological residual (case 3b). It requires either
  (a) a **level-normalization theorem** — every `HasType` derivation is convertible to one whose nested
  `let_poly` use strictly increasing levels (so the residual collapses into case 2, `lvl' > lvl`),
  closing it WITHOUT narrowing soundness — or (b) a **deeper runtime invariant** than `HasTypeRT`
  bounding instantiation-arg levels *inside* value-restricted lambda bodies (but `HasTypeRT` must keep
  stopping at lambda bodies to admit `hbody_ref`, so this is a genuinely separate predicate carried
  only for let_poly defns, and it re-narrows coverage unless paired with normalization). Both are real
  metatheorems, multi-session, and want live LSP.
- Independently, the whole **B-engine** (`Soundness.lean` ~2694–3862: `StackWfVB`/`StackWfEB`/
  `reduceEvalR`) is still on the **old non-level-tagged `HasType`** (`HasType Γ e τ ε`, no `lvl`,
  2-tuple `inv_let`), i.e. a large mechanical migration untouched by the level-tag work — not reachable
  the same session as the A-engine.
- `soundness_evalR` (`:3984`) still carries the OLD `hty : HasType [] prog τ ε` statement and will need
  an added `HasTypeRT hty` premise (already accepted by the plan via `mStateWf_initial`'s `hrt`) plus a
  nonzero ambient level — statement-affecting plumbing that must land together with the green build.

## Recommended next-session order (WITH LSP ideally)
1. **Decide the residual (3b) policy** — this is a design call for the plan owner, not a blind edit:
   pursue the level-normalization theorem (preferred; closes 3b with zero soundness narrowing), or
   accept a let_poly-defn `NoGenAt` runtime invariant (narrows coverage; must be justified against the
   soundness statement). Prototype the chosen route's `let_poly` discharge FIRST, in isolation.
2. Restructure `genAtV_closure_ready_value_node` on `by_cases (genAtV lvl defnTy).arity = 0` →
   `closure_typed_of_lambda`; else `by_cases lvl' = lvl` → `noGenAt_of_lt` for the `<` side; only the
   residual keeps `hng`. This shrinks the caller's obligation to exactly case 3.
3. Then the mechanical grind: migrate `mStateWf_E`/`soundness_evalR` to level-tagged `HasType` + thread
   `hrt`, set ambient `lvl ≥ 1`, port the whole B-engine off old `HasType`. Only commit Soundness fully
   green (no red-commit exception).

## Tree state at stop
- HEAD `8339200d` (one commit above `b6749080`). Per-file green: Typing, Runtime, Machine,
  Substitution, Scheme, Generation, Generalization.
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6 partial migration, **untouched**
  this session — only Read), uncommitted. Untracked `.claude/`, this note + plan update.
- `grep sorry Eyg/Types/*.lean`: none (committed HEAD *and* working tree). Whole-project `lake build`
  still fails only on `Soundness.lean`. Caveat 5 remains OPEN.
