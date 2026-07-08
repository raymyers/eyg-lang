---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 3a DONE, Phase 3b sharpened
status: Phase 3a DONE and committed; Phase 3b scoped with a newly-found subtlety
kind: progress
component: lean (Eyg/Types/{Ty,Scheme,Generalization,Soundness}.lean)
---

# G1 Phase 3a done: real `Ty.var` carries a level tag. Phase 3b scoped precisely.

Follow-up to `progress/2026-07-08-G1-level-tag-spike-GO.md` (the isolated spike that
cleared the go/no-go checkpoint). This session ported the level tag onto the **real**
`Ty` datatype (not the toy `Ty2` model) and found a genuine additional subtlety in
`Scheme.instantiate`'s commutation with ambient substitution — recorded below so a
continuation doesn't have to rediscover it.

## Phase 3a — DONE, committed (`8108591a`)

`Ty.var (idx : Nat)` → `Ty.var (level idx : Nat)`, with every pre-existing use pinned
to level `0` (the "collapse convention"). This is a **pure representation change**:

- `Ty.subst`/`freeVars`/`Scheme.genAt`/`instantiate`/`substScheme`/`genArity`/
  `reindexGen` in `Scheme.lean`: unchanged *logic*, just re-typed against the 2-arg
  constructor (mechanical `.var i` → `.var 0 i` transliteration, done via a targeted
  `perl`/`sed` pass with `HasType.var` carefully excluded from the substitution).
  A handful of proofs needed a real (not just textual) fix: `subst`/`freeVars`
  pattern matches gained a `.var (l+1) _` fallback case (since the 2-arg constructor
  is no longer exhaustively covered by a single `.var 0 _` arm), and the
  corresponding `rfl`-based proofs (`subst_subst`, `subst_id`, `subst_eq_of_fixes_free`,
  `fixes_free_of_subst_eq`, `subst_congr_free`, `mem_freeVars_subst`) needed a
  `cases`/`by_cases` split on the level that wasn't needed when there was only one
  level.
- `Generalization.lean`, `Soundness.lean`'s hardcoded `fix`-scheme literals
  (`q 0`/`q 2`/`q 3`, `.var 0`/`.var 2`/`.var 3`): same mechanical transliteration,
  zero errors after the pass (Generalization.lean built with **zero** manual fixes
  beyond the mechanical substitution — only Scheme.lean's *definitions* needed real
  proof changes, since only they pattern-match `Ty` structurally).
- `Typing.lean`, `Machine.lean`, `Runtime.lean`, `Substitution.lean`, `Generation.lean`
  needed **zero changes** — confirmed by full rebuild. They only ever reference
  `Scheme`/`Ty` genuinely opaquely (via `.mono`, generic types like `.integer`, or
  the `HasType.var` *judgment constructor*, which is unrelated to `Ty.var`) and never
  construct/pattern-match a literal `Ty.var`.

**Verified:** `lake build` 1774 jobs, `lake exe spec` 104/104, and (checked via a
scratch file importing `Eyg.Types.Soundness` directly — the root `Eyg.lean` doesn't
transitively import `Soundness.lean`) `#print axioms Eyg.Types.soundness` /
`soundness_evalR` unchanged: `[propext, Classical.choice, Quot.sound]`, no `sorry`.

**What Phase 3a does *not* yet do:** `Scheme` still has no `level` field (still
`{arity, body}`); `genAt`/`instantiate`/`substScheme` still use the *old*
magnitude-based `genArity`/`reindexGen` machinery, just confined to level `0`. No
nested generalization is possible yet — this phase is representation-only, a clean
platform for Phase 3b, not new capability.

## Phase 3b — attempted, found a real subtlety, not landed this session

Attempted to give `Scheme` an actual `level` field and make `genAt`/`instantiate`/
`substScheme` level-native (no reindexing — the design the Phase 1–2 spike
validated). Hit two design points not visible from the toy spike, worth recording
precisely:

### 1. `hasType_subst` itself must become level-parameterized

The spike's `substScheme_genAt` (pushing an ambient substitution *into a stored
scheme*, unconditionally, for `ℓ ≠ ℓ'`) is real and does generalize cleanly to the
real `Ty`. But `hasType_subst`'s only real call site,
`closure_typed_of_lambda_subst` (`Substitution.lean:148`), needs to **open a
let_poly's *own* scheme** — i.e. substitute *at that scheme's level*, not at level
`0`. `hasType_subst`'s statement (`HasType Γ e τ ε → HasType (substCtx σ Γ) e
(Ty.subst σ τ) (Ty.subst σ ε)`) is hardcoded to `Ty.subst` (= `substAt 0`)
throughout its entire induction — every rule case, not just `let_poly`. Making this
work requires threading an explicit level parameter `ℓ` through the whole theorem
(`Ty.substAt ℓ` in place of `Ty.subst` everywhere), which is a larger, non-local
edit to `Substitution.lean` — not a `let_poly`-arm-only change.

### 2. `subst_instantiate`/`subst_instantiate'` need a real side-condition (not "free" the way `substScheme_genAt` is)

This is the sharper, previously-undiscovered finding. There are two *different*
commutation facts in play, and only one of them is unconditional:

- **`substScheme`-into-a-stored-scheme** (push ambient `σ` at level `ℓ` into a
  *stored, uninstantiated* `Scheme` of a *different* level `ℓ'`): unconditional,
  `simp only [Scheme.substScheme, Scheme.genAt]` in the spike. This is what the
  `let_poly` arm's `CtxWf`-threading step needs (carrying a nested scheme along
  through the substitution without opening it).

- **`subst_instantiate`** (commute an ambient substitution with *instantiating* a
  scheme — i.e. `Ty.subst σ (s.instantiate args) = (substScheme σ s).instantiate
  (args.map (Ty.subst σ))`, needed by the `var`/`builtin` rule arms of
  `hasType_subst`): **genuinely conditional**. Worked through by hand (structural
  induction on the commutation `substAt 0 σ (substAt ℓ τ t) = substAt ℓ τ'
  (substAt 0 σ t)` for `ℓ ≠ 0`, `τ' := fun i => substAt 0 σ (τ i)`): the `var 0 i`
  leaf case needs `substAt ℓ τ' (σ i) = σ i`, i.e. **`σ`'s outputs must not contain
  a level-`ℓ` leaf** — false in general (σ is an arbitrary caller-supplied ambient
  substitution; nothing stops `σ i` from happening to mention a level that some
  *other*, unrelated nested scheme in the term also uses). This is a real
  side-condition, analogous in spirit to the old `Ty.LevelMap` (which similarly
  restricted the pre-level-tag `subst_instantiate`) — just a different, hopefully
  simpler shape: "`σ`'s range avoids whatever levels the term's nested schemes use,"
  which should be satisfiable by a level-freshness/monotonicity discipline (fresh
  levels are always chosen *deeper* than anything already in scope, so a
  *well-formed* derivation's `σ` — built from concrete/ground types or references to
  *already-established*, lower levels — never collides) but needs to be **stated and
  threaded**, not assumed away.

### Why this session didn't push through it

Mid-edit, discovering point 1 while already deep in a `Scheme.lean` rewrite led to
an attempted patch with `sorry`s and a nonsensical placeholder case (mixing up the
toy spike's `Ty2.fn` naming with the real `Ty.fun`) — caught before committing,
reverted via a clean mechanical re-derivation (Phase 3a, described above) rather
than compounding the mistake. Point 2 was only discovered *afterward*, working
through what Phase 3b's `subst_instantiate` proof obligation would actually require
once `Scheme` gains a real level field. Better to stop and record both findings
precisely than attempt a second live rewrite under time pressure.

## Continuation spec for Phase 3b (concrete, so a future session can start immediately)

1. Add `level : Nat` to `Scheme` (alongside the existing `arity`, kept for
   informational parity — see below).
2. Redefine `genAt (ℓ : Nat) (d : Ty) : Scheme := ⟨(d.levels.filter (· = ℓ)).length, ℓ, d⟩`
   — no reindexing (`d.levels : List Nat`, a new level-aware primitive alongside the
   existing level-`0`-only `freeVars`, both already sketched in the abandoned
   Phase-3b attempt and easy to re-derive).
3. Redefine `instantiate s args := Ty.substAt s.level (fun i => args.getD i (.var
   s.level i)) s.body` — `args.getD` handles under/over-application unconditionally,
   no `arity`-bound case split needed (this *simplifies* on the old design).
4. Redefine `substScheme σ s := ⟨s.arity, s.level, Ty.subst σ s.body⟩` (σ always
   ambient/level-`0`).
5. Prove `substScheme_genAt`-shape commutation for the *real* `Ty` (should port
   near-verbatim from `LevelTagSpike.lean`, now unconditional in `ℓ ≠ ℓ'` — but audit
   whether the *unconditional* claim still holds once `Ty` has 12 formers instead of
   the spike's 2, particularly around `promise`/row formers; expect yes, since none
   of them touch `var` specially, but verify).
6. **The real work:** level-parameterize `hasType_subst` (`Ty.substAt ℓ` throughout,
   not just in a `let_poly` arm) and give `subst_instantiate`/`subst_instantiate'` the
   side-condition from finding 2 above — design its exact shape (candidate: `∀ i,
   (σ i).levels ⊆ {levels already in scope below the current threading level}`,
   or simpler, a monotonicity/freshness invariant threaded like the old
   `CtxWf`/`LevelMap` was) and re-derive `hasType_subst`'s `var`/`builtin` cases
   under it.
7. Only after 1–6 land green: re-thread `Typing.lean`'s `let_poly` rule (drop
   `noLambdaLet`), re-green `Machine.lean`/`Runtime.lean`, then `Soundness.lean`
   (Phases 4–6 of the original plan, unchanged in shape).

## Current state

Tree is green at the Phase 3a commit (`8108591a`): `lake build` 1774, spec 104/104,
axioms unchanged. No `sorry` anywhere in the touched files. This note plus the plan
update are the only changes on top of that commit.
