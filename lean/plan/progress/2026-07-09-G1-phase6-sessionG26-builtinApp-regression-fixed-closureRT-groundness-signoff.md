---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G26". Cleared the `builtinApp_arity2`/`instantiateV`
  mechanical regression (A+B) and migrated the headline `soundness_evalR_*` wrappers, bringing the
  A-engine of `Soundness.lean` to EXACTLY the two closure-apply RT-gap sites (874-877, 1036-1039) with
  no other A-engine errors. Definitively characterized the closure-body-RT gap as an env/context
  GROUNDNESS invariant threading — beyond the G22-G23 scalar-field pattern — and signed it off as the
  genuine open design question. B-engine left as a clean un-migrated block.
status: PARTIAL (durable working-tree progress; no new commit — all changes inside uncommittable-until-
  green `Soundness.lean`). `Soundness.lean` uncommitted-red but STRICTLY BETTER than G25 left it:
  A-engine errors ~10 → 2 (only the closure-RT crux), builtin regression gone, wrappers migrated.
  No `sorry` anywhere, every step. Caveat 5 OPEN.
kind: progress
component: lean
---

# G1 Phase 6 (Session G26): builtinApp/instantiateV regression cleared; closure-RT gap = groundness threading (sign-off)

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep/Edit + `lake env
lean -DmaxErrors=N`. HEAD `471de13a`. `grep -rn sorry Eyg/Types/*.lean` empty throughout, every step.
All edits in the (already-uncommitted-red) `Soundness.lean` working tree, which persists across sessions;
no git commit (Soundness is not committable until fully green — no red-commit exception).

## Landed in the working tree (durable, verified error-reducing)

1. **`builtinApp_arity2`/`instantiateV` regression (G23 leftover) — FIXED (A+B).** The
   `HasTypeV.partialBuiltin` constructor now demands `BuiltinPartialWf (s.instantiateV args) …`, but
   `builtinApp_arity2`/`_B`'s `hbase` premise + internal `rw [hbase]` (Soundness ~1938/~3796) and the
   `fix`-creation `hB`/`rw [hB] at hpw` (~2044/~3858) were still typed at `s.instantiate`. Changed the
   `hbase` premise type to `s.instantiateV sargs = …`, the internal `hB` to `Scheme.instantiateV`
   (`simp [Scheme.instantiateV, Ty.substAt]`), and the 16 mono caller `hbase` proofs
   `by simp [Scheme.instantiate_mono, Ty.pure2]` → `by simp [Scheme.instantiateV_mono, Ty.pure2]` +
   the 2 `equal` caller proofs → `simp [Scheme.instantiateV, Ty.substAt, …]`. The `simpa … using hpw`
   caller lines were untouched (they close by defeq — with a concrete literal scheme `s.instantiateV`
   reduces). Verified: the ~1938/~2050 errors are gone.

2. **Headline `soundness_evalR_*` wrappers migrated.** `mStateWf_initial` now takes
   `(1 ≤ lvl) (HasType lvl …) (HasTypeRT h)`; `soundness_evalR_value`/`soundness_evalR_noBadCrash` still
   passed the pre-migration `HasType [] prog τ ε` (`[]` where a `Nat` `lvl` is now expected). Added
   `{lvl}`, `(hlvl : 1 ≤ lvl)`, `(hrt : HasTypeRT hty)` and re-threaded into `mStateWf_initial`. (This is
   the same additive level-tagging exposure the whole G1 migration performs; not a soundness weakening.)

**Net A-engine state:** with (1)+(2), `lake env lean -DmaxErrors=500 Soundness.lean` shows the ENTIRE
A-engine (< line 2444) green EXCEPT the two closure-apply sites `preservation_V`/`progress` Apply-frame
closure case (874-877 and its mirror 1036-1039). So the first engine is complete modulo the one genuine
gap — matching the "first engine complete except closure-body-RT" claim. Total file errors ~95, of which
~89 are the un-migrated B-engine (see below); only 2 A-engine (well, 2 sites × ~3 cascade lines each).

## The closure-apply RT gap — DEFINITIVE characterization (sign-off)

At the Apply-frame closure case (`preservation_V`, Soundness ~868): `cases hf with | closure …` yields
`hbody : HasType lvl' ((x,.mono argTy) :: Γ) body retTy εb` (the migrated 5-field `HasTypeV.closure`;
the site's `cases` binder count + refine shape are also un-migrated, but those are trivial once the RT
field exists). The produced `.E`-state (`MStateWf.E`, Machine.lean:412) REQUIRES `HasTypeRT` of that
body derivation. `hasTypeRT_subst` (LANDED, G25) can PRODUCE it — from `RTSubstReady ℓ hbody` + a ground
`σ` — but **neither is available at the site, and `HasTypeRT hbody` is genuinely NOT derivable from
anything the closure currently carries**:

- `HasTypeV.closure` stores only `hbody` (raw), not any RT witness; and it CANNOT store `HasTypeRT hbody`,
  because at the Lambda-creation site (Soundness ~211) all that is available is the lambda-NODE RT
  (`hasTypeRT_lambda`/`HasTypeRT.lam`), which carries **no** body premise — deliberately: a legitimately
  typed body can be non-RT (`\w. a w` with `a : ∀α.α→α` instantiated at `[.var 2 0]`, arg level 2 ∉
  {0, a-scheme-level}). Strengthening `HasTypeRT.lam` to recurse into the body would reject that
  legitimate referencing program (make the initial program non-RT). So body-RT is un-storable.
- Therefore body-RT must be RE-ESTABLISHED at apply time by grounding. But the non-RT arg levels are the
  body's references to **outer (captured, level < lvl') poly bindings** — NOT the closure's own level
  `lvl'` and NOT the mono argument. To ground them, `σ` must come from the **environment/context**
  (which at runtime realizes those outer bindings with concrete, ground schemes). `MStateWf.V`/
  `HasTypeV.closure`/`EnvWf`/`StackWf*` carry **no** such groundness today.
- **New subtlety surfaced this session (extends G24/G25):** a single body can reference **several**
  distinct outer generalization levels, so a single-`ℓ` `hasTypeRT_subst` does not suffice in general —
  the grounding is potentially **iterated** (one `hasTypeRT_subst` pass per outstanding outer level), or
  the invariant must package a simultaneous multi-level ground substitution. Also, for the running
  config's exposed types (retTy/εb/argTy/Γ) to be preserved, each grounding `ℓ` must be **outside**
  those exposed level sets — an additional constraint the invariant must guarantee.

**Conclusion (the sign-off):** closing gap 1 requires threading an **env/context groundness (poly-below-
lvl') invariant** through `HasTypeV.closure` + `EnvWf`/`MStateWf`/`StackWf*` (both engines) such that a
closure's stored body is provably `RTSubstReady` at its outstanding outer levels AND those levels are
ground-substitutable from the captured environment. This is a **structural readiness predicate on
contexts/environments** whose CONSTRUCTION at the plain-Lambda creation site is non-obvious — it is NOT
the bounded scalar-field addition of G22-G23 (`1 ≤ lvl`/`CtxPolyBd`/`hpoly`), which were dischargeable
locally at every site. The substitution engine (`RTSubstReady` + `hasTypeRT_subst`, G25) is the
downstream consumer and is ready; the missing piece is the upstream groundness invariant + an
RT-producing keystone variant + the (potentially iterated) wiring. Recommend the next session design the
env-groundness predicate explicitly (candidate: an inductive `CtxGround ℓ Γ` / `EnvGround` asserting
every Γ binding is mono-or-generalized-at-a-ground-level, threaded into `EnvWf.cons` and
`HasTypeV.closure`) BEFORE touching the four apply sites.

## B-engine: left as a clean un-migrated block (deliberate)

The B-engine (`StackWfB`/`StackWfVB`/`StackWfEB`/`MStateWfB` and all their proofs, Soundness ~2452-end,
the T7 base-row row-evolution groundwork) still uses the PRE-migration `HasType Γ e τ ε` (no `lvl`) and
`Scheme.instantiate` (not `instantiateV`). Its ~89 errors cascade from the four root `def`/`inductive`s
failing to elaborate (`HasType` applied at the wrong arity ⇒ "unknown identifier StackWfB" / "function
expected" downstream). Migrating it means re-doing the entire `lvl`+`HasTypeRT`+`instantiateV` threading
the A-engine received (across ~1500 lines) AND it hits the SAME closure-apply RT gap in its
`preservation_VB/EB` mirrors — so it cannot reach green independently either. Deliberately NOT
partially migrated this session: a half-threaded B-engine (root inductives changed, downstream proofs
not) would be MORE broken and harder to resume than the current clean, well-characterized block. The
mechanical mirror is straightforward once the closure-RT groundness invariant (above) is designed, since
that is the one non-mechanical dependency both engines share.

## Tree state at stop

- No commit (all work inside uncommittable-red `Soundness.lean`; the working tree persists to next
  session, as it has since G23).
- `Soundness.lean`: uncommitted, red, but STRICTLY BETTER than G25 — A-engine at 2 crux sites (was ~10),
  builtin regression eliminated, wrappers migrated, no `sorry`, no A-engine regressions.
- `plan/eyg-g1-level-tagged-ty.md`: Session G26 entry appended under Phase 6. This note added.
- Caveat 5 OPEN (poly-let preservation DISCHARGED; closure-body-RT: substitution infra COMPLETE (G25),
  env-groundness invariant + wiring OPEN and now precisely scoped; B-engine mechanical mirror pending).
