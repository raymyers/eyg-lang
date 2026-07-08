---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 4 scoping: dropping `noLambdaLet` from the real `HasType.let_poly` is confirmed inseparable from Phases 5-6 (the level-native migration of `HasTypeV`/`EnvWf` and the Soundness re-green). No source edits made; tree held green at `f33550e7`.
status: SCOPED, NOT LANDED — grounded blast-radius measurement + go/no-go analysis; tree pristine (zero source edits), still green at f33550e7. Honest stop per the plan's stated philosophy (cf. 2026-06-19-G1-foundational-wall-confirmed-no-additive-slice.md).
kind: progress
component: lean (scoping only; no files changed)
---

# G1 Phase 4: scoping the `noLambdaLet` drop — confirmed a 2-3 session migration, not a one-line relaxation

Phase 4's deliverable is "re-thread `Typing.lean`: drop the side-channel `n`/`CtxWf`; `let_poly`
uses the tag directly; drop `noLambdaLet` from the rule." This session **measured the exact blast
radius on the current tree** and reached a firm go/no-go conclusion. **No source files were edited**
— the tree remains pristine at `f33550e7` (`lake build` 1777, spec 104/104, axioms
`[propext, Classical.choice, Quot.sound]`). This note records exactly why the change is not
one-session-landable without live LSP, with the precise site inventory a future session should
start from.

## The core finding: `noLambdaLet` is load-bearing for `let_poly` *preservation*, not just for typing

The constructor field `Tree.Node.noLambdaLet lbody` on `HasType.let_poly` (`Typing.lean:106`) is not a
dead threaded token. Tracing every consumer:

1. **`hasType_subst` (`Substitution.lean:62-63`) requires `noLambdaLet e` on the *whole term*.** Its
   `let_poly` arm (`:85-86`) is discharged **vacuously** — `noLambdaLet (Let (Lambda ..) body)` reduces
   to `False`, so `simp only [Tree.Node.noLambdaLet] at hnl` (the top-level hypothesis) closes it. The
   constructor's own `noLambdaLet` field is *unused* here.
2. **`closure_typed_of_lambda_subst` (`Substitution.lean:148-152`)** calls `hasType_subst σ h (…noLambdaLet…)`,
   so it inherits the whole-term `noLambdaLet` requirement.
3. **`generalizes_closure_ready` (`Generalization.lean:135-145`)** and **`genAt_closure_ready`
   (`Generalization.lean:294-301`)** both take `hnl : Tree.Node.noLambdaLet body` as a hypothesis and
   pass it to `closure_typed_of_lambda_subst`.
4. **The two `let_poly` preservation cases in `Soundness.lean` — `:242` (A-engine) and `:2967`
   (B-mirror) — literally call**
   `exact genAt_closure_ready (fun _ hf => ctxWf_fixed hcw hf) hnl henv hdefn args`,
   where `hnl` is the constructor's `noLambdaLet` field, obtained by destructuring the `let_poly`
   derivation via `inv_let` (`Soundness.lean:225-226`, `:2952`; tuple shape
   `⟨lx, lbody, la, defnTy, n, hdl, hdefn, hcw, hnl, hbody⟩`).

**Consequence:** dropping the `noLambdaLet` field makes those two preservation cases unprovable **with
the current magnitude machinery** — there is no `hnl` to feed `genAt_closure_ready`, and
`genAt_closure_ready` cannot be re-proved without `noLambdaLet` (it bottoms out in the whole-term
`hasType_subst` vacuity guard). This is exactly the mathematical wall the whole G1 plan diagnosed; it
is discharged only by the **level-native** readiness keystone `genAtV_closure_ready_value`
(`RuntimeAtV.lean`), proven this-week additively.

## Why the level-native keystone cannot be dropped in locally (the migration coupling)

`genAtV_closure_ready_value` concludes `HasTypeVAt lvl (Value.Closure …) τ`, whereas `Soundness.lean:242`
must supply the **`EnvWf.cons` readiness obligation**, whose type is fixed by `EnvWf`'s definition
(`Runtime.lean:211`) over `HasTypeV v (s.instantiate args)` — the *magnitude* value judgment. The two
conclusion types (`HasTypeVAt`/`instantiateV` vs. `HasTypeV`/`instantiate`) are not defeq and cannot be
bridged pointwise. Therefore using the level-native keystone at that one site forces:

- `EnvWf` → `EnvWfAt` (obligation stated over `HasTypeVAt s.level`/`Scheme.instantiateV`), and
- `HasTypeV` → `HasTypeVAt` **everywhere it flows through the soundness induction**.

`HasTypeVAt`/`EnvWfAt` already exist and are fully proven additively (`RuntimeAtV.lean`), but only for
the generalization-bearing value shapes (base literals + `closure`); the partial/continuation shapes
(`partialBuiltin`/`partialResume`/data) are the deliberately-omitted mechanical Phase-5 transliterations.

## Blast-radius inventory (measured on `f33550e7`)

| Site | Location | What changes | Mechanical? |
|---|---|---|---|
| `let_poly` constructor | `Typing.lean:103-108` | drop `noLambdaLet`; replace `n`/`CtxWf n` with the level tag (`genAtV lvl`/`CtxWfV lvl`) — needs `HasType` to *carry* `lvl` | design |
| `HasType` signature | `Typing.lean:70` | gains `lvl` (promote `HasTypeAt`) — `lam`/`let_` also change shape (stored `lvl'`, cf. `TypingAt.lean:72,83`) | design |
| `hasType_ctxConv` let_poly arm | `Typing.lean:236-239` | drop `hnl`; thread `lvl` | mechanical |
| `hasType_subst` | `Substitution.lean:62-86` | becomes level-parameterized (`hasTypeAt_subst` already exists in `TypingAt.lean`) | port |
| `closure_typed_of_lambda_subst` / `_of_lambda` | `Substitution.lean:137-152` | level-native readiness | port |
| `genAt_closure_ready` / `generalizes_closure_ready` | `Generalization.lean:135,294` | replaced by `genAtV_closure_ready_value` (exists) | port |
| Generalization let_poly/CtxWf | `Generalization.lean` (29 `let_poly`, 23 `CtxWf`, 8 `noLambdaLet`) | level-native `GeneralizesAtV` (exists) | port |
| `Runtime.lean` `HasTypeV`/`EnvWf` | `Runtime.lean:57,211` | → `HasTypeVAt`/`EnvWfAt` (exist for load-bearing shapes; partials need mechanical mirror) | port + Phase 5 |
| `Machine.lean` value typing | 2 `let_poly`, 8 HasTypeV matches | mechanical `lvl` thread | Phase 5 |
| `Soundness.lean` | 62 `HasType`, **256 `HasTypeV`**, 22 `EnvWf`; 19 inversion lemmas (`inv_lambda`/`inv_let`/…); 2 `let_poly` preservation cases (`:242`,`:2967`) | every inversion lemma's tuple shape + consumers re-elaborate under the new `lam`/`let_`/`let_poly` arity; the two preservation cases re-proved via `genAtV_closure_ready_value` | Phase 6, dominant cost |

The Soundness cost is dominated by **`HasTypeV` (256 sites)**, because migrating it to `HasTypeVAt`
touches the value-typing spine of every preservation/progress case, plus the 19 inversion lemmas whose
output tuples encode the (changing) `lam`/`let_`/`let_poly` shapes. Most cases don't *inspect* the level,
but every one **re-elaborates** under the new constructor arities — the exact re-elaboration cost the
Phase-3a note characterized, now confirmed at scale.

## Why no committable intermediate exists

`lakefile.toml`'s `lean_lib Eyg` uses `globs = ["Eyg.*"]`, which builds `Eyg.Types.Soundness` as part of
standard `lake build` (its axioms are checked in the green-tree contract). There is therefore **no
"green-except-Soundness" landable state**: the migration must reach a fully green `Soundness.lean` before
any commit. Combined with the absence of live LSP in this session (batch `lake build` only, on a
4278-line mutual-induction file), a blind full migration has a high probability of ending red and
unrecoverable in-session — precisely the outcome the plan's hard constraints forbid.

## Recommended execution plan for the next (LSP-equipped) session(s)

1. **Session A — promote `HasTypeAt`→`HasType` and re-green everything *except* Soundness.**
   Rename `HasTypeAt` to `HasType` (level-parameterized), delete the old magnitude `HasType`.
   Port `hasType_subst`←`hasTypeAt_subst`, `genAt_closure_ready`←`genAtV_closure_ready_value`,
   `HasTypeV`←`HasTypeVAt`, `EnvWf`←`EnvWfAt` (adding the mechanical partial/continuation arms).
   Re-green `Generation.lean` (inversion lemmas — new tuple shapes), `Substitution.lean`,
   `Generalization.lean`, `Runtime.lean`, `Machine.lean`. This is the bulk of Phases 4-5. Not
   committable yet (Soundness red), but a coherent worktree checkpoint.
2. **Session B (and possibly C) — re-green `Soundness.lean` (Phase 6).** Mechanically thread `lvl`
   through the 19 inversion-lemma consumers and the 141 case matches; re-prove the two `let_poly`
   preservation cases (`:242`, `:2967`) via `genAtV_closure_ready_value` (both already proven in
   isolation). Adjust the `soundness`/`soundness_evalR` *statements* if the level-parameterized
   `HasType` requires it (permitted; axiom set must stay `[propext, Classical.choice, Quot.sound]`).
   Only commit once fully green.

The mathematics is entirely settled (Phase 3b): every lemma Session A/B needs already exists and is
axiom-clean. What remains is large, mechanical, re-elaboration-heavy file editing that is safe to do
*only* with interactive goal-state tooling — not batch iteration.

## Current state

Tree **green and pristine** at `f33550e7`: zero source edits this session. `lake build` 1777, `lake exe
spec` 104/104 on all three lines, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`. The only
working-tree change is this note (+ the plan's Phase-4 entry annotation) and the untracked `.claude/`.
Phase 4 is **not landed**; it is confirmed inseparable from Phases 5-6 and correctly deferred to
LSP-equipped sessions, per the plan's conservative-budget / honest-stop philosophy.
