---
name: eyg-g1-level-tagged-ty-plan
description: Close Caveat 5 (nested let-polymorphism) by giving Ty a level-tagged variable representation, so nested generalization is structurally distinguishable instead of relying on a derivation-side de-Bruijn level. Multi-session; hard go/no-go checkpoint after the spike.
date: 2026-07-08
---

# G1 — nested let-polymorphism via a level-tagged `Ty`

## Background (do not re-derive)

The headline soundness theorem excludes nested *generalizable* `let`s (a `let` binding a
lambda, nested inside another generalized lambda's body) — `Tree.Node.noLambdaLet`
(`Typing.lean:106`). Prior sessions (`progress/2026-06-19-G1-foundational-wall-confirmed-no-additive-slice.md`
and its addendum) determined this is **not** an additive proof-engineering gap: it is a
representation wall in `Ty` itself.

**Root cause.** `Ty.var : Nat → Ty` (`Ty.lean:38`) is one flat index space. A `Scheme
⟨arity, body⟩` splits it in two *by convention* — indices `< arity` are this scheme's own
quantifiers, `≥ arity` is ambient/enclosing scope (`Scheme.lean:316-328`). That convention
works for exactly one layer of generalization. The current code instead threads a
**derivation-level de-Bruijn level** `n` (`HasType.let_poly`'s `n`, `Scheme.genAt n`,
`CtxWf n`) to fake a second layer — which works for typing a single top-level `let_poly`,
but breaks when re-proving `hasType_subst`'s `let_poly` arm for a *nested* one: the
instantiation witness `σ_args` (`Scheme.instantiate`) is a plain down-shift, and down-shifts
don't compose with the `LevelMap` substitution-stability argument
(`generalizesAt_subst`) the second layer needs. `generalizes_subst_false` is a
machine-checked theorem that no arbitrary substitution discharges this — the wall is real,
not a missing lemma.

Full sizing and rejected alternatives (intrinsically-scoped `Fin`-indexed `Ty`; named
variables + alpha-equivalence) are in the session transcript this plan was written from;
summary: level-tagging `Ty.var` is the minimal structural fix that keeps `subst` structural
(no shifting-logic change, no capture-avoidance) while making "which generalization layer"
decidable from the type itself instead of a side-channel.

## The fix

Change the variable constructor from `Ty.var (idx : Nat)` to `Ty.var (level idx : Nat)`.
`level` names which generalization layer a variable belongs to (0 = outermost/globally-
ambient, k = k-deep in nested polymorphic lets); `idx` is its position within that layer.
Instantiating a scheme at level `k` only ever touches `var k _`; every other level is
structurally untouched by that instantiation — no more index-arithmetic disambiguation,
no down-shift/`LevelMap` mismatch.

## Blast radius (measured from the current tree)

| File | Lines | `.var` sites | `HasType`/`HasTypeV` matches | Note |
|---|---|---|---|---|
| `Ty.lean` | 197 | 1 | – | the constructor itself; `TyEquiv` congruence shapes unaffected |
| `Scheme.lean` | 548 | 18 | – | `instantiate`/`substScheme`/`genAt`/`freeVars` — all index arithmetic, every one re-derived |
| `Substitution.lean` | 156 | 1 | 22 | **the crux** — where the nested `let_poly` arm currently goes vacuous |
| `Generalization.lean` | 591 | 35 | 11 | heaviest non-Soundness file; `genAt`, `LevelMap`, `generalizesAt_subst` |
| `Typing.lean` | 329 | 7 | – | `let_poly` rule signature (drop side-channel `n`, or reinterpret as the tag) |
| `Machine.lean` / `Runtime.lean` | 430 / 585 | 2 / 2 | 8 / 10 | value typing / interpreter port, mechanical re-green |
| `Soundness.lean` | 4278 | 20 | **141** | dominant cost: every `preservation`/`progress` case (A-engine + B-mirror) re-elaborates under the new constructor arity, even where the *logic* is unaffected |

~7,600 lines across 13 files touch `Ty`/`HasType`/`Scheme`; `Soundness.lean` is ~60% of
that and is where a constructor-arity change costs the most just from re-elaboration.

**Correction from Phase 3a (2026-07-08):** this table overstated the blast radius for
the *representation* change specifically. `Typing.lean`, `Machine.lean`, `Runtime.lean`,
`Substitution.lean`, `Generation.lean` needed **zero changes** for the `Ty.var` arity
change — their `.var`/`HasType.var` hits were all the unrelated `HasType.var` *judgment*
constructor, not `Ty.var`. Only `Scheme.lean` (real proof changes: totality + level
case-splits) and `Generalization.lean`/`Soundness.lean` (mechanical `.var i → .var 0 i`
transliteration, zero manual fixes needed in Generalization.lean beyond the mechanical
pass) were touched — see `progress/2026-07-08-G1-phase3a-done-phase3b-scoped.md` for the
exact diff shape. The *capability* work (Phase 3b onward — giving `Scheme` a real level
field and level-parameterizing `hasType_subst`) is where the real remaining cost is, not
the datatype change itself.

## Phases

- [x] **Phase 1 (spike) — tagged core in isolation.** DONE (2026-07-08),
      `Eyg/Types/LevelTagSpike.lean`: a minimal `var`/`fn`-only model with
      `Ty2.var (level idx : Nat)`, `substAt`, `Scheme2`, `genAt`, `instantiate`,
      `substScheme`. Touches nothing existing; wired into `Eyg.lean` only to be
      build-checked. `lake build` 1774 jobs, axiom/`sorry`-clean.
- [x] **Phase 2 (spike, go/no-go) — re-prove `generalizesAt_subst`'s nested case.**
      **GO** (2026-07-08) — see `progress/2026-07-08-G1-level-tag-spike-GO.md`.
      `substScheme_genAt` (the direct analog of `genAt_substScheme`) holds with **no
      `LevelMap`-style hypothesis at all** — `simp only [Scheme2.substScheme,
      Scheme2.genAt]`, essentially definitional. The original `generalizes_subst_false`
      counterexample scenario, re-run tagged, no longer collides. The down-shift/
      re-level problem that blocked the untagged system doesn't arise because
      `genAt`/`substAt` never inspect index magnitude, only the level tag.
      **Checkpoint passed — proceeding to Phase 3.**
- [x] **Phase 3a — port the level tag onto the real `Ty`, collapsed to level `0`.** DONE
      (2026-07-08, commit `8108591a`): `Ty.var(idx)` → `Ty.var(level, idx)`; every
      pre-existing use pinned to level `0` (pure representation change, zero semantic
      change). `lake build` 1774, spec 104/104, axioms unchanged. See
      `progress/2026-07-08-G1-phase3a-done-phase3b-scoped.md`.
- [ ] **Phase 3b — make `Scheme`/`genAt`/`instantiate` level-native.** Give `Scheme` a
      `level` field; `genAt`/`instantiate`/`substScheme` become level-tag-based (no
      reindexing). **Attempted 2026-07-08, not landed — found a real subtlety, fully
      scoped in the progress note above:** `hasType_subst` must become
      level-parameterized (not hardcoded to level `0`) throughout its whole induction,
      not just the `let_poly` arm; and `subst_instantiate`/`subst_instantiate'` (the
      `var`/`builtin` rule arms) need a genuine side-condition on the ambient
      substitution's range (distinct from — but analogous in spirit to — the old
      `LevelMap`), unlike the *stored-scheme* commutation (`substScheme_genAt`-shape),
      which the spike already confirmed is unconditional. **Both commutation facts are
      now mechanically validated in isolation** (`LevelTagSpike.lean`, commit
      `c2db9272`): `substScheme_genAt` (unconditional) and `substAt_substAt_comm` +
      `substAt_eq_self_of_not_mem` (the conditional one, with its exact side condition
      `hclean`). Porting these onto the real `Ty`/`Scheme` and re-deriving
      `Generalization.lean`'s `CtxWf`/freshness threading around the *level* dimension
      is real file-editing work but no longer open mathematical uncertainty. 7-step
      continuation spec is in the progress note.
- [ ] **Phase 4 — re-thread `Typing.lean`.** Drop the side-channel `n`/`CtxWf`; `let_poly`
      uses the tag directly; drop `noLambdaLet` from the rule (the actual deliverable).
- [ ] **Phase 5 — re-green `Machine.lean`/`Runtime.lean`** (value typing, interpreter port).
      Mechanical but must land fully before Phase 6, since it's upstream of every
      preservation case.
- [ ] **Phase 6 — re-green `Soundness.lean`.** The expensive step: mostly "adjust to
      compile" (most of the 141 case-matches don't inspect `var` directly), plus genuine
      re-proof for the `let_poly` preservation/progress cases specifically.
- [ ] **Phase 7 — sanity example + report update.** A nested-generalizable-let example
      (e.g. `let f = \x. (let g = \y.y in g x) in ...`) types under the relaxed rule;
      Caveat 5 in `plan/report/type-soundness-report.md` updated to reflect the closed gap
      (mirroring how Caveats 3/4 record corrected restrictions).

## Definition of done (per phase, and overall)

`lake build` + `lake exe spec` 104/104 green, `#print axioms soundness` (and
`soundness_evalR`) still exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`, at
every commit — this is not landable partially the way `EffSub'` was; don't leave the tree
red between sessions. If Phase 2 fails, that is a legitimate outcome: record why in
`plan/progress/`, same as `2026-06-19-G1-foundational-wall-confirmed-no-additive-slice.md`
did, and the caveat stays open and honestly documented.

## Estimate

Phases 1–2 (spike) and 3a (real datatype port) are **done** (2026-07-08, one session,
three commits: `406061c1` spike, `8108591a` Phase 3a, plus two further spike commits
`c2db9272`/`a3e448f7` that fully validate Phase 3b's remaining math — the conditional
`hasType_subst`-var/builtin commutation and the `CtxWf`/freshness-threading discipline,
both with zero open uncertainty left). Phase 3b's *math* is settled; what's left is
porting it onto the real `Ty`/`Scheme`/`Generalization.lean` (including a full redesign
of `CtxWf` and every lemma downstream of it — `ctxWf_fixed`, `ctxWf_substCtx`,
`genAt_generalizes`, `genAt_closure_ready`, `generalizes_closure_ready` — around levels
instead of magnitude) plus level-parameterizing `hasType_subst` across all ~15 rule
cases in `Substitution.lean` — genuinely substantial file-editing even with the design
fully de-risked. Then Phases 4–7 (re-thread `Typing.lean`, re-green `Machine`/`Runtime`,
re-green `Soundness.lean`, sanity example + report). Revised rough sizing: Phase 3b
1–2 more sessions (now low-risk, not open-ended), Phases 4–7 2–3 more. Total from here:
3–5 sessions.
