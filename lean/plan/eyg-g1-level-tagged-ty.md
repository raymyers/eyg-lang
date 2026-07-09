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
- [x] **Phase 3b — make `Scheme`/`genAt`/`instantiate` level-native.** DONE (2026-07-08,
      seven follow-up sessions, commits `ea64f73c` through `78fa925e`). The mathematical
      wall is fully resolved, both term- and value-typing sides, all the way down to a
      concrete runtime closure — see `RuntimeAtV.lean`'s `genAtV_closure_ready_value` and
      the `hOuterVClosure_*` demonstrations. What remains (Phases 4–7 below) is folding
      this back into the real `HasType`/`HasTypeV`/`EnvWf`/`Soundness.lean` — engineering
      against a now-fully-de-risked design, not open mathematics. Detailed history: Give `Scheme` a
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
      **Progress 2026-07-08 (same day, follow-up session), commits `ea64f73c`/
      `53300a81`/`3e25495c`/`58d22a0a`, see `progress/2026-07-08-G1-phase3b-scheme-
      level-field-and-substAt-ported.md`:** four green, verified sub-steps landed —
      (1) `Ty.substAt`/`Ty.levels`/`Ty.freeVarsAt` + `substAt_eq_self_of_not_mem`/
      `substAt_substAt_comm` ported from the spike's toy `Ty2` onto the real 12-former
      `Ty` (purely additive, retires the "audit the 12-former case" open item);
      (2) `Scheme` now actually carries the `level : Nat` field (pinned to `0`
      everywhere, `genAt`/`instantiate`/`substScheme` logic still the old magnitude
      machinery — pure representation change, mirrors Phase 3a's playbook);
      (3) **`genAtV`/`instantiateV`/`substSchemeV`** — the level-native redesign
      itself, landed as an additive prototype (named with a `V` suffix, coexisting
      with the still-magnitude-based originals, not yet wired into
      `Typing.lean`/`Generalization.lean`) — with **`subst_instantiateV` proved**:
      substitution commutes with level-native instantiation for a scheme generalized
      at any nonzero level, given the `hclean` side-condition, built directly from
      `substAt_substAt_comm`. This is the actual mathematical core `hasType_subst`'s
      `var`/`builtin` arms will need, now proven on the real `Scheme`/`Ty` (not just
      the spike); (4) **`CtxWfV`/`ctxWfV_cons`** — the freshness-threading discipline
      ported onto the real `Ctx`, completing the port of the *whole* spike (not just
      its one-shot commutation). Two design subtleties in the level-native flip were
      found and resolved **by hand** (no live Lean session — this follow-up had no
      Lean LSP/interactive goal-state tooling, only batch `lake build`), then
      confirmed correct by the successful `subst_instantiateV` proof: (a)
      `instantiateV` needs an explicit `arity = 0` short-circuit, or
      `instantiateV_mono` breaks for mono schemes whose body references *other*
      ambient variables at whatever level they're tagged; (b) `substSchemeV`-after-
      `genAtV` should **not** be expected to equal `genAtV` on the substituted body
      (that only held in the spike because `Scheme2` has no `arity` field at all) —
      the commutation targets the `instantiate`-level directly instead, which never
      reads `.arity`. **What's left to actually retire Phase 3b:** bridge
      `subst_instantiateV`/`CtxWfV` to the `generalizes_closure_ready` keystone (a
      level-native `GeneralizesAtV`, mirroring `GeneralizesAt`/`genAt_generalizesAt`)
      — but that keystone bottoms out in `closure_typed_of_lambda_subst`
      (`Substitution.lean`), built on the **still level-`0`-only** `hasType_subst`.
      So the remaining Phase 3b work is unavoidably: level-parameterize
      `hasType_subst` (`Ty.substAt ℓ` throughout its whole induction, ~15 rule
      cases in `Substitution.lean`, not just the `let_poly` arm) — genuinely large,
      error-prone file-editing best done with live Lean LSP tool access (interactive
      goal-state inspection), not batch `lake build` iteration. Full detail and a
      sharpened continuation spec are in the progress note.
      **Progress 2026-07-08 (third follow-up session, WITH Lean tool access), see
      `progress/2026-07-08-G1-phase3b-hasType_substAt-nested-arm-grounded.md`:** two more
      green additive commits landed, resolving the *substitution-commutation* half of the
      wall and machine-grounding the exact residual gap. (1) **`GeneralizesAtV`**
      (`Generalization.lean`) — the level-native mirror of `GeneralizesAt`, with
      `genAtV_generalizesAtV` and the keystone **`genAtV_substSchemeV_generalizesAtV`**:
      substitution-stability of a level-`ℓ` generalization under an *arbitrary* ambient
      (level-`0`) `σ`, proved with **no `LevelMap`/`hclean`/`ℓ≠0` premise at all** (plus
      `Ty.substAt_var_self`, `substAt_fixes_zero`). This is exactly the obligation
      `generalizes_subst_false` proves *false* for the flat encoding — now trivial
      level-natively, on the real 12-former `Ty`/`Scheme`. (2) **`hasType_substLM_letPoly`
      + `substCtx_cons_genAt`** — the `hasType_subst` `let_poly` arm **fired non-vacuously**
      on the existing `HasType`: given `LevelMap n σ` at the let's stored level `n`, the
      `Let`-binds-a-`Lambda` node reconstructs via `HasType.let_poly` from the two
      substituted sub-derivations, `noLambdaLet` required only on the inner lambda body
      (not the whole term — so it fires on a term the general `hasType_subst` cannot reach).
      **Exact residual gap, now machine-grounded (not hand-argued):** the *only* missing
      hypothesis for a full `hasType_substAt` induction is `n ≤ n_let` — the ambient threaded
      de-Bruijn level must be `≤` each `let_poly`'s stored generalization level, so
      `LevelMap n σ` lifts (`LevelMap.mono`) to `LevelMap n_let σ`. `HasType.let_poly` does
      not record the ambient level, so this needs a **level-tracking judgment**
      (`HasTypeAt (lvl) Γ e τ ε`, `let_poly` generalizes at exactly `lvl`, binders bump
      `lvl`) — the next concrete deliverable. The wall itself is now removed (the
      substitution-commutation is proved both magnitude-native *and* level-native); what
      remains is judgment-plumbing, not open mathematics.
      **Progress 2026-07-08 (fourth follow-up session, WITH Lean tool access — the
      deliverable landed), see
      `progress/2026-07-08-G1-phase3b-HasTypeAt-nested-arm-landed.md`:** the level-tracking
      judgment and its substitution lemma are DONE, one green additive commit in a new file
      `Eyg/Types/TypingAt.lean`. (1) **`HasTypeAt (lvl) Γ e τ ε`** — the ~21-constructor
      parallel of `HasType` threading the ambient level: `let_poly` generalizes at *exactly*
      `lvl` (so `n_let = lvl` by construction — the `n ≤ n_let` gap is now `rfl`), records
      `CtxWf lvl Γ`, types its body at `lvl + 1`, and carries **no `noLambdaLet`** (nested
      `Let`-binds-`Lambda` genuinely accepted); `lam`/`let_` store an explicit sublevel
      `lvl'` with `lvl ≤ lvl'` + `freeVars argTy < lvl'` rather than a *computed* bump (the
      one non-mechanical subtlety: a computed `genArity 0` bump does not commute with a
      `LevelMap lvl` substitution for `lvl > 0`; a stored `lvl'` reconstructs at the same
      level, `freeVars (subst σ argTy) < lvl'` following structurally from `LevelMap`).
      (2) **`hasTypeAt_subst`** — the level-parameterized `hasType_subst` analog, with a
      **non-vacuous `let_poly` arm firing for arbitrarily deep nesting** (no `noLambdaLet`
      on the term): reconstructs via `substCtx_cons_genAt`/`ctxWf_substCtx`/`genAt_substScheme`
      (the `hasType_substLM_letPoly` pattern) on the magnitude machinery, plus one helper
      `genAt_freeVars_lt`. (3) **The wall-falls check** — `hInner`/`hOuter` type the exact
      Caveat-5 term `let outer = \x. (let inner = \y.y in inner x) in outer 1` (doubly
      generalized) under `HasTypeAt`, and `hInner_subst` applies `hasTypeAt_subst` with a
      genuine non-identity `α ↦ integer` (`LevelMap 1`) to re-type the nested `Let`-binds-
      `Lambda` core at `integer` under `x : integer` — non-vacuous. `lake build` 1775, spec
      104/104, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`. Purely additive.
      Remaining Phase 3b-tail/Phase 4: migrate to the level-native
      `genAtV`/`CtxWfV`/`GeneralizesAtV` (for the readiness keystone) and drop `noLambdaLet`
      from `HasType.let_poly` itself in `Typing.lean`.
      **Progress 2026-07-08 (fifth follow-up session — the readiness keystone examined; down-shift
      wall confirmed removed at the mathematics level, two plumbing obstructions located), see
      `progress/2026-07-08-G1-phase3b-readiness-keystone-two-obstructions-located.md`:** one green
      additive commit (`substAt_instantiateV` + `substSchemeVAt` in `Scheme.lean`) — the readiness
      keystone's **cross-level instantiation commutation**: it generalizes `subst_instantiateV` from a
      level-`0` ambient substitution to an **arbitrary level-`ℓ'`** one (`ℓ' ≠` the inner scheme's
      level `ℓ`, `σ` clean w.r.t. `ℓ`), the `var`/`builtin`-arm commutation a level-native re-typing
      under the *outer scheme's instantiation* would consume for a nested inner scheme. With this the
      **mathematics half of the readiness keystone is complete**: both commutations it rests on — the
      stored-scheme one (`genAtV_substSchemeV_generalizesAtV`, unconditional) and the instantiated-type
      one (`substAt_instantiateV`, level-disjoint + clean) — are proved level-natively on the real
      `Ty`/`Scheme`. **The 2026-06-19 down-shift wall is confirmed removed level-natively** (the
      instantiation substitution is "anti-`LevelMap`" — moves the generalized region, fixes the ambient
      — which is why `hasType_subst`/`hasTypeAt_subst`, both `LevelMap`-only, cannot discharge it and
      degenerate to `σ = id` at `lvl = 0`; distinct levels make the two motions orthogonal, no
      down-shift). **But the readiness keystone does NOT close additively this session**, blocked by two
      distinct, precisely-located obstructions, *neither of which is the down-shift wall*: **(A)** a full
      `substAt ℓ` re-typing induction on a `genAtV`-storing judgment (`HasTypeAtV`) is not yet built —
      the current `HasTypeAt` deliberately stores the magnitude `genAt`/level-`0` vars and re-types under
      level-`0` `subst`, wrong for the instantiation motion; de-risked (every per-arm commutation is now
      proved) but a multi-session parallel judgment; **(B)** `Runtime.lean`'s `HasTypeV.closure`/`EnvWf`
      require a *magnitude* `HasType` closure-body derivation, which for a nested body of
      generalization-depth ≥ 3 (a middle lambda whose body binds a polymorphically-used lambda-let) does
      not exist (`noLambdaLet lbody` fails), so the value judgment can't express the closure typing until
      Phase 4 (drop `noLambdaLet` from `HasType.let_poly`) or Phase 5 (parallel `HasTypeVAt`/`EnvWfAt`).
      Both are anticipated judgment plumbing, not open mathematics.
      **Progress 2026-07-08 (sixth follow-up session — obstruction (A) RESOLVED, the level-native
      readiness keystone landed), see
      `progress/2026-07-08-G1-phase3b-HasTypeAtV-instantiation-keystone-landed.md`:** one green
      additive commit in a new file `Eyg/Types/TypingAtV.lean` — obstruction (A) is closed. (1)
      **`HasTypeAtV lvl Γ e τ ε`** — the level-native sibling of `HasTypeAt`: `let_poly` generalizes at
      exactly `lvl` via `Scheme.genAtV lvl` (not the magnitude `genAt`), records `CtxWfV lvl Γ`, types
      its body at `lvl + 1`, no `noLambdaLet`; `lam`/`let_` store a sublevel `lvl'` with the
      `Ty.levels`-shaped freshness `∀ l ∈ argTy.levels, l < lvl'`; `var`/`builtin` instantiate via
      `Scheme.instantiateV`. (2) **`hasTypeAtV_substAt`** — the full **instantiation-direction** re-typing
      induction (all ~21 arms): re-type under an *outer* `substAt ℓ` (`ℓ ≠ 0`, `ℓ < lvl`, `σ`'s levels
      `≤ ℓ`, context poly-bindings above `ℓ` via the `PolyAbove` invariant). The `let_poly` arm
      reconstructs level-natively via `substSchemeVAt_genAtV` (a new `genAtV`-arity-stability lemma built
      on a level-`k`-occurrence *count-preservation* lemma `length_filter_levels_substAt` — the
      unconditional-in-the-level-dimension analog of `genAt_substScheme`, needing only level-disjointness
      + freshness, no `LevelMap`); the `var` arm via a new general `substAt_instantiateV_scheme` (covers
      every mono/`genAtV`-at-a-distinct-level binding); the `builtin` arm via `substAt_instantiateV_closed`
      + a closed-body commutation `substAt_substAt_comm_of_no_mem` (builtins are level-`0`-closed, proved
      by `Builtins.scheme_levels_zero`/`scheme_no_level`). (3) **`genAtV_instantiate_lam_ready`** — the
      level-native readiness keystone: for a let-bound lambda typed via its `lam` components at ambient
      level `ℓ` (body strictly above `ℓ`, context below `ℓ`, args' levels `≤ ℓ`), **every** instantiation
      of its scheme `genAtV ℓ defnTy` is a genuine `substAt ℓ` re-typing of the lambda's own
      `HasTypeAtV` derivation (composing `genAtV_generalizesAtV` with `hasTypeAtV_substAt`, plus
      `substCtxAt_fix` for the ambient context being fixed structurally). Does NOT wire in
      `Value.Closure`/`HasTypeV`/`EnvWf` — that is obstruction (B), still a future session. (4) **Nested
      non-vacuous demonstration** — `hInnerV`/`hOuterV_instantiate`/`hOuterV_typed_integer_arrow` type the
      exact Caveat-5 term `\x. (let inner = \y.y in inner x)` (outer scheme at level `1`, nested inner at
      the *distinct* level `2`) and run the keystone at `[integer]`, producing a genuine non-identity
      re-typing `Integer → Integer` (outer `α ↦ integer`, inner re-generalized at level `2`) — the
      level-native "wall falls" check, on a term the original chain reaches only vacuously. `lake build`
      1776 jobs, spec 104/104 on all three lines, axioms `[propext, Classical.choice, Quot.sound]`, no
      `sorry`. Purely additive (`HasType`, `HasTypeAt`, `Runtime.lean`, `Soundness.lean` untouched).
      **Only obstruction (B) remains for the value-typing keystone**: `HasTypeVAt`/`EnvWfAt` (or Phase 4's
      `noLambdaLet` drop) to turn this term-level re-typing into `HasTypeV (Value.Closure …)`.
      **Progress 2026-07-08 (seventh follow-up session — obstruction (B) RESOLVED, the value-side keystone
      landed; Caveat 5's soundness gap closed both term- and value-side), see
      `progress/2026-07-08-G1-phase3b-HasTypeVAt-value-keystone-landed.md`:** one green additive commit in
      a new file `Eyg/Types/RuntimeAtV.lean` — obstruction (B) is closed. (1) **`HasTypeVAt lvl v τ`** —
      the level-native value-typing sibling of `HasTypeV`, whose `closure` constructor consumes a
      **level-native `HasTypeAtV lvl Γ ⟨.Lambda x body, a⟩ τ ε`** lambda derivation (which exists for
      arbitrarily nested generalization, no `noLambdaLet`) instead of the `noLambdaLet`-restricted
      magnitude `HasType` body derivation `HasTypeV.closure` demands; base literals thread `Ty.TyEquiv`
      unchanged; `HasTypeVAt.conv` derived. (2) **`EnvWfAt env Γ`** — the level-native `EnvWf` sibling,
      its `cons` readiness stated over `HasTypeVAt s.level`/`Scheme.instantiateV` at the scheme's own
      generalization level, with the natural instantiation-args side-condition `∀ t ∈ args, ∀ l ∈
      t.levels, l ≤ s.level` (the value-side of `hasTypeAtV_substAt`'s `hσ` bound). (3) **The value-level
      keystone `genAtV_closure_ready_value`** — the level-native `generalizes_closure_ready`: composes
      `genAtV_instantiate_lam_ready` (term level) with `HasTypeVAt.closure` to prove a let-bound lambda's
      runtime closure inhabits **every** (well-formed) instantiation of `genAtV ℓ defnTy` — exactly the
      `EnvWfAt.cons` obligation, discharged with **no `noLambdaLet`** on the closure body. (4) **The
      nested demonstration** — reusing `hInnerV`/`hOuterV_instantiate`, builds the *actual runtime
      closure* `Value.Closure "x" outerBody []` for the outer lambda `\x. (let inner = \y.y in inner x)`
      and shows it `HasTypeVAt`-typed at `Integer → Integer` (via both the keystone `hOuterVClosure_ready`
      /`hOuterVClosure_typed_integer_arrow` and the plain constructor `hOuterVClosure_via_constructor`) —
      the whole chain `term derivation → closure value → typed-at-every-instantiation` genuinely closing
      for the doubly-nested Caveat-5 case the original `HasType`/`HasTypeV`/`generalizes_closure_ready`
      chain reaches only vacuously. `lake build` 1777 jobs, spec 104/104 on all three lines, axioms
      `[propext, Classical.choice, Quot.sound]` (soundness, soundness_evalR, and the new theorems), no
      `sorry`. Purely additive (`HasType`, `HasTypeV`, `EnvWf`, `Runtime.lean`, `Soundness.lean`, every
      prior declaration untouched; only edits outside the new file are the `import` in `Eyg.lean` and this
      note). **This is the complete mathematical resolution of Caveat 5's soundness gap — both the
      term-typing and value-typing sides of nested let-polymorphism, all the way down to a concrete
      runtime closure.** Remaining for Phases 4–7: fold this back into `Typing.lean`/`Machine`/`Runtime`/
      `Soundness.lean` by actually dropping `noLambdaLet` from `HasType.let_poly` and re-greening the
      soundness proof over the level-native judgments — engineering, not open mathematics. The
      value-side `HasTypeVAt` deliberately mirrors only the generalization-bearing shapes (base literals +
      the crux `closure`); the runtime-continuation / partial value constructors (`partialBuiltin`,
      `partialResume`, data/partials) carry zero generalization content and are mechanical
      `HasTypeV → HasTypeVAt lvl` transliterations left for the Phase-5 `Machine`/`Runtime` re-green.
- [x] **Phase 4 — re-thread `Typing.lean`.** DONE (2026-07-08, "Session A", commit noted below).
      `HasType` is now level-parameterized (`HasType lvl Γ e τ ε`); `let_poly` generalizes at exactly
      `lvl` via `Scheme.genAtV`/`CtxWfV`, **`noLambdaLet` dropped**, no side-channel `n`. `hasType_subst`
      (instantiation-direction) + `genAtV_instantiate_lam_ready` live in `Typing.lean`. See
      `progress/2026-07-08-G1-phase4-5-sessionA-hastype-promoted-soundness-red.md`.
- [ ] **Phase 4 (superseded scoping note) — re-thread `Typing.lean`.** Drop the side-channel `n`/`CtxWf`; `let_poly`
      uses the tag directly; drop `noLambdaLet` from the rule (the actual deliverable).
      **Scoped 2026-07-08 (no source edits, tree held green at `f33550e7`), see
      `progress/2026-07-08-G1-phase4-scoped-multisession-not-landed.md`:** grounded blast-radius
      measurement confirms Phase 4 is **inseparable from Phases 5-6** and not one-session-landable
      without live LSP. The `noLambdaLet` field is load-bearing for *preservation*, not just typing:
      `Soundness.lean:242`/`:2967` (the two `let_poly` preservation cases) literally call
      `genAt_closure_ready … hnl …`, consuming the constructor's `noLambdaLet` field via `inv_let`.
      Dropping it makes both cases unprovable with the magnitude machinery; the only replacement,
      the level-native `genAtV_closure_ready_value` (`RuntimeAtV.lean`), concludes `HasTypeVAt`/
      `instantiateV`, whose type cannot bridge `EnvWf.cons`'s fixed `HasTypeV`/`instantiate`
      obligation — forcing `HasTypeV`→`HasTypeVAt` (**256 Soundness sites**) and `EnvWf`→`EnvWfAt`
      (22) wholesale, plus `HasType`→level-parameterized (changing `lam`/`let_`/`let_poly` arities,
      hence all 19 inversion lemmas + their consumers). No committable green intermediate exists
      (`Eyg.*` glob builds `Soundness`). Recommended: Session A promotes `HasTypeAt`→`HasType` and
      re-greens everything except Soundness (Phases 4-5); Session B/C re-greens `Soundness.lean`
      (Phase 6). All required lemmas already exist axiom-clean (Phase 3b); the remainder is
      re-elaboration-heavy editing safe only with interactive goal-state tooling.
- [x] **Phase 5 — re-green `Machine.lean`/`Runtime.lean`** (value typing, interpreter port). DONE
      (2026-07-08, "Session A"). `HasTypeV`/`EnvWf`/`StackWf`/`StackSegWf` keep their arities (the
      ambient level is an **existential field** of `closure`/`assign`/`arg`, not an index — this
      collapses the projected ~256-site migration to a handful of sites). `EnvWf.cons` readiness is now
      level-native + conditional; `genAtV_closure_ready_value` ported into `Substitution.lean`.
      `Generation.lean`/`Generalization.lean` re-greened; the magnitude readiness keystones removed as
      superseded. Prototype files (`TypingAt`/`TypingAtV`/`RuntimeAtV`) deleted. Verified green
      per-file; `Soundness.lean` deliberately left red (authorized exception — see the progress note).
- [ ] **Phase 6 — re-green `Soundness.lean` (Session B).** The remaining step, all mechanical (101+
      errors, categorized in `progress/2026-07-08-G1-phase4-5-sessionA-hastype-promoted-soundness-red.md`):
      thread `lvl` through the inversion-lemma consumers and case matches; re-prove the two `let_poly`
      preservation cases via `genAtV_closure_ready_value`; adjust `soundness`/`soundness_evalR` to type
      at a nonzero ambient level (`ℓ ≠ 0` for the keystone). Only commit once fully green.
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
