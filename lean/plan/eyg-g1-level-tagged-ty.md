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
- [ ] **Phase 6 — re-green `Soundness.lean` (Session B).** The remaining step, scoped as mechanical
      (101+ errors, categorized in
      `progress/2026-07-08-G1-phase4-5-sessionA-hastype-promoted-soundness-red.md`): thread `lvl`
      through the inversion-lemma consumers and case matches; re-prove the two `let_poly` preservation
      cases via `genAtV_closure_ready_value`; adjust `soundness`/`soundness_evalR` to a nonzero ambient
      level. **BLOCKED — Session B (2026-07-08) confirmed a non-mechanical wall; STOPPED, tree left at
      `6deadc54`.** See `progress/2026-07-08-G1-phase6-sessionB-polyabove-wall-sequential-letpoly.md`.
      The keystone `genAtV_closure_ready_value` requires `PolyAbove ℓ Γ`, which is **provably false**
      (machine-checked) for the ambient context of any nested/sequential `let_poly` — the two
      preservation cases are unprovable with it, and the level-native keystone thereby **regresses basic
      sequential let-polymorphism** (sound in the pre-G1 magnitude system, whose `noLambdaLet` only ever
      restricted a let-binds-lambda nested in a generalized lambda's body, never sequential lets). Real
      fix: re-prove `hasType_subst` (`Typing.lean`) with a **free-variable-aware** precondition
      replacing blanket `PolyAbove` (the `var` arm only ever uses it for the looked-up variable), then
      re-derive `genAtV_instantiate_lam_ready`/`genAtV_closure_ready_value` — genuine metatheory, best
      with live LSP, multi-session, *above* the still-pending ~150-error mechanical migration. The
      mechanical migration pattern + the required `StackWfV`/`StackWfE`→`instantiateV`+side-condition
      `Machine.lean` refactor are recorded in the note for reuse. Caveat 5 remains OPEN.
      **Progress 2026-07-08 (Session B2 — the `PolyAbove` wall RESOLVED), see
      `progress/2026-07-08-G1-phase6-sessionB2-polyaboveFV-keystone-fixed.md`:** one green additive edit
      to `Typing.lean`/`Substitution.lean` (both build green per-file; `Soundness.lean` deliberately
      untouched). The blanket `PolyAbove ℓ Γ` precondition is replaced by the **free-variable-aware**
      `PolyAboveFV ℓ Γ e := ∀ x ∈ e.freeVars, ∀ s, Γ.lookup x = some s → s.arity = 0 ∨ ℓ < s.level`
      (new `Node.freeVars`; helpers `polyAboveFV_sub`/`_bind`; `polyAboveFV_of_polyAbove` bridge). It
      threads through the whole `hasType_subst` induction because every binder adds a *fine* binding
      (`mono` ⇒ `arity 0`; `let_poly`'s `genAtV lvl` ⇒ `level = lvl > ℓ`), so it never constrains the
      pre-existing ambient bindings the term does not reference. `hasType_subst`,
      `genAtV_instantiate_lam_ready`, and `genAtV_closure_ready_value` re-proved over
      `PolyAboveFV ℓ Γ ⟨.Lambda x lbody, la⟩`; axioms unchanged (`[propext, Classical.choice,
      Quot.sound]`), no `sorry`. **Validated non-vacuously** with permanent regression examples in
      `Typing.lean`: `¬ PolyAbove 2 Γseq` (the wall, `by decide`), `PolyAboveFV 2 Γseq (\z.z)` (holds
      where `PolyAbove` fails), the keystone firing for `c` at level 2 producing
      `\z.z : Integer → Integer`, and the whole program `let a = \x.x in (let c = \z.z in c)`
      type-checking at `HasType 1 []`. **Residual for Session C (flagged, not forced):** the
      *referencing* case (a generalized inner lambda that references an outer lower-level polymorphic
      binding, e.g. `let a = \x.x in (let c = \w. a w in c)`) needs a tightening of `EnvWf.cons`'s args
      side-condition (the level-native analog of the pre-G1 `ctxWf_fixed`/`subst_eq_of_fixes_free`),
      best settled with the Soundness preservation cases that produce the args — judgment bookkeeping,
      not open mathematics. Full analysis in the note.
      **Progress 2026-07-08 (Session C — referencing-case gap CLOSED; Soundness re-green still pending),
      commit `32c42948`, see
      `progress/2026-07-08-G1-phase6-sessionC-referencing-case-closed-soundness-pending.md`:** Part 1
      done via two coordinated additive changes — (1) weaken `PolyAboveFV`'s per-variable disjunct from
      `ℓ < s.level` to `s.level ≠ 0 ∧ s.level ≠ ℓ` (admits referenced bindings *below* `ℓ`); (2) tighten
      the substitution/args side-condition from `l ≤ ℓ` to `l = 0 ∨ l = ℓ` throughout (`hasType_subst`,
      `genAtV_instantiate_lam_ready`, `genAtV_closure_ready_value`, `EnvWf.cons`/`envwf_lookup`,
      `StackWfV`/`StackWfE`). The `var` arm derives cleanliness `s.level ∉ σ.levels` from
      `σ.levels ⊆ {0, ℓ}` + `s.level ∉ {0, ℓ}`, uniformly below *and* above `ℓ`. Validated non-vacuously
      (permanent regression examples in `Typing.lean`: `polyAboveFV_reflam`, `hbody_ref`, keystone firing
      to `Integer → Integer`, whole referencing program `let a = \x.x in (let c = \w. a w in c)` at
      `HasType 1 []`). Per-file green, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`.
      **Part 2 (re-green `Soundness.lean`) NOT reached** — 103 errors; working-tree Soundness found
      partially migrated, left as-found (uncommitted, unedited this session). One non-mechanical
      obstruction for Session D: var-preservation must discharge the tightened args side-condition for
      args `HasType.var` does not record — needs a runtime "instantiation args are ground/ambient-level"
      invariant on the machine-state typing (NOT a premise on `HasType.var`, which would wrongly reject
      typing-time instantiations). Error-cluster map + recommended Session D order in the note.
      **Progress 2026-07-08 (Session D — the two non-mechanical pieces DESIGNED + VALIDATED, Soundness
      error map corrected to its true two-engine shape; no LSP this session so the mechanical grind was
      not attempted; NOTHING committed), see
      `progress/2026-07-08-G1-phase6-sessionD-runtime-groundness-invariant-designed-soundness-two-engine-map.md`:**
      (1) **The var-preservation obstruction is designed and validated.** The invariant is *runtime
      groundness*: in a running well-typed machine state, the control's `HasType` derivation has all
      `var`/`builtin` instantiation args ground (levels `⊆ {0}` ⊆ the `l=0∨l=s.level` bound). Validated
      against `hbody_ref` (`Typing.lean` examples): its non-ground arg (`a:level 1` at `[var 2 0]`) is a
      *static* subderivation inside a level-2 generalization; when the closure is applied the keystone's
      `substAt 2` re-typing grounds it (`[integer]`) before it is ever a control — so the invariant
      simultaneously ALLOWS `hbody_ref` and guarantees ground runtime args. Recommended threading: a
      runtime-restricted judgment `HasTypeRT` (mirror of `HasType`, `var`/`builtin` arms carry the args
      bound; used by `MStateWf`/`StackWfE`/`StackWfV`) — NOT a premise on `HasType.var` (header-fence,
      rejects `hbody_ref`), and NOT merely goal-type-groundness (irrelevant `getD`-padded args escape
      that — a subtlety the note documents). (2) **The `genAtV_closure_ready_value_node` wrapper is
      designed:** the `inv_lambda` TyEquiv bridge is SOLVED (new additive lemma `instantiateV_genAtV_
      tyEquiv`, via `Ty.substAt_tyEquiv` + `Ty.levels_tyEquiv` preserving the arity-0 check), with one
      residual small subtlety (a `lvl < lvl'` strictness gap: arity-0 short-circuits via
      `closure_typed_of_lambda`; arity≠0 needs `lvl ∈ defnTy.levels ⇒ lvl < lvl'`). (3) **Soundness map
      corrected:** Session C's "103 errors" hid 66 spurious repeats of ONE `<;> simp` error at line 1592
      that MASKED the entire second engine. A one-line de-masking fix (line 1560, 5-tuple→6-tuple
      `mStateWf_E` destructure, applied this session, uncommitted) reveals the TRUE shape: ~25 A-engine
      (`reduceEval`) + ~66 B-engine (`reduceEvalR`/`soundness_evalR`, 2392-3237) mechanical errors, the
      var-preservation blocker in BOTH engines (216-219 and 2943-2945), and the B-engine still on old
      magnitude `sc.instantiate` in places (130/1908/2700-2711/3775). Caveat 5 remains OPEN; Session E
      (with LSP) executes the designed pieces + the ~90-error two-engine grind (order in the note).
      **Progress 2026-07-08 (Session E — the TyEquiv-bridge deliverable LANDED; wrapper strictness gap
      precisely isolated as entangled with the runtime-groundness invariant; no LSP, so `HasTypeRT`/the
      grind deferred), one green additive commit, see
      `progress/2026-07-08-G1-phase6-sessionE-tyequiv-bridge-landed-strictness-gap-isolated.md`:**
      (1) **`instantiateV_genAtV_tyEquiv` implemented** in `Substitution.lean` (Session D's designed
      lemma), builds clean per-file, axiom-clean, additive — `instantiateV` of a level-`ℓ`
      generalization respects `TyEquiv` of the body (arity-0 branch agrees via `Ty.levels_tyEquiv`; else
      via `Ty.substAt_tyEquiv`). (2) **The wrapper strictness gap is sharpened, not closed:** the
      arity-0 branch short-circuits cleanly via `closure_typed_of_lambda`; the arity≠0 branch's
      `lvl < lvl'` is **genuinely undischargeable from `inv_lambda`** when `lvl ∈ εb.levels ∪ retTy.levels`
      but `lvl ∉ argTy.levels` (`inv_lambda`/`HasType.lam` bound only `argTy.levels < lvl'`, nothing on
      the result/effect rows). It needs a levels-bound metatheorem, a rule change (header-fence), or —
      the right fix — the **runtime-groundness invariant itself**: `hasType_subst`'s strict `ℓ < lvl'` is
      exactly what excludes the `lvl' = lvl ∧ lvl ∈ retTy.levels` state, so the wrapper's strictness and
      the var-preservation groundness blocker are the **same obstruction** and must be closed together
      via `HasTypeRT`. Recommendation: land the wrapper *as part of* step 2, not before. (3) `HasTypeRT`
      (24-constructor mirror + RT-inversion) and the ~90-error two-engine grind deferred — both need live
      goal-state and the grind depends on `HasTypeRT` being wired first. `Soundness.lean` left as-found
      (uncommitted; committed HEAD `Soundness.lean` is itself already red across the Phase-6 arc, so the
      additive bridge commit adds no new breakage). Caveat 5 remains OPEN.
      **Progress 2026-07-08 (Session F — Session E's "same obstruction" conjecture REFUTED with a
      machine-checked witness; the two gaps are DECOUPLED), one green additive commit to `Typing.lean`,
      see `progress/2026-07-08-G1-phase6-sessionF-gap2-decoupled-from-groundness-effect-tail-witness.md`:**
      No LSP again, so instead of the blind `HasTypeRT` mirror + grind, this session **tested** Session
      E's central claim (gap 2's `ℓ < lvl'` strictness = gap 1's runtime-groundness blocker, both fixed
      by `HasTypeRT`) against a concrete derivation and **falsified it**. Witness (now a permanent green
      example in `Typing.lean`'s `section Examples`): `\x. perform "op" x` types at ambient level `1`
      with body sublevel `lvl' = 1` (arg type ground ⇒ `lam` does not force `lvl'` up), its type carries
      a generalizable **effect tail** `μ = var 1 0` at level `1`, so `genAtV 1 defnPerf` has `arity ≠ 0`
      while `lvl' = ℓ = 1` (non-strict) — the exact arity≠0/non-strict wrapper branch — and the
      derivation is **fully ground** (the level-`1` tag is `perform`'s freely-chosen `μ`, not any
      instantiation arg). So `HasTypeRT` (which bounds only `var`/`builtin` args) does **not** touch it:
      gap 1 and gap 2 are independent. **True fix for gap 2 (orthogonal to `HasTypeRT`):** `hasType_subst`
      consumes strict `ℓ ≠ lvl` in **exactly one arm** (`let_poly`'s `hne`); the wrapper's conclusion is
      true even here (the body has no `let_poly`, and `perform` is already `μ`-polymorphic). So the fix
      is a `hasType_substAt_le` companion with precondition `ℓ ≤ lvl` + a **derivation-level** side
      condition `NoGenAt ℓ` ("no reachable `let_poly` generalizes at exactly `ℓ`") — NOT a term-only
      predicate (a `let_poly`'s gen-level is its ambient level, derivation-dependent), NOT a rule-strictness
      change (upward level-weakening is unsound, breaks examples, header-fence). Session G can land the two
      pieces (`NoGenAt`/`hasType_substAt_le` for gap 2; `HasTypeRT` for gap 1) **separately and in either
      order**, then the ~90-error grind. `Typing.lean` per-file green (EXIT 0), Substitution/Machine
      re-checked green; no `sorry`, no axioms, no rule change, no statement weakened. Caveat 5 OPEN.
      **Progress 2026-07-08 (Session G1 — gap 2 CLOSED), see
      `progress/2026-07-08-G1-phase6-sessionG1-noGenAt-closes-wrapper-strictness-gap.md`:**
      `NoGenAt`/`hasType_substAt_le`/`genAtV_instantiate_lam_ready_le`/`inv_lambda_noGenAt` landed in
      `Typing.lean`, plus a strengthening lemma `Ty.mem_levels_substAt_strong` in `Scheme.lean` — closes
      gap 2 (the wrapper's strictness obstruction) exactly as Session F diagnosed. Per-file green on
      both files, whole-project `lake build` still fails **only** on `Soundness.lean` (103 errors,
      unchanged count — no new breakage). Still TODO: wire `genAtV_closure_ready_value_node`
      (`Substitution.lean`, untouched this session) to actually call the new keystone; gap 1
      (`HasTypeRT`, var-preservation runtime groundness) remains open and independent; the ~90-error
      mechanical `Soundness.lean` grind untouched. No `sorry`, no axioms, no rule change.
      **Progress 2026-07-08 (Session G2 — gap 1's `HasTypeRT` DESIGNED + LANDED, wired into
      `MStateWf.E`; three green additive commits `379c4d62`/`020e28ff`/`4d5fe793`, see
      `progress/2026-07-08-G1-phase6-sessionG2-hastypeRT-landed-lam-nonrecursion-correction.md`):**
      No LSP (script fallback). Built the runtime-restricted judgment `HasTypeRT` (indexed by a
      `HasType` derivation, à la `NoGenAt` — NOT a 24-constructor standalone mirror, which would force
      re-proving all typing plumbing at RT level). **Design correction over Session D's sketch** (found
      + validated while building): the `lam` arm must **not** recurse into the lambda body, and
      `let_poly` not into its lambda-defn. A lambda body is never evaluated as a control until its
      closure is applied (re-typed by the keystone with ground args); recursing would wrongly reject the
      *legitimate* whole referencing program (`hbody_ref`'s `\w. a w` body has non-ground arg
      `[.var 2 0]`, level 2 ≠ `a.level` 1). Landed in `Typing.lean`: `HasTypeRT` + `inv_var_rt` (the
      exact gap-1 discharge — extracts the args side-condition `∀ t ∈ args, ∀ l ∈ t.levels,
      l = 0 ∨ l = s.level` that `envwf_lookup`'s conditional `hvty` needs) + `inv_builtin_rt` +
      `hasTypeRT_lambda` (any lambda control is RT) + RT-inversions `inv_app_rt`/`inv_let_rt`
      (preservation plumbing). Non-vacuously validated: RT of a lambda whose body is exactly
      `hbody_ref` holds via `HasTypeRT.lam` (no body premise). Wired into `Machine.lean`: `MStateWf`'s
      `.E` case now carries `HasTypeRT hty` of the control; `mStateWf_initial` gains a `HasTypeRT h`
      premise (entry-point instance of the invariant). **Genuine finding on the "runtime args always
      ground" hypothesis (Session D flagged "verify carefully"):** it holds only as a *threaded runtime
      property* — the initial program is RT for closed programs of **ground result type** (an open-result
      program like `id id` has non-ground top-level var args and is legitimately non-RT, hence
      `mStateWf_initial`'s RT premise rather than a universal lemma), and preservation must
      **re-establish** it at each step (via `hasTypeRT_lambda` / the keystone's `substAt`-grounding for
      applied closures). Per-file green (Typing/Machine/Runtime/Generation/Substitution), axioms
      `[propext]` only, no `sorry`. **Still open for the next (LSP) session:** (a) StackWf /
      StackWfE / StackWfV **frame-RT threading** (Arg/Assign frames store expressions that become
      controls — needed for preservation to re-establish `MStateWf.E`'s RT across frame pops; entangled
      with the Soundness preservation proof, deferred); (b) wire `genAtV_closure_ready_value_node`
      (`Substitution.lean`) to the Session-G1 keystone; (c) the ~90-error two-engine `Soundness.lean`
      grind (var-preservation now discharges via `inv_var_rt`). Caveat 5 OPEN.
      **Progress 2026-07-08 (Session G3 — step 2 `genAtV_closure_ready_value_node` LANDED; step-1
      frame-RT cascade fully mapped with its linchpin isolated; see
      `progress/2026-07-08-G1-phase6-sessionG3-wrapper-landed-step1-cascade-mapped.md`):** No LSP.
      One green additive commit (`cb598ce0`, `Substitution.lean`). (1) **`genAtV_closure_ready_value_node`**
      — the lambda-*node*-derivation closure-readiness wrapper the `let_poly` preservation cases call:
      from `HasType lvl Γ ⟨.Lambda x lbody, la⟩ defnTy ε` + `NoGenAt lvl h` + `PolyAboveFV`/`CtxWfV`/
      `EnvWf`, produces `∀ args, (level-bounded) → HasTypeV (Value.Closure ..) ((genAtV lvl
      defnTy).instantiateV args)`, composing `inv_lambda_noGenAt` + the Session-G1 non-strict keystone
      `genAtV_instantiate_lam_ready_le` + `HasTypeV.closure` + `instantiateV_genAtV_tyEquiv`. `NoGenAt`
      is a genuine premise (the non-strict `lvl'=lvl` `perform` branch needs it); the working-tree
      A-engine call site (`Soundness.lean:243`) omits it, so step 3 must additionally supply it.
      (2) **Step 1 (frame-RT threading) precisely mapped, deferred.** Confirmed dischargeable in
      Soundness (`inv_app_rt`/`inv_let_rt` on the `MStateWf.E` `hrt` supply the frame RT witnesses),
      but the cascade forces `HasTypeRT` onto `StackWf.assign`/`.arg` **and** `StackSegWf.assign`/`.arg`
      (Runtime.lean's mutual block with `HasTypeV`). All mechanical **except** `stackSeg_input_conv`,
      which rebuilds the stored assign body via `hasType_ctxHead_conv` and so needs a new **24-arm
      derivation-indexed companion `hasTypeRT_ctxConv`** (RT-preservation under `hasType_ctxConv`) —
      the linchpin, needs live goal-state, deferred. Recommended next-session order: land
      `hasTypeRT_ctxConv` (Typing.lean, self-contained) → thread RT into StackSegWf (Runtime) → into
      StackWf/StackWfV/StackWfE (Machine) → then the step-3 Soundness grind. (3) **Step 3 confirmed
      not one-session-reachable blind:** the working-tree B-engine (`reduceEvalR`, ~2392–3237) is
      structurally mangled (unknown `StackWfB`/`stackWfB_assign_inv`, a "Function expected" destructure
      cascade, and a pre-existing uncommitted `sorry` at :2880 — never committed), not mere mechanical
      residue. (4) **Sharpest open design question:** whether `NoGenAt`-at-the-call-site is a runtime
      fact that must be threaded as an `MStateWf` invariant (gap-2 analog of gap-1's `HasTypeRT`) —
      candidate: strengthen the already-wired `HasTypeRT` control witness to also carry `NoGenAt`.
      Soundness.lean left exactly as found. Caveat 5 OPEN.

      **Progress 2026-07-08 (Session G4 — step 1 linchpin `hasTypeRT_ctxConv` LANDED; step 2 frame-RT
      threading LANDED across Runtime+Machine; step 3 Soundness grind assessed, gap-2 provenance
      pinned; see `progress/2026-07-08-G1-phase6-sessionG4-steps1-2-landed.md`):** No LSP. Two green
      additive commits. (1) **`hasTypeRT_ctxConv` + `hasTypeRT_ctxHead_conv`** (`Typing.lean`,
      commit `4d232f7b`) — the RT companion to `hasType_ctxConv`. Because `HasTypeRT` is indexed by the
      *specific* derivation and `hasType_ctxConv`'s output is an opaque recursor application that
      case-splits on the runtime binder lookup, it is stated **bundled** as `∃ h', HasTypeRT h'`
      (rebuilding a fresh converted derivation + its RT arm-for-arm, 21 RT arms), NOT as
      `HasTypeRT (hasType_ctxConv h …)`. The var conv-subcase is discharged because both `.mono σ` and
      `.mono σ'` have `.level = 0`, so the args-level side-condition transports verbatim; `lam`/`let_poly`
      defn subterms reuse the plain `hasType_ctxConv`. (2) **Step 2 frame-RT threading** (`Runtime.lean`
      + `Machine.lean`, commit `c223c4c1`) — added a `HasTypeRT hbody`/`HasTypeRT harg` field to the
      `assign`/`arg` constructors of both `StackSegWf` and `StackWf`; threaded through
      `stackSeg_conv_output`/`_input_conv` (the latter via `hasTypeRT_ctxHead_conv`)/`_append`,
      `stackSeg_toStackWf`, `stackWf_assign_inv`/`_arg_inv` (now surface the RT existentially), the
      `StackWfV`/`StackWfE` Assign heads, and `stackWf_toStackWfV`/`E`, `stackWfE_toStackWf`/
      `_lambda_step`/`_value_step`. Both files + all non-Soundness deps per-file green; no `sorry`, no new
      axioms. (3) **Working-tree Soundness.lean re-characterized** (correcting Session G3's note): the
      uncommitted diff is only **53 lines** of *legit* level-tag migration (not "structurally mangled"):
      `StackWfB` **IS defined** at :2443 (T7 groundwork — not an unknown identifier), and there is
      **NO `sorry`** anywhere in the current working tree. 103 cascading errors from an *incomplete*
      migration (starts at :34 `mStateWf_E` — still out of sync with the RT-carrying `MStateWf.E`).
      (4) **Gap-2 provenance pinned.** The `let_poly` preservation case (`Soundness.lean:243`) needs
      three facts `genAtV_closure_ready_value_node` requires but that are absent at the runtime site:
      `hℓ : lvl ≠ 0` (solvable: run `soundness` at a fixed ambient `lvl ≥ 1`, threaded via `MStateWf`),
      `hΓpa : PolyAboveFV lvl Γ ⟨.Lambda …⟩` (candidate: derive from `CtxWfV`/`PolyAbove`, or thread as
      an `MStateWf` invariant), and the sharp one `hng : NoGenAt lvl hdefn` (the gap-2 analog of gap-1's
      `HasTypeRT` — most likely must become a new `MStateWf.E` invariant, e.g. strengthen the wired
      `HasTypeRT` witness to also carry `NoGenAt` of the control). Full-green Soundness is a multi-session
      grind + this gap-2 design resolution; **not** reachable blind this session. Soundness.lean left as
      found. Caveat 5 OPEN.

      **Progress 2026-07-09 (Session G5 — NoGenAt-provenance question DECOMPOSED, prev session's
      leading hypothesis REFUTED; one green additive commit `8339200d` to `Typing.lean`; see
      `progress/2026-07-09-G1-phase6-sessionG5-noGenAt-of-lt-provenance-decomposed.md`):** No LSP.
      (1) **Route A refuted.** "Strengthen `HasTypeRT.let_poly` to carry `NoGenAt lvl hdefn`" (Session
      G4's lead) is **not** universally true for well-typed runtime let_poly controls and would
      *narrow* soundness coverage: witness a valid derivation `\x. pair (g[a:=.var lvl 0]) (let h=\y.y
      in h)` — `defnTy` mentions `lvl` (`arity≠0`) via an internal level-`lvl` instantiation arg AND an
      inner `let_poly` generalizes at exactly `lvl`, so `NoGenAt lvl hbody` is *false*, yet the current
      un-strengthened `HasTypeRT` (which does NOT recurse into defn-lambda bodies) still accepts it. NB
      the Phase-7 target `let f=\x.(let g=\y.y in g x) in …` is NOT a counterexample (its `defnTy` is
      ground, `arity 0`). (2) **Correct decomposition of the wrapper's `NoGenAt lvl hbody` need:**
      `arity 0` → `closure_typed_of_lambda`, no NoGenAt (covers all ground-generalization nested lets);
      `lvl' > lvl` → NoGenAt **for free** via the new `noGenAt_of_lt`; residual `arity≠0 ∧ lvl'=lvl`
      genuinely needs it (benign `defnPerf` — derivable; pathological Route-A shape — unprovable from the
      site's data). (3) **Landed `noGenAt_of_lt`** (`Typing.lean`, commit `8339200d`): a HasType
      derivation at level `lvl` satisfies `NoGenAt ℓ` for every `ℓ < lvl` (ambient levels only increase
      on descent). Clean 21-arm induction, non-narrowing, per-file green, axioms `[propext]`, no
      `sorry`. (4) **Full green confirmed NOT blind-reachable** (independently, not time): the residual
      3b corner needs a genuine **level-normalization theorem** (nested `let_poly` at strictly
      increasing levels — collapses the residual into the `lvl'>lvl` case with ZERO soundness narrowing)
      OR a deeper let_poly-defn runtime invariant (narrows coverage); plus the whole **B-engine**
      (`~2694–3862`) is still on old non-level-tagged `HasType`, and `soundness_evalR` still carries the
      old statement (needs `HasTypeRT` premise + nonzero ambient level). Soundness.lean left as found.
      Caveat 5 OPEN.

      **Progress 2026-07-09 (Session G6 — `NoGenAt` shown to be a JUDGMENT-level property (proof
      irrelevance), correcting the G5 framing; residual-corner witness shown to satisfy `NoGenAt` via
      normalization; one green additive commit `865d8ac0` to `Typing.lean`; see
      `progress/2026-07-09-G1-phase6-sessionG6-noGenAt-proof-irrelevant-normalization.md`):** No LSP.
      (1) **Structural correction.** `NoGenAt ℓ` is a `Prop` indexed by a `HasType` *proof*, and
      `HasType` is a `Prop`, so definitional proof irrelevance makes `NoGenAt ℓ h₁ ≡ NoGenAt ℓ h₂`
      whenever `h₁,h₂` type the same judgment. Hence `NoGenAt ℓ h` means "the *judgment* admits SOME
      derivation with no reachable `let_poly` generalizing at `ℓ`" — NOT a fact about the specific
      runtime derivation. The G5 note's residual-corner analysis (which treated `NoGenAt` as derivation-
      specific and concluded an external witness is required) is thereby **superseded**: the wrapper's
      `NoGenAt lvl hdefn` premise only needs *a* good derivation of the same lambda judgment, e.g. one
      typing the body at a higher sublevel. A blocking `cases`/inversion on `NoGenAt` is impossible for
      the same reason, so the "route-a-literal is false" ¬`NoGenAt` claim is itself false. (2)
      **Machine-checked on the hardest known residual-corner witness** `\x.(let h=\y.y in perform "op"
      x)` (types at `defnPerf`: `arity≠0` via the effect tail `μ=var 1 0`, inner `let_poly` present):
      it ALSO types with `lvl'=2` (inner `let_poly` at level `2 > 1`), giving `NoGenAt 1` via
      `noGenAt_of_lt`; by proof irrelevance this *also* proves `NoGenAt 1` of the un-normalized `lvl'=1`
      derivation the runtime hands us (`advPerf_lvl1_noGenAt := advPerf_lvl2_noGenAt` type-checks). So
      **route (a) HOLDS for this witness** — the supposed adversary is not adversarial. (3) **Open
      frontier pinned precisely.** The witness's inner `let_poly` (`h : int→int`, ground) is *vacuous*
      (`genAtV n (int→int)` is `arity 0` ∀`n`), so bumping `lvl'` is a free renaming. The genuinely
      general theorem needs level **RENAMING** (a `≥ℓ`-level shift on the whole derivation), NOT mere
      weakening — `HasType n Γ e τ ε → HasType (n+1) Γ e τ ε` (fixed `Γ,τ,ε`) is FALSE once an inner
      `let_poly` generalizes real level-`n` vars, since `genAtV n d ≠ genAtV (n+1) d`. The argument that
      renaming preserves observable types (inner generalization vars are bound-and-gone; instantiation
      results depend on args, not gen levels; the outer fixed `defnTy` occurrences are separate free
      occurrences the inner shift never touches) strongly indicates route (a)-via-renaming is TRUE in
      general, but the metatheorem itself (21-arm shift induction + `genAtV`/`instantiateV`-shift
      commutation) is multi-session and wants live LSP. The right integration is to fold that
      normalization *into* `genAtV_closure_ready_value_node`, dropping its `NoGenAt lvl h` premise so the
      Soundness site never supplies it. `Typing.lean` per-file green, no `sorry`, no new axioms.
      Soundness.lean left as found. Caveat 5 OPEN.

      **Progress 2026-07-09 (Session G7 — the renaming metatheorem's residual corner SHARPENED: a
      uniform tag-shift is ill-defined there, the entanglement is not excluded by `HasTypeRT` and DOES
      occur in sound RT-valid derivations, precise obstruction = same-level non-commutation; one green
      additive commit `c50bbfe9` to `Scheme.lean`; see
      `progress/2026-07-09-G1-phase6-sessionG7-renaming-entanglement-sharpened.md`):** No LSP.
      (1) **A tag-uniform level shift is ILL-DEFINED in the residual corner** (`arity≠0 ∧ lvl'=lvl`).
      The OUTER lambda's gen vars (level `lvl` in `retTy`/`εb`, quantified by `genAtV lvl defnTy`) must
      STAY at `lvl`; the INNER `let_poly`'s gen vars (also level `lvl`) must MOVE to a fresh `f` to
      decouple from the keystone's `substAt lvl`. Both are the identical leaf `var lvl i` —
      indistinguishable by tag — so no `substAt lvl (·↦var f)` moves one and fixes the other. This
      corrects G6's "renaming is a straightforward `≥ℓ`-shift induction, likely TRUE": as a *global tag
      shift* it is not well-defined. `CtxWfV lvl Γ_inner` localizes the inner vars to the let's subtree
      but does NOT keep them out of the let's RESULT type. (2) **The escape into the result type occurs
      in sound, `HasTypeRT`-valid derivations.** Witness `\x. (let h = \z.z in h) : α → (β → β)`: the
      inner `id`'s gen var re-surfaces in `retTy = β→β`, giving `arity(genAtV lvl defnTy) ≥ 1` AND an
      inner `let_poly` at exactly `lvl`; the let-body is the var `h` with args `[var lvl 0]`
      (`level = h.level`), so `HasTypeRT.var` accepts it — gap-1 groundness does NOT exclude the escape.
      (Independently re-confirms G5's Route-A refutation.) (3) **The precise mechanical obstruction is
      same-level non-commutation.** The escape is semantically benign (specializing the inner `id` when
      the outer lambda is called is sound), but pushing `substAt lvl σ` through an inner `genAtV lvl`
      node requires the outer-specialization `σ` and the inner-instantiation `args` to commute at the
      SAME level, which they do not (opposite application orders) — exactly why the `let_poly` arm
      demands `ℓ ≠ lvl`. (4) **Re-characterized correct metatheorem:** NOT a global shift, but a
      **per-`let_poly` fresh-level normalization** — rewrite so every `let_poly` generalizes at a
      globally-unique level `>` every interface level and every sibling gen level; then tags identify
      binders, `substAt` never collides, and `noGenAt_of_lt` discharges the wrapper premise for free.
      Induction allocates fresh per node top-down; per-node step is `substAt oldLvl (·↦var freshLvl)`,
      bookkeeping = the new `substAt_substAt_same` + `substAt_substAt_comm`. Multi-session, wants LSP.
      (5) **Landed `Ty.substAt_substAt_same`** (`Scheme.lean`, `c50bbfe9`): same-level substitution
      composition, unconditional — the renaming-step building block. Per-file green, no `sorry`, axioms
      unchanged. Soundness.lean left as found. Caveat 5 OPEN.

      **Progress 2026-07-09 (Session G8 — G7's freshen/mono-ize split CORRECTED: the escaping inner
      `let_poly` is freshenable via re-instantiation, so the mono-ize branch is unnecessary; the
      residual corner reduces to a SINGLE level-raising lemma; one green additive commit `68f207d3` to
      `Typing.lean`; see
      `progress/2026-07-09-G1-phase6-sessionG8-escape-freshenable-reinstantiation.md`):** No LSP.
      (1) **The "escape ⇒ mono-ize" dichotomy is imprecise.** G7's escape witness
      `\x. (let h = \z.z in h)` (inner gen var re-surfaces in `retTy = β→β`, `arity ≠ 0` — the genuinely
      hard corner, unlike `advPerf`'s vacuous ground inner let) is **freshenable**, not requiring
      mono-ize. The level-`lvl` var in `retTy` is produced by *instantiating* the inner scheme at an
      outer/lower variable, and that argument is chosen independently of the inner scheme's gen level —
      so the inner level moves fresh while the identical argument reproduces the identical `retTy`.
      Machine-checked: `escLam_lvl1` (inner `let_poly` at level `1`, escaping; `genAtV 1 escDefnTy`
      `arity 2`) and `escLam_lvl2` (inner `let_poly` freshened to level `2`, use re-instantiated at the
      identical `[var 1 0, var 1 0]`) prove the **identical judgment**; `NoGenAt 1` holds via
      `noGenAt_of_lt` + proof irrelevance, **no** mono-ize / principal-types step. Landed as permanent
      green witnesses in `section Examples`. (2) **Why re-instantiation dissolves G7's representation
      wall.** The correct transformation is not a tag-uniform *type substitution* (ill-defined, G7
      Finding 1) but a *re-elaboration*: re-tag the inner node's own gen level to fresh on its **defn
      subtree only** (well-defined, since `CtxWfV lvl Γ` — `Typing.lean:51`, `∀ b ∈ Γ, ∀ l ∈
      b.2.body.levels, l < ℓ` — forbids any level-`lvl` var in the *context*, so the only level-`lvl`
      vars in the defn are this node's own gen vars) and re-instantiate each use at the same arguments.
      A use's result type depends only on its instantiation **arguments** (outer/ground, unchanged),
      never on the inner gen level (bound-and-gone), so `retTy` is preserved; the interface is never
      substituted at `lvl`, so no tag collision. (3) **Re-characterized metatheorem (supersedes G7's
      split):** the residual corner needs a **single** level-raising lemma, not a two-branch case split —
      `hasType_raise_sublevel : HasType lvl Γ e τ ε → CtxWfV lvl Γ → HasType (lvl+1) Γ e τ ε` (same
      `Γ`/`τ`/`ε`), whose `let_poly` arm re-tags `genAtV lvl d ↦ genAtV (lvl+1) (substAt lvl (·↦var
      (lvl+1)) d)` on the defn and threads identical args through the body's `var` uses (commutation =
      `substAt_substAt_same` + `substAt_substAt_comm`); `CtxWfV lvl Γ` keeps the raise from ever
      touching a context scheme. One raise turns the wrapper's residual `lvl' = lvl` into `lvl' > lvl`,
      whence `noGenAt_of_lt` discharges `NoGenAt lvl` with zero soundness narrowing. Cleaner/smaller
      than G7's split (no mono-ize, no escape predicate, no global fresh-level allocation). **Not proved
      this session** — statement pinned, `let_poly`-arm mechanism validated on the witness; the 21-arm
      induction (genAtV/instantiateV re-instantiation commutation) is high-risk under batch `lake env
      lean`, wants live LSP. Per-file green, no `sorry`, axioms `[propext]`. Soundness.lean left as
      found. Caveat 5 OPEN.
      **Progress 2026-07-09 (Session G9 — sharpens G8's target; commit `8696f55b`, Scheme.lean; see
      `progress/2026-07-09-G1-phase6-sessionG9-raise-sublevel-induction-insufficiency.md`):** three
      findings correcting G8's "single one-liner raise" framing. **(1)** Plain `induction h` is
      *provably insufficient* for the `let_poly` arm: the recursor fixes the stored scheme
      `genAtV lvl defnTy` in `ihbody`, but a `let_poly` at the raised ambient `lvl+1` **requires** the
      stored scheme re-tagged to `genAtV (lvl+1) _`, and no rule accepts a stored scheme generalizing
      *below* the ambient — so the arm needs a dedicated `hasType_subst`-scale re-instantiation
      sub-lemma (a "generalization-level shift on a context binding" that rewrites the let-bound var's
      *uses*), NOT a one-liner over the two commutation facts. **(2)** Two edge cases the single
      `escLam` witness does not exhibit: (a) *under-application* of the poly var leaks a floating
      level-`lvl` quantifier var into `bodyTy` (e.g. `let h=\z.z in h` at `args=[]`), so the raised
      derivation must **explicitly extend** args with `var lvl i` to reproduce it (`escH_body`'s
      `[var 1 0, var 1 0]` is this extension done by hand); (b) *pre-existing* level-`(lvl+1)` vars in
      `defnTy` (leakable when its body sublevel `≥ lvl+2`) make the naive relabel `lvl→lvl+1` *inflate*
      `genAtV`'s arity, so the internal relabel must target a genuinely **fresh** level `f` (> all
      levels in the derivation), not `lvl+1` — the ambient-raise `+1` and the inner-gen-relabel are
      *independent*, which G8's "single +1" conflated. Plus the `genAtV` arity=count-vs-index wart:
      `args'` coverage must exceed the max level-`ℓ` *index* in `d`, not the arity. **(3)** The right
      wire-in shape drops `NoGenAt` from `genAtV_closure_ready_value_node` entirely (raise the lambda
      *body* when `lvl'=lvl`, then use the *strict* keystone `genAtV_instantiate_lam_ready`); `NoGenAt
      lvl h` for the runtime's own `h` is genuinely *not* derivable (false for a colliding derivation;
      proof irrelevance cannot cast across the differing ambient-level index). Banked green:
      `Scheme.substAt_congr_freeVarsAt` (level-native analog of `subst_congr_free`), the congruence the
      re-instantiation equality consumes. Per-file green, no `sorry`, axioms unchanged. Soundness.lean
      left as found. Caveat 5 OPEN.

      **Progress 2026-07-09 (Session G10 — shortcut evaluated & REJECTED with proof; G9 rec 1 LANDED,
      commit `63ed5a67`, Scheme.lean; see
      `progress/2026-07-09-G1-phase6-sessionG10-reinstantiation-equality-shortcut-rejected.md`):** No
      LSP/MCP (canary failed). **(1) The finding-3 shortcut does NOT sidestep the sub-lemma.** The
      outer generalization level is *pinned* at `lvl` by `HasType.let_poly` (its stored scheme is
      `genAtV lvl defnTy` — not a free choice), and the strict keystone `genAtV_instantiate_lam_ready`
      requires generalization-level `< body-sublevel`. In the residual corner `lvl' = lvl` the only
      escapes — raise the body's sublevel, relabel `defnTy`'s gen level to a fresh `f`, or shift the
      body's levels up — *all* re-tag the body's inner `let_poly` schemes (`genAtV oldlvl → genAtV
      newlvl`), which is exactly G9 Finding 1's wall; "pick a fresh high level via `Nat` unboundedness"
      fails because a fresh level *above* the body breaks the keystone's `<` and a fresh level *below*
      still collides with the body's inner gens at `lvl`. Proof-irrelevance (G6) reframes the target
      to "*exhibit some* re-derivation of the same lambda judgment with `NoGenAt lvl`", but constructing
      that re-derivation IS the raise — no free lunch. Conclusion: the generalization-level-shift
      sub-lemma is *irreducibly* required; recorded as a genuine obstruction, not forced. **(2) Banked
      green (G9 rec 1, the pure re-instantiation equality):** `Ty.length_filter_levels_relabel`
      (relabel `ℓ→f` preserves the generalized-occurrence count — arity-preservation core),
      `Ty.substAt_relabel_getD` (body-level heart: re-substituting the `f`-relabel at `args` reproduces
      the `ℓ`-substitution, under a *coverage* hypothesis discharging G9 Finding 2(a)/(c)), and
      `Scheme.instantiateV_genAtV_relabel` (scheme-level: `genAtV ℓ d` and `genAtV f (relabel d)`
      instantiate at the same `args` to the same type — the `escLam_lvl1/lvl2`, `advPerf_lvl1/lvl2`
      witnesses are its by-hand `arity ≤ 2` instances). Per-file green (Scheme + Typing), no `sorry`,
      axioms unchanged. Soundness.lean left as found. **Remaining to close Caveat 5:** the
      `hasType_subst`-scale generalization-level-shift induction on the body derivation (G9 rec 2),
      whose `var`/`builtin` arms now consume `substAt_relabel_getD`/`instantiateV_genAtV_relabel` with a
      constructed coverage-respecting `args'`, and whose `let_poly` arm re-tags via the same; then
      wire-in per G9 finding 3's shape (drop `NoGenAt` from `genAtV_closure_ready_value_node`). Caveat 5
      OPEN. Wants live LSP — this is error-prone under batch `lake env lean`.
      **Progress 2026-07-09 (Session G11 — the raise pinned as a TWO-theorem re-elaboration; a natural
      `hasType_subst` reuse REFUTED; var-arm padding banked, commit `26e1f566`, Scheme.lean; see
      `progress/2026-07-09-G1-phase6-sessionG11-raise-two-theorem-architecture-hasTypeSubst-refuted.md`):**
      No LSP/MCP. Sharpens G10's "single generalization-level-shift sub-lemma" into a precise architecture.
      **(1) The wrapper only needs an ambient RAISE** (no `NoGenAt` premise): raise the `inv_lambda` body
      `hbody : HasType lvl' … lbody retTy εb` to any fresh `L > lvl` keeping context/`retTy`/`εb`
      **literally fixed**, then either `noGenAt_of_lt` (free `NoGenAt lvl`) or — cleaner — the STRICT
      keystone `genAtV_instantiate_lam_ready` directly (`lvl < L`). `CtxWfV lvl' ((x,.mono argTy)::Γ)`
      holds from `hΓwf`+`hfv`. Drops `hng`/`hΓpa` from `genAtV_closure_ready_value_node`. **(2) The raise
      keeps the conclusion type LITERALLY FIXED**, resolving G7 Finding 1's tag conflation: all conclusion
      types carry only *ambient* level tags (inner-gen tags are bound-and-gone, re-entering only via
      instantiation args), and the `var` arm absorbs the collision by *padding args* — the escaped var
      (from an unchanged arg) stays, the inner-gen var (in the relabeled *scheme body*) moves, same tag,
      different syntactic position, no uniform type-function. **(3) The `let_poly` arm needs a SECOND,
      coupled theorem — and `hasType_subst` CANNOT be it.** Raising a `let_poly` (ambient=genlevel=stored
      level, all tied) forces the stored scheme to `genAtV (k+o) (substAt k (·↦var(k+o)) defnTy)`, so
      `hdefn'` must carry the *relabeled* type, not the fixed one. `hasType_subst`/`hasType_substAt_le`
      require `σ`'s range levels `∈ {0,ℓ}` (the *instantiation* direction), which **excludes** a
      relabel-to-a-fresh-level map (`var (k+o)`, level `∉ {0,k}`) — a genuine refutation of the obvious
      "compose with existing subst" shortcut. A dedicated **fresh-level relabel re-typing theorem**
      (`hasType_subst`'s 21-arm shape with the `{0,ℓ}` precondition replaced by *freshness*, discharging
      `var` via the already-general `substAt_instantiateV_scheme`, and bumping the ambient — mutually
      recursive with the type-fixed main raise) is required. **(4) Freshness** wants a threaded global cap
      `LevelsBelow N h` (a `NoGenAt`-shaped inductive) + `∃ N`, so a single offset `o ≥ N` relabels every
      node freshly. **Banked green (commit `26e1f566`):** `instantiateV_congr_getD` (instantiation depends
      on `args` only through the padded lookup) and `instantiateV_pad_default` (padding with default leaves
      is instantiation-invariant, extends length arbitrarily to meet coverage) — the constructive half of
      the `var` arm, so it keeps the conclusion type fixed while the looked-up scheme is relabeled.
      Per-file green (Scheme), axioms unchanged, no `sorry`. Soundness.lean left as found. **Remaining:**
      `LevelsBelow`+`∃N`; `raiseCtx`+lemmas; the two mutually-recursive 21-arm raise inductions;
      wire-in (drop `NoGenAt`, strict keystone); then the Soundness grind + Phase 7. Architecture now
      precise and math de-risked; the two inductions want live LSP goal-state. Caveat 5 OPEN.
      **Progress 2026-07-09 (Session G12 — THREE of G11's four remaining pieces landed; relabel
      re-entrancy insight; three green additive commits `5413665c`/`fe30f615`/`a9a80052`, Typing.lean;
      see `progress/2026-07-09-G1-phase6-sessionG12-levelsBelow-raiseCtx-varArm-landed-relabel-
      reentrancy.md`):** No LSP/MCP (canary failed). **(1) `LevelsBelow N h` + `LevelsBelow.mono` +
      `exists_levelsBelow`** (`5413665c`) — G11's threaded global freshness cap as a `NoGenAt`-shaped
      21-arm inductive (only the `let_poly` arm bounds `defnTy.levels < N`); `∃N` by per-node max. A
      single offset `o ≥ N` relabels every gen level to a fresh `k+o ∉ defnTy.levels`. **(2) `raiseScheme
      t o` + `raiseCtx t o` + `raiseCtx_lookup`/`_fix`/`raiseScheme_mono`/`_of_level_lt`** (`fe30f615`) —
      `raiseScheme t o (genAtV k d)` for `k ≥ t` = `genAtV (k+o) (substAt k (·↦var(k+o)) d)` (the exact
      input of `instantiateV_genAtV_relabel`), identity below `t`; `raiseCtx_fix` fixes a
      below-threshold context. **(3) `raiseScheme_genAtV_instantiateV`** (`a9a80052`) — the var-arm crux,
      now a *concrete proven lemma* (G11 had prose only): explicit padded `args' = args ++ (range extra).
      map (var k …)` under which `(raiseScheme t o (genAtV k d)).instantiateV args' = (genAtV k d).
      instantiateV args`, composing `instantiateV_pad_default` + `instantiateV_genAtV_relabel`, freshness
      from `N ≤ o`. Concretely decouples the escaped var (stays at `k`, in `args`) from the scheme body's
      gens (move to `k+o`). **(4) New structural insight (sharpens G7 Fdg 3):** `hasType_relabel_raise`,
      called on a `let_poly`-defn (lambda at ambient `k`, relabel level `k`), is **NOT** a clean
      distinct-level induction — a ground-arg defn's `lam` body sits at sublevel exactly `k` and may hold
      an inner `let_poly` at exactly `k`, so the relabel-at-`k` re-collides same-level, *one layer down*.
      The two theorems are therefore **re-entrant on the collision**, so the `mutual` block's termination
      must be **structural on the derivation**, not a level measure. This also proves a single "relabel
      ≥ t in both type and derivation" theorem cannot subsume both (an escaped threshold-level tag must
      STAY via the var arm while a sibling `let_poly` at that level MOVES — decoupled only structurally).
      **Remaining (the LAST piece):** the two mutually-recursive 21-arm inductions `hasType_raise`
      (type-fixed) / `hasType_relabel_raise` (fresh-level, relabel level = node gen level), context
      invariant `CtxLevelsBelow N Γ` (bind-BODY levels < N, not `CtxWfV`), as a `mutual` block with
      derivation-structural `termination_by`; then wire-in (`raiseCtx_fix` for the fixed context, strict
      keystone) + the Soundness grind + Phase 7. All statements + arm recipes recorded in the note. Wants
      live LSP. Per-file green (Typing), axioms unchanged, no `sorry`. Soundness.lean left as found.
      Caveat 5 OPEN.
      **Progress 2026-07-09 (Session G13 — the G12 single-relabel-level blueprint found INSUFFICIENT;
      uniform `raiseTy` + bridge landed, commit `ddaf2e35`, Scheme.lean; see
      `progress/2026-07-09-G1-phase6-sessionG13-raiseTy-two-modes-need-distinct-context-raise.md`):** No
      LSP/MCP (canary failed). Attempting to build the two mutually-recursive raise inductions surfaced a
      genuine architectural subtlety G12's single-level-`k` `hasType_relabel_raise` does not resolve.
      **(1)** `raiseCtx`/`raiseScheme` is **mode-independent and single-level-per-binding**
      (`raiseScheme t o (genAtV k' d) = genAtV (k'+o) (substAt k' (·↦var(k'+o)) d)` relabels the body
      only at that binding's *own* gen level `k'`), and both modes must share it. **(2)** A relabel-`k`
      descent past an inner binding at `k' ≠ k` (both `≥ t`) whose stored body carries **foreign level-`k`
      content** (outer relabel-`k` gens instantiated into the inner defn) needs a **double** relabel
      `substAt k' (substAt k d)` of that body, but the shared `raiseCtx` supplies only the `k'` half — so
      a var-use looking it up produces un-relabeled level-`k` content, contradicting the relabel-`k`
      conclusion. **(3)** This is inherited by the *type-fixed* main raise via its `let_poly` arm (which
      delegates the defn re-typing to the relabel companion at the node's gen level `j`). **(4)** There is
      **no pure type-function** formulation: at one level `ℓ ≥ t` a tag is either a bound-gen (MOVES) or
      an escaped-arg (STAYS), indistinguishable by tag; the type-fixed raise's conclusion keeps all `≥ t`
      tags (all escaped-free there) while the relabel companion's conclusion moves all `≥ t` tags — so the
      relabel conclusion is really `raiseTy t o τ` (uniform, all `≥ t` move), **not** single-level
      `substAt k`, and the two modes need **different context-raise ops** (raise = single-level padding;
      relabel = `raiseTy` per binding). **(5)** The wrapper is not *immediately* broken (`CtxWfV lvl Γ`
      forces top-level context `< t`, so both ops = identity there); the conflict can only surface at
      nesting depth `≥ 2`. **Banked green (`ddaf2e35`):** `Ty.raiseTy t o` (uniform relabel of every
      `≥ t` level), `raiseTy_eq_self_of_levels_lt` (identity below threshold), and the crux
      `raiseTy_eq_substAt_of_single` (single-level `substAt k` = uniform `raiseTy t o` exactly when the
      type's only `≥ t` level is `k`). **Recommended next step:** migrate the relabel companion to the
      `raiseTy`-uniform form (its var-arm commutation needs no arg-padding — getD defaults match
      automatically since `raiseTy t o (var k i) = var (k+o) i`), then resolve the shared-context fork
      (prove the residual bodies never nest a foreign-cross-level `let_poly`, so single = uniform via
      `raiseTy_eq_substAt_of_single`; the two modes stay irreducibly distinct because the residual case's
      `lvl ∈ retTy.levels` — level exactly `t` — WOULD move under `raiseTy`). Per-file green (Scheme),
      axioms unchanged, no `sorry`. Soundness.lean left as found. Caveat 5 OPEN. Wants live LSP.

      **Progress 2026-07-09 (Session G14 — answered "is the narrow version sufficient?": NO, but
      re-targeted the crux to a strictly weaker, obstruction-free existence statement; no commit; see
      `progress/2026-07-09-G1-phase6-sessionG14-narrow-insufficient-strictify-is-real-target.md`):** No
      LSP (canary failed). Traced the ACTUAL call site (Soundness.lean:243) instead of the maximal-
      generality raise theorem. **`genAtV_closure_ready_value_node` (Substitution.lean:167) is already
      proven and consumes NO raise/relabel theorem** — it uses the `NoGenAt` + `..._le` keystone route.
      Its three still-open premises at the call site: **(1)** `hlvl0 : lvl ≠ 0` (easy — enter soundness at
      ambient `≥ 1`); **(2)** `hΓpa : PolyAboveFV lvl Γ ⟨.Lambda…⟩` (mostly easy — from `CtxWfV lvl Γ`
      via a new `polyAboveFV_of_ctxWfV`, residual `s.level ≠ 0` needs gen-levels-`≥ 1`, same invariant as
      (1)); **(3)** `hng : NoGenAt lvl hdefn` — **THE CRUX** (call currently mis-passes `hdefn` here).
      **NoGenAt lvl hdefn is genuinely the general problem:** `noGenAt_of_lt` needs `ℓ < root-level`, but
      here both `= lvl`; via `inv_lambda_noGenAt` it reduces to `NoGenAt lvl hbody` at the defn lambda's
      body sublevel `lvl'` (`lvl ≤ lvl'`, **non-strict**), free iff `lvl' > lvl`, and the declarative
      system permits `lvl' = lvl` with an inner same-level `let_poly` — which soundness (quantifying over
      all `h`/`hrt`) must handle. The task's "raise past one binder under `CtxWfV`" narrowing *is* the G13
      two-modes conflict, not an escape. **Sharper target isolated (route (a), G7/G8, never lifted to a
      theorem):** `HasType` is a `Prop`, so by proof irrelevance `NoGenAt lvl hdefn = NoGenAt lvl hdefn'`
      for any same-judgment `hdefn'`; it SUFFICES to prove the **existence** of a level-strict derivation
      of the *identical* judgment — `hasType_strictify (h) : ∃ h' : HasType lvl Γ e τ ε, StrictSub h'`
      (a new `NoGenAt`-shaped `StrictSub` recording `lvl < lvl'` at every lam/let_/let_poly), whence
      `NoGenAt ℓ h'` for all `ℓ ≤ lvl`. Crucially this holds `lvl`/`Γ`/`τ`/`ε` **FIXED** (only internal
      sublevels move), so it needs **no `raiseCtx`** and therefore dodges the G13 shared-context conflict
      entirely — a re-attack the functorial-raise sessions (G9–G13) never tried. Residual risk: the
      two-same-level-`let_poly`-with-intertwined-escaping-vars arm (depth ≥ 2) — plausibly separable by
      bottom-up fresh-level assignment (G8 re-instantiation), decides whether `hasType_strictify` falls to
      a clean fresh-level mutual induction. Wants live LSP to build arm-by-arm. Soundness.lean left as
      found, no code change, HEAD `e1e7a742` unchanged. Caveat 5 OPEN.
      **Progress 2026-07-09 (Session G15 — BUILT the raise induction; machine-confirmed the two-modes
      wall is REAL and isolated to the `let_poly` defn-type relabel, not dodged by the existence
      framing).** No LSP (canary failed); Read/Grep + `lake env lean` scratch. Drafted `hasType_raise`
      (the derivation-level generalization-level raise: `LevelsBelow N h → HasType (lvl+o)
      (raiseCtx t o Γ) e τ ε`, threshold `t`, offset `o ≥ N`, output type **held fixed**) with a
      canonical-context invariant `∀ b∈Γ, t ≤ b.2.level → b.2 = genAtV b.2.level b.2.body ∧ body.levels < N`
      (threads cleanly: initial `Γ` vacuous under `CtxWfV t Γ` since non-vacuous `genAtV k d` has
      `k ∈ d.levels < t`; `lam`/`let_` add `mono` at level 0; `let_poly` adds `genAtV lvl defnTy` with
      `defnTy.levels < N` from `LevelsBelow`). **All ~20 arms compile except `let_poly`** (var/lam/let_/
      app/conv/atoms verified in a scratch import of `Typing`). The `let_poly` arm fails at exactly the
      predicted spot: the reconstructed node's bound-variable scheme is `genAtV (lvl+o) (substAt lvl
      (·↦var (lvl+o)) defnTy)` (raise re-tags the scheme body), so the **defn** sub-derivation must be
      produced at the RELABELED type `substAt lvl (·↦var (lvl+o)) defnTy`, but the IH (`output fixed`)
      hands back the defn at the ORIGINAL `defnTy`. **Definitive characterization of the wall:** within
      `defnTy` every level-`lvl` tag is generalized by this `let_poly` (`genAtV lvl` captures ALL
      level-`lvl` occurrences) so ALL must relabel; but within the `let_poly`'s OUTPUT type the level-`lvl`
      tags are FREE (escaped via instantiation args, e.g. `escRetTy = var 1 0 → var 1 0`) and must STAY —
      identical tag value `lvl`, opposite requirements, indistinguishable at the type level. Neither a
      uniform "keep output fixed" nor "relabel output by `substAt t (·↦var (t+o))`" policy closes both
      the inner-defn relabel and the outer-lambda/wrapper reconstruction. `hasType_substAt_le` cannot do
      the defn relabel (its `σ` levels must be `∈ {0,ℓ}`; `var (lvl+o)` introduces a fresh level `lvl+o ∉
      {0,lvl}`), so relabeling free level-`lvl` tags in a derivation IS the raise itself — **the raise is
      genuinely self-referential/mutual**, not reducible to substitution. The `escLam_lvl2`/`advPerf_lvl2`
      witnesses sidestep this only because their inner defn is a LEAF (`\z.z`) re-derived FRESH at the
      target level; a general theorem must relabel free level-`t` tags in an arbitrary defn subtree, which
      needs a mutual (relabel-free-tags ⋈ strictify-inner-`let_poly`) development. **Landed & committed:**
      salvaged `ctxWfV_raiseCtx` (`CtxWfV lvl Γ → CtxWfV (lvl+o) (raiseCtx t o Γ)`) into `Typing.lean`
      (per-file green, no `sorry`; genuine reusable infra for whichever raise formulation lands). Typing +
      Substitution per-file green; Soundness.lean left EXACTLY as found (pre-existing 53-line partial
      migration, 85 error sites, untouched — full green far off). Axioms unchanged, no `sorry` anywhere.
      **Recommended next (with LSP):** formulate the raise as a MUTUAL pair — (a) `hasType_relabelFree`
      (relabel free level-`t` tags `t↦t+o` in a derivation with `NoGenAt t`-below, i.e. no `let_poly`
      generalizes at `t` inside) and (b) `hasType_raise` proper (bumps ambient/gen levels), with the
      `let_poly` arm of (b) calling (a) on the defn — OR fold the whole re-instantiation into
      `genAtV_closure_ready_value_node` per the G6 shape so the defn is re-derived fresh at the fresh
      level rather than transformed. Caveat 5 OPEN.
      **Progress 2026-07-09 (Session G16 — the FIRST working derivation-level generalization-level
      raise LANDED, in the *uniform* mode; two-modes conflict decoupled and pinned; two green additive
      commits `09472c84`/`2271a256`; see
      `progress/2026-07-09-G1-phase6-sessionG16-uniform-fullraise-landed-two-modes-decoupled.md`):**
      No LSP. Re-derived the obstruction independently and found a cleaner single-theorem route the
      whole G7–G15 arc missed. **Key reframing:** prior sessions pursued a *type-fixed* raise (hold the
      conclusion type/context literally fixed), which is intrinsically **two-moded** and walls at
      nesting depth ≥ 2 (a `let_poly`'s `defnTy` carries a foreign `≥ t` gen level, at which the
      single-level `raiseScheme` and the defn's needed relabel diverge — defn and body sub-derivations
      need the shared ambient context transformed incompatibly; the task's single-target
      `hasType_relabelFree` cannot handle the accumulation, which converges to a full `raiseTy`). The
      **uniform** raise collapses the two modes into one by giving up "type-fixed": relabel *every*
      level `≥ t` by `o` uniformly (types, effects, context, gen levels), so the `let_poly` arm's defn
      is handled by the SAME theorem (`genAtV (k+o) (raiseTy t o defnTy)` matches the defn's raised
      type). **Landed:** (1) `09472c84` — pure-equality core in Scheme.lean (`levels_raiseTy`,
      `length_filter_levels_raiseTy` [arity preservation, NO freshness needed], `raiseTy_substAt_comm`
      [unconditional, no `hclean`/coverage], `instantiateV_genAtV_raiseTy` [uniform instantiation
      commutation via `args.map (raiseTy t o)`, NO padding/coverage/freshness]). (2) `2271a256` —
      `raiseTy_tyEquiv`/`raiseTy_effWeaken` (Scheme.lean) + `raiseScheme_U`/`raiseCtx_U` + helpers,
      `instantiateV_raiseScheme_U` (any scheme, no canonicity), `ctxWfV_raiseCtx_U`, and
      **`hasType_fullRaise`** itself (~21-arm structural induction, NO mutual recursion, NO
      freshness/coverage/padding) in Typing.lean. Axioms `[propext, Quot.sound]`, per-file green
      (Scheme+Typing+Substitution), no `sorry`. **The first machine-checked derivation-level raise in
      the whole arc** — proves the machinery works end to end. **Confirmed limitation (now with the mode
      built, not sketched):** the uniform raise raises the outer scheme's OWN to-be-generalized
      level-`lvl` vars (they surface in `retTy ⊆ defnTy` as escapes `genAtV lvl` quantifies),
      collapsing `genAtV lvl defnTy` to arity 0 — a DIFFERENT judgment, so proof irrelevance cannot
      transport `NoGenAt lvl` to the wrapper's `hdefn`. Inner-`let_poly`-at-`lvl` (must move) and outer
      escaped level-`lvl` in `retTy` (must stay) are the identical tag `lvl`; no threshold separates
      them, so no uniform raise closes the wrapper. **Sharpest next route (needs LSP + a soundness-
      critical decision):** `instantiateV_genAtV_raiseTy` shows the raised scheme's instantiation at
      `args.map (raiseTy lvl o)` equals `raiseTy lvl o` of the original's; for **ground** `args` (levels
      ⊆ {0}) and `defnTy` with no level `> lvl`, `raiseTy lvl o` fixes the target, so `hasType_fullRaise`
      (closure *value* unchanged) yields `HasTypeV (Closure …) target` with NO `NoGenAt`. The gap: the
      wrapper quantifies over all level-bounded args, but at RUNTIME args are ground (gap-1
      `HasTypeRT`). So: restrict the closure-readiness obligation to ground/runtime args (sound — only
      consumed at ground runtime args, `inv_var_rt` supplies them), discharge via
      `hasType_fullRaise` + `instantiateV_genAtV_raiseTy`, drop `NoGenAt` from the wrapper. A soundness-
      critical `EnvWf.cons`/`StackWfV`-Assign refactor, first route the arc has that a *built* raise
      feeds. Soundness.lean left EXACTLY as found. Caveat 5 OPEN.
      **Progress 2026-07-09 (Session G17 — the G16 ground-args route REFUTED at the source; no code
      change, analysis + doc only; see
      `progress/2026-07-09-G1-phase6-sessionG17-ground-args-route-refuted-strictify-is-type-fixed-wall.md`):**
      No LSP. Checked the route against the exact judgments (not the note's prose) and found it a
      **misdiagnosis** that does not merely narrow but **does not help**. (1) `HasTypeRT.var`'s real
      groundness (`Typing.lean:835`) is `l = 0 ∨ l = s.level` = `⊆ {0, lvl}` — it **admits level-`lvl`
      args**, not the "⊆ {0}" the note assumed; it already equals the current `EnvWf.cons` precondition.
      (2) Ground args do **not** avoid the wrapper's `NoGenAt lvl hbody`: the only `NoGenAt`-free keystone
      `genAtV_instantiate_lam_ready` needs `ℓ < lvl'` (body sublevel, **arg-independent**), and the
      `..._le` variant needs `NoGenAt`; also `instantiateV` padding reintroduces `var lvl i` (level `lvl`)
      for short ground args. The obstruction is **body-structural** (inner `let_poly` at exactly `lvl`
      with `lvl' = lvl`), untouched by restricting args. (3) `hasType_fullRaise` cannot supply the
      `NoGenAt`: `NoGenAt lvl` of a `let_poly`-at-ambient-`lvl` derivation is unprovable (`NoGenAt.let_poly`
      needs `lvl ≠ ℓ`) except via proof-irrelevance from a body-sublevel-`> lvl` alternative — the
      **type-fixed** freshening `hasType_strictify`; the **uniform** raise instead moves the escaped
      `retTy` level-`lvl` tags to `lvl+o` (changing the judgment) and **recreates the identical collision
      at the top level `lvl+o`**. The `escLam_lvl2` witness (`Typing.lean:2095`) does the type-fixed
      freshening concretely (re-instantiate the inner use at the fixed level-1 `[var 1 0, var 1 0]`) but
      **only because its inner defn is a leaf** (`\z.z`); non-leaf inner defns need the type-fixed
      derivation raise the G7–G15 arc walled on. **No tightening shipped** (it would not help; a
      non-helping soundness-critical refactor is not landed). Real target unchanged: type-fixed
      `hasType_strictify` = the two-modes wall; needs invariant (i) "`defnTy` nests no foreign cross-level
      `let_poly`" (may be false) or (ii) a mutual structural-`termination_by` freshening induction. Wants
      live LSP, multi-session. Soundness.lean left EXACTLY as found. Caveat 5 OPEN.
      **Progress 2026-07-09 (Session G18 — STRATEGIC PIVOT; the raise/strictify wall DISSOLVED, not
      climbed, by an additive-`NoGenAt`-on-`let_poly` route; analysis + doc only, no code change; see
      `progress/2026-07-09-G1-phase6-sessionG18-strategic-pivot-additive-noGenAt-on-let_poly-dissolves-wall.md`):**
      No LSP. Per task, STOPPED trying to prove the type-fixed `hasType_strictify`/raise theorem (G7–G17
      convergent wall) and investigated genuinely different routes. **Key reframing:** `HasType` is a
      `Prop`, so by proof irrelevance `NoGenAt ℓ h` is a property of the JUDGMENT, not the surface
      derivation (this is exactly what `escLam_lvl1_noGenAt := escLam_lvl2_noGenAt`, Typing.lean:2113,
      already uses); `hasType_strictify` is thus "every judgment admits a `NoGenAt lvl` derivation", and
      the wall is proving it for an adversarial `lvl'=lvl` derivation where escaped-vs-bound level-`lvl`
      vars are the same leaf. **Root cause:** the `lam` rule (Typing.lean:111) permits non-strict
      `lvl ≤ lvl'`, so the `lvl'=lvl` collision is even constructible; `noGenAt_of_lt` (Typing.lean:768)
      shows `lvl'>lvl` gives `NoGenAt` free. Real algorithmic let-gen (Rémy/OCaml levels) uses strictly
      increasing fresh levels; the codebase's own canonical examples already do (Generalization.lean:651/667
      use `lvl':=2` under ambient `1`). **The route (Route 1):** make `HasType.let_poly` (Typing.lean:132)
      additively record `NoGenAt lvl hdefn` at construction. This is **self-enforcing** — `NoGenAt.let_poly`
      (Typing.lean:531) needs `lvl ≠ inner-gen-level`, so a `let_poly` nesting a same-level `let_poly`
      becomes UNCONSTRUCTABLE, removing the exact collision from the relation. Then `inv_let` at the
      Soundness `let_poly` site (Soundness.lean:236-243) hands the wrapper's `hng`
      (Substitution.lean:170) for free, with NO raise theorem. Every OTHER `let_poly` construction site
      (~15: subst arms 411/657, ctxConv 1063, effWeaken Soundness:73, examples, Generalization) supplies
      the field via companion `NoGenAt`-PRESERVATION lemmas (all these transformations FIX generalization
      levels, so `NoGenAt lvl` is preserved, never RE-derived — the crucial difference from the wall).
      **De-risked:** `lake exe spec` root `Eyg.Spec.Harness` has NO `HasType` (104/104 is pure runtime →
      spec-adequacy risk zero); canonical derivations already satisfy the field. **Blocking caveat:** this
      is a `HasType` SPEC change → per hard constraints needs parent/user approval (NOT shipped this
      session). Honest narrowing verdict: rejects same-level-nested `let_poly` nodes, conjecturally
      re-typable at fresh levels (proving that IS strictify, stays unproven); soundness fully proved for
      the new relation, statement non-trivial, spec intact — a defensible spec REFINEMENT to canonical
      fresh levels, but a genuine spec change. Routes 2 (weaker conclusion — readiness needed at full `∀
      args` generality via `envwf_lookup`), 3 (runtime freshness — strictly larger), 4 (unreachability —
      collision is constructible) investigated and rejected as primary. **Recommendation:** seek approval
      for the additive-`NoGenAt` `let_poly` field, then execute incrementally with live LSP (preservation
      lemmas first, per-file green; constructor change + Soundness discharge last). If approval withheld,
      document Caveat 5 OPEN with this route recorded as the recommended resolution rather than budgeting
      further sessions against the type-fixed strictify wall. Soundness.lean left EXACTLY as found.
      Caveat 5 OPEN.
      **Progress 2026-07-09 (Session G19 — EXECUTION session for the G18 authorized route; the LITERAL
      authorized `NoGenAt`-field design is machine-checked INFEASIBLE (induction-induction); corrected to
      the expressible strict-sublevel form, same intent; no code change, tree left as found; see
      `progress/2026-07-09-G1-phase6-sessionG19-noGenAt-field-infeasible-induction-induction-inline-strict-corrected-design.md`):**
      No LSP. **Had explicit user authorization** for the `HasType.let_poly` change (tradeoff signed off:
      refine to canonical Rémy/OCaml fresh-level generalization; reject same-level nested `let_poly`;
      conjecturally-unchanged typable-PROGRAM set; soundness fully proved for the refined relation; spec
      104/104 unaffected). **(1) The authorized field is not expressible in Lean 4.** `HasType.let_poly`
      carrying `NoGenAt lvl hdefn` requires `HasType`/`NoGenAt` to be mutually inductive with `NoGenAt`
      indexed by `HasType` proofs = **induction-induction**, which Lean 4 core does not support. Two
      independent machine-checked minimal repros: indexing one mutual inductive by another ⇒ `Unknown
      identifier 'HasType'`; and `NoGenAt (ℓ)`'s parameter vs parameterless `HasType` ⇒ `All inductive
      types declared in the same 'mutual' block must have the same parameters`. A `NoGenAt`-as-recursive-
      `Prop`-function has the same circularity; a manual induction-induction encoding is a from-scratch
      re-encoding of all 24 `HasType` constructors, far beyond the authorized "field addition". The G18
      pivot asserted the route "threadable/self-consistent" but never checked this type-theoretic
      feasibility; it does not hold. **(2) Corrected feasible design (same authorized intent): strict
      sublevel on the defn lambda.** The wrapper `genAtV_closure_ready_value_node` (Substitution.lean:167)
      already takes `NoGenAt lvl h` as a plain premise (unchanged). `NoGenAt lvl hdefn` reduces via
      `inv_lambda_noGenAt` to `NoGenAt lvl hbody` at the defn lambda's body sublevel `lvl'`, which
      `noGenAt_of_lt` supplies FOR FREE when `lvl < lvl'` (strict) — no mutual induction. So the
      self-enforcing constraint is exactly **`lvl < lvl'` on the defn lambda** (the Rémy discipline the
      G18 note itself cites), expressible by **inlining the defn lambda's `lam`-structure into `let_poly`**
      (store `lvl'/argTy/εb/retTy/hstrict:lvl<lvl'/hfvdefn/hbodydefn`, `defnTy := .fun argTy εb retTy`,
      opaque `hdefn` reconstructed as `HasType.lam (le_of_lt hstrict) hfvdefn hbodydefn`); `inv_let` then
      hands `NoGenAt lvl hdefn := NoGenAt.lam _ _ (noGenAt_of_lt hbodydefn hstrict)` to the Soundness site
      for free. **(3) Verified non-narrowing beyond the authorized refinement:** every EXISTING fresh
      construction site already descends strictly (`HasType.lam (lvl' := 2)` under ambient `1`:
      Typing.lean:1735/1742/1815/1822, Generalization.lean:652/668); `HasType.lam`'s existing
      `argTy.levels < lvl'` already forces strict whenever the arg carries a generalizable level-`lvl`
      var; result/effect-only generalizations (`defnPerf`) re-type freely at `lvl'=lvl+1`; the
      reconstruction arms (subst/ctxConv/hasTypeRT_ctxConv/fullRaise/effWeaken) PRESERVE the stored
      components. No existing construction genuinely needs `lvl'=lvl`. **(4) Why nothing shipped / no
      blind reshape:** the constructor-arity change is all-or-nothing across ~8 files with NO committable
      per-file-green checkpoint short of the full Soundness re-green (the ~90-error grind that needs live
      LSP); starting blind would leave a large red uncommitted diff with no checkpoint, violating the "not
      landable partially" discipline. Tree left EXACTLY as found (HEAD `459d5179`; Soundness.lean
      pre-existing partial migration untouched); no `sorry`, axioms unchanged. **Recommended next
      (WITH LSP):** execute the inline-strict reshape per the note's 5-step recipe, then the two-engine
      grind + Phase 7. Caveat 5 OPEN.

      **Progress 2026-07-09 (Session G20 — the authorized inline-strict `let_poly` reshape LANDED across
      the whole non-Soundness `HasType` cone; committed).** No LSP (canary failed). Executed the G19
      corrected design. **Shipped (commit after `f1156078`):** (1) `HasType.let_poly` reshaped — the
      opaque defn-lambda-node premise replaced by the inlined pieces `lvl'`,`argTy`,`εb`,`retTy`,
      `hstrict : lvl < lvl'` (STRICT), `hfv`, `hbodydefn : HasType lvl' ((lx,.mono argTy)::Γ) lbody
      retTy εb`; `defnTy := .fun argTy εb retTy`. (2) Two helpers: `HasType.letpoly_defn` (rebuilds the
      lam-node derivation `HasType.lam (le_of_lt hstrict) hfv hbodydefn`) and `noGenAt_letpoly_defn`
      (`NoGenAt lvl` of that node **for free** = `NoGenAt.lam _ _ (noGenAt_of_lt hbodydefn hstrict)`).
      (3) Companion inductives `NoGenAt`/`HasTypeRT`/`LevelsBelow` `let_poly` arms reshaped (needed
      `(la := la)` to pin the now-unconstrained Lambda annotation). (4) Every consumer updated:
      `hasType_subst`, `hasType_substAt_le`, `noGenAt_of_lt`, `inv_let_rt`, `hasType_ctxConv`,
      `hasTypeRT_ctxConv`, `LevelsBelow.mono`, `exists_levelsBelow`, `hasType_fullRaise`. (5) `inv_let`
      (Generation) and `inv_let_rt` now additionally hand `NoGenAt lvl hdefn` for free — exactly the
      closure-readiness wrapper's premise. (6) Examples: real whole-programs reconstructed (all descend
      strictly, `lvl'=lvl+1`); the obsolete residual-corner witnesses (`advPerf_*`, `lvl'=lvl`) REMOVED
      as unconstructable **by design** (private, unreferenced; the reshape's whole point is to forbid
      the same-level nested `let_poly`); the `esc*` witnesses reconstructed via the already-strict
      `escH_defn`. **Green + committed per-file:** Typing, Generation, Generalization, Machine, Runtime,
      Substitution — all build, no `sorry`. The key confirmation: `noGenAt_letpoly_defn` discharges the
      wrapper's `NoGenAt lvl h` premise with **no** external witness, exactly as the corrected design
      predicted; the reshape rejected **nothing** currently valid (verified every real construction site
      already descended strictly). **Not done (Caveat 5 still OPEN):** the `Soundness.lean` grind. Found
      it is NOT merely a `let_poly` adaptation — it is in a **broad partial level-native + RT migration**
      (103 errors; lines 34–247 byte-identical to the pre-reshape state, all `MStateWf.run`/`hvty.conv`/
      effWeaken/level-signature debt **unrelated** to `let_poly`). Completing it = finishing that whole
      migration (the ~10-session LSP wall), orthogonal to and larger than the authorized reshape. Per the
      task's "leave Soundness.lean exactly as found unless the grind completes," Soundness.lean was **not
      edited** (its pre-existing 27/26 partial-migration diff is untouched, still uncommitted, still red —
      as it was at HEAD `f1156078`, which itself does not build Soundness). **Recommended next:** wire the
      new `inv_let`/`inv_let_rt` NoGenAt output + reshaped `HasType.let_poly` into Soundness's `let_poly`
      preservation (sites `:72`,`:226`,`:243`,`:2953`) as part of completing the level-native Soundness
      migration; that migration — not the reshape — is now the sole remaining blocker. Caveat 5 OPEN.
      **Progress 2026-07-09 (Session G21 — Soundness diagnosis; overturns the "purely mechanical"
      framing).** No LSP (canary failed). Traced the full dependency chain of the `let_poly`
      preservation case (Soundness `preservation_E` `:224–243`, A-engine) and reached a definitive
      finding: it is **NOT purely mechanical.** The mechanical parts are real (thread `lvl` + `HasTypeRT`
      through `MStateWf` — the file predates BOTH additions; `mStateWf_E` `:32` still drops the
      `HasTypeRT` field the current def carries; the `.V`-producing cases just need the extra `hrt`
      ignored; app/let need the `_rt` inversions `inv_app_rt`/`inv_let_rt`/`hasTypeRT_lambda` which
      already exist in Typing). **But the poly-let case has a genuine invariant gap:**
      `genAtV_closure_ready_value_node` (Substitution `:167`) requires `hℓ : lvl ≠ 0` **and**
      `hΓpa : PolyAboveFV lvl Γ ⟨.Lambda lx lbody, la⟩`. `inv_let`/`inv_let_rt` now hand `CtxWfV lvl Γ`
      (`hcw`) and `NoGenAt lvl hdefn` (free, as designed) — but **neither `PolyAboveFV` nor `lvl ≠ 0` is
      available** from the runtime state. `MStateWf`/`EnvWf`/`HasTypeV.closure` carry **no** context-level
      invariant (checked: `MStateWf` def is just `∃ Γ τin lvl, EnvWf ∧ ∃ hty, HasTypeRT ∧ StackWfE`;
      `HasTypeV.closure` stores `lvl'` existentially with no lower bound). And `PolyAboveFV` is **not
      derivable from `CtxWfV lvl Γ`**: for a poly binding `s = genAtV k d` (arity ≠ 0 ⟹ `k ∈ d.levels`),
      `CtxWfV` gives `k < lvl` (hence `k ≠ lvl` ✓) but says **nothing about `k ≠ 0`** — a `genAtV 0 d`
      binding with `0 ∈ d.levels` and `d.levels < lvl` satisfies `CtxWfV lvl Γ` yet violates
      `PolyAboveFV`. So closing the poly-let case requires a **carried runtime invariant** ("every poly
      binding in the realized context sits at a nonzero level," equivalently "the ambient level is always
      ≥ 1 and every generalization happened at ≥ 1"), threaded from a **nonzero initial ambient level**
      into `MStateWf`/`EnvWf`/`HasTypeV.closure` — i.e. an **architectural strengthening of the runtime
      typing judgments** plus re-proof of the Runtime/Machine lemmas, gated behind approval per the
      standing "no large architectural change without approval" rule. This is small but genuinely
      conceptual/design, not mechanical — it is what task step 5's "set the ambient level to a nonzero
      constant **if the type signature needs it**" was gesturing at, but it needs the invariant *carried*,
      not just set at the entry. **Second finding:** `Soundness.lean` contains **TWO complete engines** —
      the A-engine `MStateWf` development (`~:30–2840`, partially level/RT-migrated) and a full
      **B-engine `MStateWfB`** mirror (`~:2850–4278`) still **entirely on the pre-migration API**
      (`Scheme.genAt`/`.instantiate` not `genAtV`/`.instantiateV`, old 3-arg `HasTypeV.closure`, old
      `inv_let` tuple `⟨defnTy, hdefn, hbody⟩`, `genAt_closure_ready`/`ctxWf_fixed`). So the 103 errors
      span two mirrored migrations, not one. **Decision:** made NO edits (a half-migration is
      uncommittable — red Soundness — and would leave a state harder to resume than the clean untouched
      file); left `Soundness.lean` EXACTLY as found. **Recommended next session:** (1) get approval to
      strengthen the runtime judgments with the nonzero-poly-level context invariant (or add a lemma
      `polyAboveFV_of_ctxWfV_nonzeroPoly`), then (2) grind the A-engine `MStateWf` mechanically
      (`lvl`+`HasTypeRT` threading via the existing `_rt` inversions), then (3) the B-engine mirror. Caveat
      5 OPEN.

      **Progress 2026-07-09 (Session G22 — bridge lemma LANDED + full threading design finalized; the
      gap confirmed architectural, not "small additive").** No LSP (canary failed). HEAD `095f51ad`.
      **Landed & committed (`8110c393`, green in `Typing.lean`, independent of the Soundness grind):**
      the carried-invariant infrastructure the poly-let case needs — (i) `CtxPolyBd Γ := ∀ b ∈ Γ,
      b.2.arity ≠ 0 → b.2.level ≠ 0 ∧ b.2.level ∈ b.2.body.levels` (every polymorphic binding sits at a
      nonzero level occurring among its body levels); (ii) the **bridge**
      `polyAboveFV_of_ctxPolyBd : CtxPolyBd Γ → CtxWfV ℓ Γ → PolyAboveFV ℓ Γ e` (a looked-up poly
      binding's level is `≠ 0` from `CtxPolyBd` and `< ℓ` hence `≠ ℓ` from `CtxWfV` at that level — this
      is the previously-flagged-but-unbuilt `polyAboveFV_of_ctxWfV_nonzeroPoly`, now built and named);
      (iii) preservation lemmas `ctxPolyBd_cons_genAtV` (needs `lvl ≠ 0`) / `ctxPolyBd_cons_mono`
      (vacuous). This is the conceptual keystone and is correct *independent of how the runtime threads
      the invariant*, so it is landed now.
      **Finding (revises this task's premise that the fix is "small/additive, no auth needed"):** closing
      the gap end-to-end is **NOT** just a context predicate — it also requires a **nonzero-ambient-level
      lower bound carried through `HasTypeV.closure` (and the `assign`/`arg` stack frames)**, because
      `genAtV_closure_ready_value_node` has `hℓ : lvl ≠ 0` as a *hard* precondition of the substitution
      machinery (`hasType_subst`/`hasType_substAt_le` both take `ℓ ≠ 0`), and that `lvl` is the closure
      body's / frame's ambient level, not the state's. The `lvl = 0` branch cannot be discharged
      separately: at `lvl = 0`, args carrying level-0 variables (permitted by `EnvWf`'s readiness clause
      `∀ l ∈ t.levels, l = 0 ∨ l = s.level`) make `0 ∈ defnTy.levels` possible, so `genAtV 0 defnTy` can
      have `arity ≠ 0` — exactly the `CtxPolyBd`-violating poly-binding-at-level-0. Avoiding it needs
      "no level-0 type variable is ever reachable," which is itself a carried invariant bottoming out at
      a nonzero top-level ambient. So the previous session's "architectural strengthening of the runtime
      typing judgments" diagnosis stands and is now made precise.
      **Finalized threading design (for the next session — deterministic, no re-derivation needed):**
      add four fields and discharge at construction sites:
      (a) `EnvWf.cons`: `(hpoly : s.arity ≠ 0 → s.level ≠ 0 ∧ s.level ∈ s.body.levels)` — i.e.
      `EnvWf env Γ → CtxPolyBd Γ` becomes a derived projection; mono cons trivial, `genAtV lvl` cons via
      `ctxPolyBd_cons_genAtV` (needs the frame's `1 ≤ lvl`);
      (b) `HasTypeV.closure`: `(hlvl' : 1 ≤ lvl')` — so an applied closure's body runs at nonzero ambient;
      created closures get it from the ambient `1 ≤ lvl ≤ lvl'`;
      (c) `StackWf.assign` / `StackWf.arg` (and the `StackSegWf` mirrors): `(hlvl : 1 ≤ lvl)`;
      (d) `MStateWf.E`/`.V`/`wait`: carry `1 ≤ lvl` (E-case) so preservation has it at each step —
      successors keep it (same `lvl`, `lvl+1` via `let_poly` body, or a closure's `lvl' ≥ 1`).
      `mStateWf_initial` then takes `1 ≤ lvl`; `soundness`/`soundness_evalR` fix the top ambient to `1`
      and re-type the closed program at level `1` (level-raise; every closed program typable at `0` is
      typable at `1`). Green-file blast radius: `EnvWf`/`HasTypeV.closure`/`StackWf.assign`/`arg`
      definitions in `Runtime.lean` (few sanity examples bump `lvl' 0 → 1`), the `stackWf_assign_inv`/
      `stackWf_arg_inv` inversions in `Machine.lean` (expose the new field), and `MStateWf`/
      `mStateWf_initial` in `Machine.lean`. Heavy re-proof is all in `Soundness.lean` (already red).
      Then the poly-let case: `inv_let` gives `CtxWfV lvl Γ`; `EnvWf env Γ` gives `CtxPolyBd Γ`; bridge →
      `PolyAboveFV lvl Γ`; `1 ≤ lvl` gives `lvl ≠ 0`; feed `genAtV_closure_ready_value_node`. **Decision:**
      did NOT begin the four-field threading — it ramifies across two inductive-definition files and both
      engines and cannot be validated end-to-end (Soundness stays red until the whole ~103-error two-engine
      grind lands), so a committed half-shaped strengthening would risk churn; committed only the
      validated, shape-independent bridge lemma. `Soundness.lean` left EXACTLY as found (uncommitted
      partial migration, 103 errors, unchanged). Caveat 5 OPEN.

      **Progress 2026-07-09 (Session G23 — four-field threading LANDED (green-committed); FIRST ENGINE
      Soundness migration COMPLETE except a newly-surfaced closure-body-`HasTypeRT` gap).** No LSP
      (canary failed). HEAD `d86e253c`. **Committed (two green per-file increments):**
      (1) the finalized four-field threading — `HasTypeV.closure` gains `1 ≤ lvl'`; `EnvWf.cons` gains
      `hpoly (s.arity ≠ 0 → s.level ≠ 0 ∧ s.level ∈ s.body.levels)` with `ctxPolyBd_of_envWf` as the
      derived projection; `StackSegWf.assign/.arg`, `StackWf.assign/.arg` gain `1 ≤ lvl` (inversions
      expose it); `StackWfV/StackWfE` Assign clauses + `MStateWf.E` + `mStateWf_initial` carry `1 ≤ lvl`;
      `closure_typed_of_lambda`/`genAtV_closure_ready_value(_node)` derive `1 ≤ lvl'` from the ambient.
      (2) a needed FIFTH carried field discovered mid-grind: the `hpoly` obligation must also ride in the
      `StackWfV/StackWfE` Assign clauses (the Assign-pop reconstructs `EnvWf.cons`, so it needs `hpoly`
      there and it is NOT derivable from readiness) — plus helpers `schemePolyBd_genAtV`/`schemePolyBd_mono`
      in `Typing.lean`; and `HasTypeV.partialBuiltin` moved to `s.instantiateV args` (matches `inv_builtin`;
      base type is not inspected by `BuiltinAppPreserves`). Green per-file: Typing/Runtime/Substitution/
      Machine (+ transitive); no `sorry`.
      **Soundness.lean (uncommitted, red — advanced from the pre-existing partial migration):** the
      **entire first engine is now green** — `weakenEffAux` (fixed the mis-binder'd `app`/`conv`/`let_poly`
      induction arms), `preservation_E` (rewritten to consume `inv_var_rt`/`inv_app_rt`/`inv_let_rt` and
      `builtin_instantiate_arrow`→`instantiateV`; both `let` cases discharge via
      `genAtV_closure_ready_value_node (Nat.one_le_iff_ne_zero.mp hlvl) hng (polyAboveFV_of_ctxPolyBd
      (ctxPolyBd_of_envWf henv) hcw) hcw henv` — **the Caveat-5 poly-let preservation obligation is
      MECHANICALLY DISCHARGED, exactly as the G22 design predicted**), `progress` (stale `mStateWf_E`
      destructure fixed — collapsed a 76-error cascade), `perform_walk` Assign/Arg, `preservation_V`
      Assign/Arg. Remaining first-engine errors: **only the 2 closure-application cases** (`preservation_V`
      lines ~874 & ~1036).
      **NEWLY SURFACED GAP (not covered by the "finalized design"; blocks BOTH engines' closure-apply
      case):** `MStateWf.E` requires `HasTypeRT` of the *control* derivation, but on a `reduceCall`
      closure step the new control is the closure **body** `hbody`, and `HasTypeV.closure` carries **no**
      `HasTypeRT` witness for it — and cannot: a closure is created at lambda-eval where only
      `HasTypeRT.lam` (which by design carries **no** body premise — else the legit referencing example
      `\w. a w` with its non-ground `[.var 2 0]` arg would be rejected) is available. The `HasTypeRT`
      design note (`Typing.lean` ~950) already stipulates the intended mechanism — "the closure body is
      re-typed via `substAt` with **ground** args at application, re-establishing `HasTypeRT` there" — but
      that **infrastructure is not built**: there is no `HasTypeRT`-tracking companion of
      `hasType_subst`/`hasType_substAt_le`, and the environment machine's closure-apply currently uses
      `hbody` **directly** (env-extension, not type substitution), so wiring in a re-typing is itself
      non-trivial. Building `hasTypeRT_subst` (mirror ~100-line induction, RT-tracking on the var arm via
      the ground-`σ` hypothesis) + rewriting the 4 closure-apply sites (2 engines × 2 cases) to re-type is
      the true remaining work — NOT mechanical, and arguably a runtime-judgment strengthening needing
      sign-off. The **second engine** (`MStateWfB`/`StackWfB`/`StackWfEB`/`preservation_VB`/`_EB`/`progressB`,
      Soundness ~2400-3993) is otherwise a straight mechanical repeat of the first-engine threading, blocked
      by the same closure-body-RT gap. **Decision:** committed the two validated green-cone increments;
      left `Soundness.lean` uncommitted (red, first engine complete-bar-closure-RT). Caveat 5 OPEN
      (poly-let preservation itself DISCHARGED; closure-body-RT is now the sole remaining soundness gap).
    - **Session G24 (2026-07-09) — closure-RT gap analyzed; corrected mechanism; no code landed.**
      No LSP/MCP (canary failed). HEAD `1065877d`; `Soundness.lean` uncommitted-red as G23 left it
      (52+/42−, no `sorry`, verified intact). Deliberately landed **no** speculative code — the gap is
      a genuine multi-piece design item, not the "mirror ~100-line induction" the G23 note assumed, and
      a half-written `hasTypeRT_subst` would have left `Soundness.lean` mangled with no committable green.
      **Corrected the central technical misconception in the G23 sketch:** `substAt ℓ σ`-re-typing DOES
      ground a var node's instantiation args — `substAt_instantiateV_scheme` (Scheme.lean:1535) rewrites
      the produced var to carry `args.map (Ty.substAt ℓ σ)`, not the original `args` (I had first read it
      as arg-preserving; it is arg-mapping). So the plan's "grounds `[var 2 0]` to `[integer]`" (line ~396)
      is real and the design is sound in principle. **The actual remaining obstruction (the true reason
      33 sessions did not close it):** a HasTypeRT of the output var needs its args' levels `⊆ {0, s.level}`;
      `substAt ℓ (ground σ)` yields levels `⊆ (t.levels \ {ℓ}) ∪ {0}`, so this holds **only if the input
      var's args' levels are `⊆ {0, ℓ, s.level}`** — a boundedness precondition that `HasType.var` records
      **nothing** about and `HasTypeRT` does **not** carry (its var arm bounds by `{0, s.level}`, no `ℓ`).
      Hence `hasTypeRT_subst` needs, as its hypothesis, a NEW predicate `HasTypeRTAt ℓ h` (HasTypeRT with
      the var/builtin arm relaxed to `l = 0 ∨ l = ℓ ∨ l = s.level`) — an additional ~21-arm inductive, not
      just an induction. **And the deeper blocker (the part that plausibly warrants sign-off):** at the
      closure-apply site (`preservation_V`, Apply-frame, closure case) there is **no available fact that
      the argument type `argTy` (or any body level) is ground/bounded** — `MStateWf.V`/`HasTypeV`/`EnvWf`
      carry no groundness (mono `EnvWf.cons` binds a value at *any* type; `HasTypeV.closure` stores an
      existential `lvl'` and an arbitrarily-non-ground arrow). So even a proven `hasTypeRT_subst` cannot
      fire there without first **threading a runtime groundness / level-bound invariant** (values/env bind
      at levels bounded by the closure's abstraction level; the "nonzero-ambient-level invariant" the
      Caveat-5 narrative names is the first of these fields, already threaded in G23, but the *body-var-args
      boundedness* one is not). That threading is a **load-bearing runtime-judgment strengthening across
      `MStateWf`/`HasTypeV.closure`/`StackWf*` in both engines** — the kind of change the closing-session
      brief says to FLAG rather than assume. **Also surfaced (separate, first-engine):** the G23
      `HasTypeV.partialBuiltin → instantiateV` move left `builtinApp_arity2`'s `hbase`/`rw` (Soundness
      ~1938) and the `fix` case (~2050), plus B-mirrors (~3801/~3858), typed at `s.instantiate` while the
      goal now needs `s.instantiateV` — mechanical, but only committable once the engine reaches green, so
      not landed this session. **Concrete recommended next step:** (1) add `HasTypeRTAt ℓ` to `Typing.lean`
      and prove `hasTypeRT_subst : HasTypeRTAt ℓ h → (σ ground) → NoGenAt ℓ h → ℓ ≤ lvl → PolyAboveFV … →
      HasTypeRT (hasType_substAt_le hℓ σ hσ hng hlt hΓ)` (per-file-green, committable in isolation); (2)
      SEPARATELY decide/sign-off the runtime groundness invariant that supplies `HasTypeRTAt ℓ hbody` +
      ground `σ` at the four closure-apply sites, which is the genuine open design question. Caveat 5 stays
      OPEN (poly-let preservation DISCHARGED; closure-body-RT open, now precisely characterized).
      **Progress 2026-07-09 (Session G25 — `HasTypeRTAt ℓ` + `Ty.not_mem_levels_substAt` LANDED; the
      two-induction inversion wall for `hasTypeRT_subst` isolated, clean single-predicate fix designed;
      commit `371918d7`).** No LSP (canary failed). HEAD was `32dd2ecd`; committed the G24-recommended
      part-1 infrastructure, per-file green (Typing/Scheme + full non-Soundness cone, 1762 jobs), no
      `sorry`, axioms untouched, `Soundness.lean` left EXACTLY as G23/G24 left it (52+/42−, uncommitted,
      red). **Landed:** (1) `HasTypeRTAt ℓ h` (Typing.lean) — the level-`ℓ`-aware strengthening of
      `HasTypeRT`, structurally identical except the `var`/`builtin` arms bound args by
      `l = 0 ∨ l = ℓ ∨ l = s.level` (one extra `ℓ` disjunct); like `HasTypeRT` it does NOT recurse into
      `lam`/`let_poly` bodies. (2) `Ty.not_mem_levels_substAt` (Scheme.lean) — a ground (level-`ℓ`-free)
      `σ` removes `ℓ` from `(substAt ℓ σ t).levels`; the exact fact the `hasTypeRT_subst` var/builtin arms
      need to drop the `ℓ` disjunct (`substAt ℓ σ` removes `ℓ` via this lemma, introduces only `0` via
      groundness ⇒ output args land in `{0, s.level}` = `HasTypeRT`'s bound). **`hasTypeRT_subst` NOT
      landed — a real batch-mode wall, precisely isolated.** Wrote the full ~150-line induction (mirroring
      `hasType_substAt_le`, bundling `∃ h', HasTypeRT h'`); it type-checks structurally EXCEPT the six
      points where a sub-`HasTypeRTAt` witness must be extracted from `hrtat`. `cases hrtat`/node-based
      inversion both fail in batch mode: (a) `var`/`builtin` — `cases` hits `Dependent elimination failed …
      Decidable.rec` from `s.instantiateV args`'s `if s.arity = 0` in the type index; (b) `app`/`let_`/
      `let_poly`/`conv` — `cases` re-generalizes the shared indices (`retTy`/`bodyTy`/`argTy`), yielding
      `hf✝`≠`hf` and demanding spurious alternatives, because `HasType : Prop` gives no constructor
      discrimination through the derivation index. The `inv_*_rt` lemmas dodge (a)/(b) via the
      generalize-**node** trick, but a node-based `inv_*_rtat` returns the sub-derivations as fresh
      **existentials** (its own `argTy_i`/`defnTy_i`) that do NOT defeq-match the `hng`-induction arm's
      `hf`/`hdefn` (differing existential types ⇒ proof-irrelevance does not bridge), AND for the shared
      `.Let` node it must return a `let_`/`let_poly` **disjunction** whose dead branch is irreducible
      (proof irrelevance even makes `HasType.let_ … = HasType.let_poly …`, so it can't be ruled out). So
      mixing induction-on-`hng` with inversion-of-`hrtat` (or vice-versa) is the wall. **Clean fix
      (recommended, needs LSP to verify the single induction): merge the two predicates into ONE combined
      inductive `RTSubstReady ℓ h`** carrying, in a SINGLE recursion, the `var`/`builtin` AT-bounds AND —
      at the non-RT-recursed `lam`/`let_poly`-defn positions — the `NoGenAt ℓ` witness those bodies need
      for re-typing (`lam`: `NoGenAt ℓ hbody`; `let_poly`: `NoGenAt ℓ hbodydefn` + `hne`, body recursed).
      Inducting on `RTSubstReady` ONCE yields every sub-witness as an arm variable — **no inversion of a
      second predicate, no existential mismatch, no dead disjunct**. `noGenAt_of_lt` (Typing.lean:889)
      supplies the carried `NoGenAt` fields for free wherever `ℓ <` the sub-derivation's level (all
      `let_poly` bodies/defns, and everything in the strict `ℓ < lvl` case); only the non-strict `ℓ = lvl`
      boundary needs the genuine witness, available at the keystone from `inv_let`'s `NoGenAt lvl hdefn`.
      Construction sites (keystone + 4 closure-apply) build `RTSubstReady` from that same `NoGenAt` +
      `noGenAt_of_lt`. **UPDATE (same session, LANDED — commit `93e07b91`): the `RTSubstReady` fix WORKED
      in batch mode, no LSP needed after all.** Defined `RTSubstReady ℓ h` exactly as designed and proved
      `hasTypeRT_subst : RTSubstReady ℓ h → (∀ i, ∀ l ∈ (σ i).levels, l = 0) → ℓ ≤ lvl → PolyAboveFV ℓ Γ e
      → ∃ h' : HasType lvl (substCtxAt ℓ σ Γ) e (substAt ℓ σ τ) (substAt ℓ σ ε), HasTypeRT h'` by a single
      induction on `RTSubstReady` — every sub-witness an arm variable, zero inversions. The ONLY fixes the
      designed proof needed were four `HasTypeRT.{lam,app,let_poly,conv}` constructor calls that had to be
      handed their implicit derivation/EffWeaken/TyEquiv args explicitly (`(hbody := …)`, `(hw := …)`,
      `(hbodydefn := …)(hcw := …)`, `(hτ … )(hε …)`) — proof irrelevance leaves those implicits
      unsynthesized otherwise. Per-file green (Typing + full non-Soundness cone, 1762 jobs), no `sorry`,
      axioms untouched. **So the ENTIRE gap-1 substitution infrastructure is now COMPLETE**
      (`Ty.not_mem_levels_substAt` + `HasTypeRTAt` + `RTSubstReady` + `hasTypeRT_subst`, three green
      commits `371918d7`/`be7c3eec`/`93e07b91`). `HasTypeRTAt` is now superseded by `RTSubstReady` as the
      working predicate (kept as the clean "pure args-bound" statement; harmless, a future session may
      drop it). **What remains for gap 1 (the genuine open architectural item, G24 item 2, unchanged):**
      thread a runtime groundness/level-bound invariant through `HasTypeV.closure`/`MStateWf`/`StackWf*`
      (both engines) so the 4 closure-apply sites can SUPPLY `RTSubstReady ℓ hbody` + a ground `σ` when
      invoking `hasTypeRT_subst`, then add an RT-producing variant of `genAtV_closure_ready_value_node`
      and wire the sites. That threading is the load-bearing runtime-judgment strengthening; it ramifies
      across two inductive-definition files + both engines and can only be validated once `Soundness.lean`
      goes green (so not committable in isolation). Also still pending: `builtinApp_arity2`/`instantiateV`
      mechanical regression (Soundness ~1938/~2050 + B-mirrors) and the ~66-error B-engine grind. Caveat 5
      OPEN (poly-let preservation DISCHARGED; closure-body-RT: **substitution infra COMPLETE**, runtime
      threading + wiring remain).
      **Progress 2026-07-09 (Session G26 — `builtinApp_arity2`/`instantiateV` regression CLEARED (A+B) +
      headline wrappers migrated; A-engine now at EXACTLY the 2 closure-RT crux sites; closure-RT gap
      signed off as an env/context-GROUNDNESS invariant beyond the G22-G23 scalar-field pattern; no
      commit — all durable working-tree progress inside uncommittable-red `Soundness.lean`).** No LSP
      (canary failed). HEAD `471de13a`; `grep -rn sorry Eyg/Types/*.lean` empty throughout. **Landed
      (working tree, verified error-reducing):** (a) the G23 `partialBuiltin → instantiateV` regression —
      `builtinApp_arity2`/`_B`'s `hbase` premise + internal `rw` (~1938/~3796), the `fix`-creation
      `hB`/`rw … at hpw` (~2044/~3858), the 16 mono caller `hbase` proofs
      (`Scheme.instantiate_mono` → `Scheme.instantiateV_mono`) and the 2 `equal` proofs
      (`Scheme.instantiate,Ty.subst` → `Scheme.instantiateV,Ty.substAt`); the `simpa … using hpw` lines
      left alone (close by defeq on a concrete literal scheme). (b) `soundness_evalR_value`/
      `soundness_evalR_noBadCrash` re-threaded to the migrated `mStateWf_initial`
      `(1 ≤ lvl)(HasType lvl …)(HasTypeRT h)` (they still passed pre-migration `HasType [] prog τ ε`).
      **Result:** `lake env lean -DmaxErrors=500 Soundness.lean` shows the WHOLE A-engine (< 2444) green
      EXCEPT the two Apply-frame closure-case sites (874-877 + mirror 1036-1039) — the RT gap; ~89 of the
      remaining ~95 errors are the un-migrated B-engine. **Closure-RT gap — DEFINITIVE sign-off:** the
      `.E`-state (`MStateWf.E`) needs `HasTypeRT hbody` for the applied closure body; `hasTypeRT_subst`
      (G25) can produce it from `RTSubstReady ℓ hbody` + ground `σ`, but **neither is available and
      `HasTypeRT hbody` is genuinely un-storable in `HasTypeV.closure`** (the Lambda-creation site has
      only the lambda-NODE RT, which by design carries no body premise — a legitimately-typed body can be
      non-RT, e.g. `\w. a w`; recursing `HasTypeRT.lam` into bodies would reject it). Body-RT must be
      re-established by grounding at apply — but the non-RT arg levels are references to **outer, captured,
      level-`<lvl'`** poly bindings, groundable only from the **environment/context**, which today carries
      NO groundness. **New subtlety (extends G24/G25):** a body may reference **several** outer
      generalization levels ⇒ grounding is potentially **iterated** (one `hasTypeRT_subst` per level), and
      each grounding `ℓ` must lie **outside** the exposed `retTy/εb/argTy/Γ` level sets to preserve the
      running config's types. **So gap 1's remaining piece is a structural env/context-groundness
      predicate (candidate `CtxGround ℓ Γ`/`EnvGround`, threaded into `EnvWf.cons` + `HasTypeV.closure`)
      whose CONSTRUCTION at the plain-Lambda site is non-obvious — NOT the locally-dischargeable scalar
      fields of G22-G23.** The substitution consumer (`RTSubstReady`+`hasTypeRT_subst`) is ready; the
      upstream groundness invariant + RT-producing keystone variant + (iterated) wiring remain, and the
      B-engine is a straightforward mechanical mirror once that shared invariant is designed. B-engine left
      a CLEAN un-migrated block (a half-migration would be more broken/harder to resume). Caveat 5 OPEN.
      **Progress 2026-07-09 (Session G27 — closure-RT groundness DESIGN session; the G24/G26 "put it on
      `HasTypeV.closure`" recommendation CORRECTED; single-grounding discharge + 3 side conditions worked
      out; no code landed, Soundness.lean preserved intact). See
      `progress/2026-07-09-G1-phase6-sessionG27-closureRT-groundness-applyf-frame-correction.md`.** No LSP
      (canary failed). HEAD `471de13a`; no edits (G26 working tree preserved), `grep -rn sorry` empty.
      Confirmed the exact error state (`-DmaxErrors=8`): A-engine errors ONLY at 874-877/1036-1039, root
      cause = `cases hf with | closure henvc hbody heqc` binds 3 of the migrated 5 fields + the `.E`
      `refine` misses the `HasTypeRT hty` slot for `hty = weakenEff (HasType.conv hbody hR …) …`.
      **KEY RESULT (corrects the standing recommendation): the groundness invariant CANNOT be a
      `HasTypeV.closure`/`HasTypeRT.lam` field** — proven by two concrete reachable witnesses: (1)
      `let f = (\u. \w. a u) in …` makes the inner body instantiate `a` at `[.var L1 0]` (L1 = f's gen
      level `≠` inner level `lvl'`), so the stored body is not `RTSubstReady lvl'`, and `EnvWf.cons`'s
      poly-readiness must build `HasTypeV.closure` for such non-ground instantiations; (2) at
      `closure_typed_of_lambda` (Soundness 214) only the body-premise-free `HasTypeRT.lam` is available,
      and strengthening it to `RTSubstReady lvl' hbody` was evaluated + REJECTED (admits `\w. a w` but
      rejects witness (1) ⇒ would make a legitimate closed program non-RT at `mStateWf_initial`). **The
      real principle: stored closures can be non-RT; only APPLIED closures are ground-enough ⇒ the
      invariant belongs on the `applyf` frame (`StackWf.applyf`/`StackSegWf.applyf`) + an `EnvWf.cons`
      ground-args-only readiness clause, NOT `HasTypeV.closure`.** **Discharge (single grounding, no
      iteration — dissolves the G24/G26 multi-level worry):** at the apply site run the already-landed
      `hasTypeRT_subst` ONCE at `ℓ = lvl'` with any ground `σ`, under 3 side conditions the frame must
      guarantee — (C1) `CtxWfV lvl' Γ`; (C2) `retTy'`/`εb'` levels `< lvl'`; (C3) `RTSubstReady lvl'
      hbody` — which make `substCtxAt/substAt lvl' σ` identity on `Γnew/retTy'/εb'` (argTy' already
      `< lvl'`) so the re-typed derivation matches the required judgment AND is `HasTypeRT`. Next session:
      thread (C1)+(C3) into `EnvWf.cons` (ground-args clause only), (C2) into `applyf`, wire the 4 apply
      sites (+ `hasTypeRT_weakenEff`, a `weakenEffAux`-mirror needed in Soundness.lean). This threading is
      multi-file (Runtime+Machine+both Soundness engines), validatable only at full green — hence not
      landed this session. Caveat 5 OPEN.

      **Progress 2026-07-09 (Session G28 — attempted the G27 applyf-frame threading; MACHINE-CHECKED
      REFUTATION of the leading packaging mechanism + a newly-surfaced source-of-readiness gap). See
      `progress/2026-07-09-G1-phase6-sessionG28-closureReady-propirrelevance-refutation.md`.** No LSP
      (canary failed). HEAD `0c0b6951`; NO source edits — G26 near-green `Soundness.lean` preserved
      byte-identical (backed up + `diff`-verified), `grep -rn sorry` empty. Re-confirmed the exact error
      state (`-DmaxErrors=40`): A-engine errors ONLY at 874-877/1036-1039 (3-of-5 `cases` binders +
      missing `HasTypeRT` slot, as G27 diagnosed) + the un-migrated B-engine at 2460/2501/2573.
      **RESULT 1 (machine-checked, scratch-validated): the natural vehicle for carrying (C1)-(C3) —
      a `def HasTypeV.closureReady (hf : HasTypeV f (.fun …)) : Prop := match hf with | .closure … => (C1)∧(C2)∧(C3) | _ => True`
      threaded as an `applyf` field — DOES NOT WORK.** The `def` itself compiles, but at the apply site
      `cases hf` cannot reduce a hypothesis `hcr : hf.closureReady` into the closure-branch content:
      `HasTypeV : Prop`, so its matcher can only large-eliminate into `Prop`, and reverting the
      hf-dependent `hcr` forces a `Sort`-polymorphic motive → `casesOn can only eliminate into Prop`.
      Proof-irrelevance blocks extracting the closure existentials (`lvl'`, `hbody`) from the *proof*
      `hf` in a `cases`-alignable way. So (C1)-(C3) cannot be packaged as a match-def over the closure
      derivation. **RESULT 2 (design gap G27 glossed): even a two-constructor frame inductive
      (`closureApplied`-with-(C1)-(C3) / `partialApplied`-with-`HasTypeV`) still needs (C3)
      `RTSubstReady lvl' hbody` SUPPLIED at the Arg→`applyf` creation site (Soundness 862), where only
      the function VALUE `hv : HasTypeV v (.fun …)` and the ARGUMENT's typing/RT are in scope — the
      function control's `rf : HasTypeRT hf` was consumed during `f`'s evaluation and HasTypeV carries no
      RT. So readiness must be threaded forward from the Apply-node's `rf` onto the persistent `StackWf.arg`
      frame as a forward obligation about the eventual function value (a StackWfE-`Assign`-style
      "future-closure readiness", but over the arg frame's function slot), discharged at value-production.
      This is materially larger than G27's "add 3 fields to applyf + EnvWf.cons ground clause" and is the
      genuinely-open piece. Everything is entangled in the red `Soundness.lean` (no independently-committable
      increment: any `applyf`/`arg`/`EnvWf.cons` field change breaks Runtime+Machine+Soundness at once, and
      the no-red-commit rule bars landing until full green), which is why speculative half-threading was
      NOT attempted — it would only deepen the near-green tree's breakage. Caveat 5 OPEN; substitution
      infra (G25 `hasTypeRT_subst`) still complete and correct; the discharge recipe (single grounding at
      `lvl'`) unchanged — only the CARRIER + readiness SOURCE remain to be built.
      **Progress 2026-07-09 (Session G29 — design correction: the crux needs `HasTypeRT hbody`, NOT
      `RTSubstReady lvl' hbody`; the forward-readiness-on-arg-frame (G28) shown to relocate rather than
      solve; true obstruction localized to ONE site + ONE invariant; no code landed, Soundness.lean
      preserved byte-identical). See
      `progress/2026-07-09-G1-phase6-sessionG29-hasTypeRT-not-RTSubstReady-correction.md`.** No LSP
      (canary failed). HEAD `96e68baf`; no edits (G26/G28 working tree preserved, `diff -q` IDENTICAL vs
      `/tmp/Soundness.G28start.backup.lean`); `grep -rn sorry` empty. Error state unchanged (A-engine red
      ONLY at 874-877/1036-1039; B-engine un-migrated ≥ 2460). **RESULT 1 — the crux needs `HasTypeRT
      hbody`, not `RTSubstReady lvl' hbody` (corrects G27):** traced `MStateWf.E`'s missing slot at the
      Apply-frame closure case — it is `HasTypeRT hty` for `hty = weakenEff (HasType.conv hbody …) …`,
      i.e. after peeling `weakenEff`/`conv` (two small Soundness-local wrappers, not yet built) the real
      need is **`HasTypeRT hbody`**, a `HasTypeRT` not an `RTSubstReady`. `HasTypeRT.var` bounds arg
      levels by `{0, s.level}` (the var's OWN scheme level); `RTSubstReady` adds an `ℓ` disjunct +
      `lvl≠ℓ`/`NoGenAt`. **G27's two rejection witnesses are HasTypeRT-fine:** `\u.\w. a u` (inner body
      `a u`, `a` at `[.var L1 0]`, `a.level=L1`) satisfies `HasTypeRT.var` (`L1 ∈ {0,L1}`); the escape
      witness `\x.(let h=\z.z in h)` satisfies `HasTypeRT.let_poly` (needs only `HasTypeRT` of the
      let-body var `h`, instantiated at `[.var lvl' 0]`, `h.level=lvl'`). Both FAIL `RTSubstReady lvl'`
      but that predicate was never what the crux needed. **This dissolves the entire G6-G9
      escape/level-normalization/raise-sublevel line** for the crux (no grounding, no `hasTypeRT_subst`,
      no level-raise metatheorem needed for these bodies). **RESULT 2 — the G28 forward-readiness-on-arg
      -frame does NOT reduce to the StackWfE-Assign template:** the Assign obligation is about the
      IMMEDIATE control being a lambda (closure one step away, body available at `stackWf_toStackWfE`);
      the arg frame's function slot is filled by a value produced by ARBITRARY evaluation of `f`, so the
      obligation must survive `f`'s whole evaluation — not derivable from `rf` (`HasTypeRT.lam` has no
      body premise, re-confirmed) and inexpressible as a one-step forward clause. To survive arbitrary
      evaluation it must ride the VALUE judgment ⇒ **it relocates onto `HasTypeV.closure`, it does not
      solve the problem.** G28's design is a detour. **RESULT 3 — true minimal obstruction: env-groundness
      at the plain lambda-eval site.** Put `HasTypeRT hbody` on `HasTypeV.closure`. Poly-let discharge:
      closures are only materialized by the readiness function (`genAtV_closure_ready_value_node`) at
      GROUND args ⇒ grounded body ⇒ `HasTypeRT` via the G25 `hasTypeRT_subst` infra. Mono-let: via
      `closure_typed_of_lambda`. The SINGLE genuine gap is the plain lambda-eval site (Soundness 211-215),
      where `HasTypeV.closure` is built from `inv_lambda hty` but the only RT in scope is
      `hrt=HasTypeRT.lam` (no body premise) ⇒ `HasTypeRT hbody` is not locally available. `HasTypeRT
      hbody` fails exactly for a body instantiating a captured var off its own scheme level (e.g. `\w. a w`
      at `[.var 2 0]`, `a.level=1`), which arises only as a static poly-let DEFN inside a live
      generalization — but by the time any lambda is evaluated as a plain CONTROL the enclosing
      generalization has been instantiated to ground. **That is exactly a runtime env/context-groundness
      invariant (G26's `CtxGround`/`EnvGround`), threaded on `EnvWf`/`HasTypeV.closure`, whose one payoff
      is `HasTypeRT hbody` at lambda-eval; the crux then closes by `cases hf` projecting the stored field
      — no arg-frame forward-readiness, no apply-site grounding, no level-normalization.** **Net for next
      session:** (1) field = `HasTypeRT hbody` on `HasTypeV.closure`; (2) design+prove the env-groundness
      invariant (its construction at lambda-eval + preservation) — the real remaining metatheory, a
      runtime-judgment strengthening (flag for sign-off); (3) poly/mono discharge reuse existing infra;
      (4) keep `RTSubstReady`/`hasTypeRT_subst` (still needed for the poly-let ground re-typing, just NOT
      at the apply site). Nothing independently committable (field change breaks Runtime+Machine+both
      engines at once; wrappers Soundness-local; invariant unbuilt) — tree preserved byte-identical,
      G25 infra intact. Caveat 5 OPEN.
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
