---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G25". Landed the closure-body-RT gap's precondition
  predicate `HasTypeRTAt ℓ` + its supporting substitution-level lemma `Ty.not_mem_levels_substAt`
  (one green committed increment). Isolated the precise batch-mode wall blocking `hasTypeRT_subst`
  and designed the clean single-inductive fix that sidesteps it. Runtime groundness invariant (the
  second, separate open item) unchanged.
status: PARTIAL. One green commit (`371918d7`). Soundness.lean left EXACTLY as G23/G24 left it
  (52+/42−, uncommitted, red, no sorry, verified intact — NOT edited). Caveat 5 OPEN (poly-let
  preservation DISCHARGED; closure-body-RT: infra landed, `hasTypeRT_subst` blocked on a single
  well-characterized proof-engineering step + the runtime threading).
kind: progress
component: lean
---

# G1 Phase 6 (Session G25): HasTypeRTAt landed; hasTypeRT_subst inversion wall isolated + fix designed

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake env
lean`/`lake build`. HEAD `32dd2ecd`. `grep -rn sorry Eyg/Types/*.lean` empty throughout, every step.

## Committed (green, `371918d7`)

1. **`Ty.not_mem_levels_substAt`** (Scheme.lean, in `namespace Ty` after `mem_levels_substAt_strong`):
   `(∀ i, ℓ ∉ (σ i).levels) → ℓ ∉ (substAt ℓ σ t).levels`. Direct 12-former induction. A ground
   (level-ℓ-free) σ removes ℓ from the output's level set — every `var ℓ _` leaf becomes an ℓ-free
   `σ _`, no other leaf carries ℓ. This is the exact fact the `hasTypeRT_subst` var/builtin arms need
   to DROP the extra `ℓ` disjunct: for `l ∈ (substAt ℓ σ t0).levels`, `mem_levels_substAt_strong`
   gives `l ∈ t0.levels` (then `l ≠ ℓ` by this lemma, so the input bound `{0,ℓ,s.level}` collapses to
   `{0,s.level}`) or `l ∈ (σ i).levels` (then `l = 0` by groundness).

2. **`HasTypeRTAt ℓ h`** (Typing.lean, right after `HasTypeRT`): the level-ℓ-aware strengthening —
   structurally IDENTICAL to `HasTypeRT` (indexed by the `HasType` derivation; does NOT recurse into
   `lam`/`let_poly` bodies) except the `var`/`builtin` arms bound args by
   `∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = ℓ ∨ l = s.level` (one extra `ℓ` disjunct vs
   `HasTypeRT`'s `{0, s.level}`). This is the precondition `hasTypeRT_subst` consumes: before grounding,
   a legitimately-typed nested-poly body (`\w. a w`, `a : ∀α.α→α` at `[.var 2 0]`) carries args at the
   inner generalization level `ℓ = 2`; `substAt ℓ (ground σ)` grounds them, recovering `HasTypeRT`.

Per-file green: Typing/Scheme + full non-Soundness cone (`lake build … Machine Runtime Generation
Generalization Substitution`, 1762 jobs). Axioms untouched, no `sorry`. Additive.

## `hasTypeRT_subst` NOT landed — the exact batch-mode wall

Wrote the full ~150-line induction (mirror of `hasType_substAt_le`, inducting on `hng : NoGenAt ℓ h`,
bundling `∃ h', HasTypeRT h'`; ground σ; var/builtin arms discharge the ℓ disjunct via the new lemma;
lam/let_poly-defn bodies re-typed via `hasType_substAt_le`; RT-recursive positions via the IH). It
type-checks structurally EXCEPT the six points that must extract a sub-`HasTypeRTAt` witness from
`hrtat`. Both extraction routes fail in batch mode:

- **`cases hrtat` (var/builtin):** `Dependent elimination failed … Decidable.rec` — the type index
  `s.instantiateV args` unfolds to the `if s.arity = 0` (Decidable.rec) that blocks unification.
- **`cases hrtat` (app/let_/let_poly/conv):** re-generalizes the shared HasType indices
  (`retTy`/`bodyTy`/`argTy`), producing `hf✝ ≠ hf` and demanding spurious alternatives ("Alternative
  `conv`/`let_poly` not provided"). `HasType : Prop` gives `cases` no constructor discrimination
  through the derivation index.
- **Node-based `inv_*_rtat` (the trick `inv_var_rt`/`inv_app_rt`/`inv_let_rt` use):** works to invert,
  BUT returns the sub-derivations as fresh **existentials** (its own `argTy_i`/`defnTy_i`) that do not
  defeq-match the `hng`-induction arm's `hf`/`hdefn` — differing existential types, and proof
  irrelevance does not bridge different Props. AND for the shared `.Let` node it must return a
  `let_`/`let_poly` **disjunction** whose dead branch is irreducible (proof irrelevance even makes
  `HasType.let_ … = HasType.let_poly …`, so the wrong disjunct can't be ruled out).

So the wall is: **mixing an induction on one derivation-indexed Prop predicate (`hng`/`hrtat`) with an
inversion of the other** — the inversion's existential witnesses never line up with the induction's arm
variables, and the shared-`.Let`-node forces an unusable disjunction. This is exactly the class of
dependent-elimination bookkeeping that needs live goal-state; it is not a mathematical gap.

## Clean fix (Session-G26 deliverable, needs LSP): one combined inductive, single induction

Merge `HasTypeRTAt` and the needed `NoGenAt` facts into ONE inductive `RTSubstReady ℓ h`, carrying in a
SINGLE recursion:
- `var`/`builtin`: the `{0,ℓ,s.level}` args bound (as now);
- `lam`: `NoGenAt ℓ hbody` **carried, not recursed** (RT.lam needs no body premise; the re-typing does);
- `app`/`let_`: `RTSubstReady` of both sub-derivations;
- `let_poly`: `NoGenAt ℓ hbodydefn` (+ `hne : lvl ≠ ℓ`) carried for the defn, `RTSubstReady hbody` recursed;
- `conv`: `RTSubstReady` of the inner; leaves: nothing.

Induct on `RTSubstReady` ONCE ⇒ every sub-witness (RT bounds AND the carried NoGenAts) is an arm
variable — **no inversion of a second predicate, no existential mismatch, no dead disjunct.** The
produced `h'` is reconstructed exactly as the written proof already does (defeq handles mono/arrow
reshaping via `substCtxAt_cons`/`substSchemeVAt_mono` = `rfl`; the `let_poly` genAtV context via a
packaged-existential `rw [substCtxAt_cons_genAtV]` — both already worked in the written attempt).

**Discharging `RTSubstReady`'s carried NoGenAt fields for free:** `noGenAt_of_lt` (Typing.lean:889)
gives `NoGenAt ℓ h` whenever `ℓ <` the sub-derivation's level. Every `let_poly` body (`lvl+1`) and defn
(`lvl' > lvl ≥ ℓ`) qualifies unconditionally; in the strict `ℓ < lvl` case EVERYTHING qualifies. Only
the non-strict `ℓ = lvl` boundary needs a genuine witness — available at the keystone from `inv_let`'s
`NoGenAt lvl hdefn`. So construction sites (the keystone `genAtV_closure_ready_value_node` + the 4
closure-apply sites) build `RTSubstReady` from that same `NoGenAt` + `noGenAt_of_lt`, no new obligation.

(Alternative to redefining: keep `HasTypeRTAt` as committed and prove `hasTypeRT_subst` by inducting on
`HasTypeRTAt` while carrying `hng` and extracting sub-NoGenAts via `noGenAt_of_lt` for the strict
positions + a SINGLE `cases hng`-free extraction for the `ℓ=lvl` boundary — but `noGenAt_of_lt` does
not cover the `ℓ=lvl` lam/app/let_/conv sub-positions, so the boundary still needs hng-inversion. The
combined `RTSubstReady` avoids this entirely and is strictly cleaner.)

## Still open after this (unchanged from G24)

The **runtime groundness / level-bound invariant** (G24 item 2) that must be threaded through
`MStateWf`/`HasTypeV.closure`/`StackWf*` (both engines) so the four closure-apply sites can SUPPLY a
`RTSubstReady ℓ hbody` witness AND a ground `σ` when they invoke `hasTypeRT_subst`. This is the genuine
runtime-judgment strengthening. Plus: the `builtinApp_arity2`/`instantiateV` mechanical regression
(Soundness ~1938/~2050 + B-mirrors) and the ~66-error B-engine mechanical mirror grind.

## Tree state at stop

- Committed `371918d7`: Scheme.lean (`not_mem_levels_substAt`), Typing.lean (`HasTypeRTAt`). Green.
- `Soundness.lean`: uncommitted, red, unchanged from G23/G24 (52+/42−, no sorry, verified intact).
- `plan/eyg-g1-level-tagged-ty.md`: Session G25 entry appended under Phase 6. This note added.
- Caveat 5 OPEN.
