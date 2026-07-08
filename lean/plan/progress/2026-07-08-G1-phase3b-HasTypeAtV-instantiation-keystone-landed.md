---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 3b: obstruction (A) RESOLVED — the level-native term judgment `HasTypeAtV`, its instantiation-direction re-typing induction `hasTypeAtV_substAt`, and the level-native readiness keystone `genAtV_instantiate_lam_ready`, all landed additively, non-vacuous on the nested Caveat-5 term
status: one green additive commit (new file `Eyg/Types/TypingAtV.lean`); obstruction (A) from the previous session is closed; only obstruction (B) (the value judgment `HasTypeV.closure`/`EnvWf` on magnitude `HasType`) remains for the *value*-typing keystone
kind: progress
component: lean (Eyg/Types/TypingAtV.lean, Eyg.lean)
---

# G1 Phase 3b: `HasTypeAtV` + the instantiation-direction re-typing + the level-native readiness keystone

Continuation of `progress/2026-07-08-G1-phase3b-readiness-keystone-two-obstructions-located.md`. That
session confirmed the down-shift wall is removed at the mathematics level and located two plumbing
obstructions: **(A)** no `substAt ℓ` re-typing induction on a `genAtV`-storing judgment exists yet, and
**(B)** `Runtime.lean`'s value judgment is stated on the magnitude `HasType`. This session **resolves
(A) in full** and delivers the level-native readiness keystone at the term level. **(B) is untouched,
as scoped** (out of scope for this session).

## What landed (one additive commit, new file `Eyg/Types/TypingAtV.lean`)

### 1. `HasTypeAtV lvl Γ e τ ε` — the level-native sibling of `HasTypeAt`

The ~21-constructor parallel of `HasType`/`HasTypeAt` built on the level-native scheme machinery:

- `let_poly` generalizes at **exactly** `lvl` via `Scheme.genAtV lvl` (not the magnitude `genAt`),
  records `CtxWfV lvl Γ` (bounding `Ty.levels`, not `Scheme.freeVars`), types its body at `lvl + 1`,
  carries **no `noLambdaLet`** (nested `Let`-binds-`Lambda` genuinely accepted).
- `lam`/`let_` store an explicit sublevel `lvl'` with `lvl ≤ lvl'` and the **`Ty.levels`-shaped**
  freshness premise `∀ l ∈ argTy.levels, l < lvl'` (differs from `HasTypeAt`'s `Scheme.freeVars`-shaped
  one — precisely because `CtxWfV` bounds `Ty.levels`).
- `var`/`builtin` instantiate via the level-native `Scheme.instantiateV` (consistent with the schemes
  `let_poly` stores; a magnitude `instantiate` would mismatch `genAtV`'s level-native quantifiers).

### 2. `hasTypeAtV_substAt` — the instantiation-direction re-typing induction (obstruction A)

Re-type a derivation under an **outer** level-`ℓ` substitution `substAt ℓ σ`, under the hypotheses
`hℓ : ℓ ≠ 0`, `hlt : ℓ < lvl`, `hσ : ∀ i, ∀ l ∈ (σ i).levels, l ≤ ℓ`, and a context invariant
`PolyAbove ℓ Γ` (every polymorphic — `arity ≠ 0` — binding sits at a level strictly above `ℓ`). This is
the *opening* lemma the readiness keystone needs — orthogonal to `hasTypeAt_subst`, which is the
*ambient/weakening* (`LevelMap`) direction. New supporting lemmas:

- **`length_filter_levels_substAt`** — `substAt ℓ σ` (`ℓ ≠ k`, `σ` `k`-clean) preserves the count of
  level-`k` occurrences (neither removes existing ones — it rewrites only level-`ℓ` leaves — nor
  introduces new ones). Hence **`substSchemeVAt_genAtV`**: `substSchemeVAt ℓ σ (genAtV k d)
  = genAtV k (substAt ℓ σ d)`, the level-native `genAt_substScheme` — **unconditional in the level
  dimension** (only `ℓ ≠ k` + freshness, no `LevelMap`). This is the `let_poly`-arm context rewrite
  (`substCtxAt_cons_genAtV`).
- **`substAt_instantiateV_scheme`** — the `var`-arm commutation for an *arbitrary* scheme: either mono
  (`arity = 0`, short-circuited unconditionally) or at a level `≠ ℓ` with `σ` clean there. Covers every
  binding a well-formed `HasTypeAtV` context can hold (mono from `lam`/`let_`, `genAtV`-above-`ℓ` from
  nested `let_poly`); `PolyAbove` + `Ty.clean_of_levels_lt` discharge the side-conditions.
- **`substAt_instantiateV_closed`** + **`Ty.substAt_substAt_comm_of_no_mem`** — the `builtin`-arm
  commutation. Builtins live at level `0`, so `σ` (which produces level-`0` ambient content) is *not*
  clean w.r.t. their level; but their bodies have **no** level-`ℓ` occurrence (`ℓ ≠ 0`), so the
  cross-level commutation holds with no cleanness at all. `Builtins.scheme_levels_zero`/`scheme_no_level`/
  `scheme_substSchemeVAt` establish the level-`0`-closedness.
- `Ty.substAt_tyEquiv`/`substAt_effWeaken`/`mem_levels_substAt`, `substCtxAt`(+`_lookup`/`_fix`),
  `ctxWfV_substCtxAt` — the mechanical threading (conv/app arms, context reconstruction).

The `PolyAbove` invariant is preserved by `lam`/`let_` (add mono, `arity 0`) and `let_poly` (adds a
level-`lvl > ℓ` generalization). The whole induction is **non-vacuous for arbitrarily deep nesting** —
the `let_poly` arm fires on a `Let`-binds-`Lambda` node the magnitude `hasType_subst` cannot reach.

### 3. `genAtV_instantiate_lam_ready` — the level-native readiness keystone (term level)

For a let-bound lambda presented via its `lam` components at ambient level `ℓ` — body at a strictly
higher level `lvl'`, context `Γ` below `ℓ` (so `substAt ℓ` fixes it, `substCtxAt_fix`), args' levels
`≤ ℓ` — **every** instantiation of the generalized scheme `genAtV ℓ (.fun argTy εb retTy)` is achieved
by a genuine `substAt ℓ`-instantiation of the lambda's own `HasTypeAtV` derivation. Composes
`genAtV_generalizesAtV` (each `instantiateV` is a `substAt ℓ` instance) with `hasTypeAtV_substAt`.
Handles the `arity = 0` (vacuous) and `arity ≠ 0` (genuine argument-map) instantiations uniformly.

**Explicitly does NOT** wire in `Value.Closure`/`HasTypeV`/`EnvWf` — that is obstruction (B), a future
session. This is exactly the term-level ingredient the value-typing side will consume.

### 4. The nested non-vacuous demonstration

`hInnerV` types the inner core `let inner = \y.y in inner x` at ambient level `2` (inner generalized to
`∀β. β → β` at level `2`, applied to the level-`1` `x : α`) — a `Let`-binds-`Lambda` node.
`hOuterV_instantiate` runs the keystone on the outer lambda `\x. (let inner = \y.y in inner x)` at
ambient level `1` (body = `hInnerV` at the strictly higher level `2`), producing the lambda re-typed at
`(genAtV 1 (α → α)).instantiateV [integer]`. `hOuterV_typed_integer_arrow` reduces that instantiation
(by `rfl`) to `Integer → Integer`: the outer type variable `α` (level `1`) is **genuinely replaced** by
`integer`, while the **nested inner** scheme (level `2` ≠ `1`) is correctly re-generalized during the
`substAt 1` re-typing (`substSchemeVAt_genAtV`). The level-native "wall falls" check — the outer scheme
opened non-vacuously through a term the original `generalizes_closure_ready` chain reaches only
vacuously, with the inner scheme untouched because the two generalization levels are distinct.

## Key design decisions (the non-mechanical points)

- **`substAt ℓ` is the instantiation motion; `ℓ < lvl` strict, not `ℓ ≤ lvl`.** The re-typing induction
  opens at level `ℓ`; every enclosed `let_poly` at level `lvl₀` must satisfy `ℓ ≠ lvl₀` for the scheme
  commutation. Threading `ℓ < lvl` (strict) makes `ℓ ≠ lvl₀` automatic (levels are non-decreasing under
  binders). The keystone therefore does *not* apply the induction to the lambda node itself (ambient
  `ℓ`, where `ℓ < ℓ` fails) — it peels the `lam` and applies the induction to the **body** at `lvl' > ℓ`
  (hence the keystone takes the `lam` components, requiring `ℓ < lvl'` — true in the non-vacuous case,
  where the generalized level-`ℓ` variable forces the freshness bump).
- **`PolyAbove`, not `CtxWfV ℓ`, is the context invariant for the `var` arm.** `CtxWfV ℓ Γ` bounds body
  levels `< ℓ` (wrong direction for a `genAtV`-above-`ℓ` binding). The re-typing needs
  `ℓ ≠ s.level` + `σ` clean w.r.t. `s.level` for a looked-up polymorphic scheme; `PolyAbove ℓ Γ`
  (poly-bindings at level `> ℓ`) supplies both (with `hσ`'s `≤ ℓ` bound). This scopes the induction to
  derivations where captured polymorphic bindings are **fresher** than the opening level — exactly the
  nested-generalization shape (inner schemes at higher levels), which is the non-vacuous case the
  keystone targets.
- **`σ`'s levels `≤ ℓ`, not `< ℓ`.** The instantiation witness `fun i => args.getD i (.var ℓ i)`
  mentions level `ℓ` itself (the identity slots), so the clean-above-`ℓ` bound must be `≤ ℓ`; it still
  gives cleanness w.r.t. every inner level `> ℓ` via `Ty.clean_of_levels_lt` (with `n = ℓ + 1`).

## What this closes / what remains

- **Obstruction (A) is closed.** The `substAt ℓ` re-typing induction on a `genAtV`-storing judgment
  exists, is non-vacuous for arbitrary depth, and the level-native readiness keystone
  `genAtV_instantiate_lam_ready` is proved on the real 12-former `Ty`/`Scheme`.
- **Obstruction (B) remains (scoped out).** Turning the term-level re-typing into
  `HasTypeV (Value.Closure x lbody env) (instantiate …)` still needs either a parallel value judgment
  `HasTypeVAt`/`EnvWfAt` (which will consume `genAtV_instantiate_lam_ready` per instantiation) or Phase
  4's `noLambdaLet` drop from `HasType.let_poly`. This is the next session's deliverable.
- No new mathematical uncertainty surfaced. The only scoping choice (the `PolyAbove` fresher-than-`ℓ`
  invariant) is precisely the nested-generalization discipline; a captured *lower*-level polymorphic
  binding used polymorphically inside a value-restricted lambda is the separate concern the value
  restriction already governs, and is not exercised by the keystone.

## Current state

Tree green at HEAD (one commit this session on top of `0f1423f8`): `lake build` 1776 jobs, `lake exe
spec` 104/104 evaluation + 104/104 FBS≡interpreter + 21/21 round-trip + 21/21 CID, `#print axioms` for
`soundness`/`soundness_evalR` (and `hasTypeAtV_substAt`/`genAtV_instantiate_lam_ready`/
`hOuterV_typed_integer_arrow`) = `[propext, Classical.choice, Quot.sound]`, no `sorry` in
`Eyg/Types/*.lean`. Purely additive — every previously load-bearing declaration
(`HasType`/`hasType_subst`/`HasType.let_poly`, `HasTypeAt`/`hasTypeAt_subst`, `Generalizes`/
`generalizes_closure_ready`/`closure_typed_of_lambda_subst`, `Runtime.lean`, `Soundness.lean`)
untouched; the only edits outside the new file are the `import` line in `Eyg.lean` and this plan/note.
