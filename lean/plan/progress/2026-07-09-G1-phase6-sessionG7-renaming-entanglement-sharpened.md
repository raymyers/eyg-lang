---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G7". The level-renaming metatheorem's residual corner
  sharpened: a uniform tag-based level shift is NOT well-defined there (inner/outer same-tag
  entanglement), the entanglement is NOT excluded by HasTypeRT and DOES occur in sound RT-valid
  derivations, and the precise mechanical obstruction is the non-commutation of same-level
  substitution. One green additive commit: c50bbfe9 (Scheme.lean, substAt_substAt_same).
status: PARTIAL. One green additive commit (c50bbfe9, Scheme.lean). Soundness.lean left exactly as
  found (uncommitted partial migration, untouched — only Read). Caveat 5 OPEN. Full green NOT reached.
  The renaming metatheorem is re-characterized (not a global shift; a per-let_poly fresh-level
  allocation) and remains a multi-session deliverable, best with live LSP.
kind: progress
component: lean (Eyg/Types/Scheme.lean)
---

# G1 Phase 6 (Session G7): the renaming residual corner is inner/outer tag-entanglement

No LSP/MCP this session (canary failed: Read/Grep/Edit + `lake env lean` only).

## What was asked

State + prove (or refute) the **level-renaming metatheorem**: for a `HasType lvl Γ e τ ε` derivation
whose inner `let_poly` generalizes at exactly `lvl` (the residual corner G5/G6 pinned), produce an
ALTERNATE derivation of the *same* judgment where that `let_poly` is shifted to a strictly higher
(fresh) level, `τ`/`ε`/`Γ`/`lvl` unchanged — so `noGenAt_of_lt` discharges the wrapper's
`NoGenAt lvl` premise and `genAtV_closure_ready_value_node` can drop it.

## The chain, re-confirmed

`genAtV_closure_ready_value_node` (Substitution.lean:167) consumes `NoGenAt lvl hbody` via
`inv_lambda_noGenAt`. `NoGenAt` is consumed by `hasType_substAt_le` (Typing.lean:584); its **only**
load-bearing use is the `let_poly` arm's `hne : ℓ ≠ lvl` (line 649), which — with `ℓ ≤ lvl` — recovers
the strict `ℓ < lvl` the arm needs for `substCtxAt_cons_genAtV` / `substSchemeVAt_genAtV` /
`hcleanlvl`. When the keystone substitutes at `ℓ = lvl` (the outer lambda's own gen level) and the body
has a `let_poly` at exactly `lvl`, that arm is unreachable. So `noGenAt_normalize` (via proof
irrelevance + an alternate derivation with body sublevel `> lvl`) is exactly what would let the wrapper
drop the premise.

## Finding 1 (decisive, sharper than G6): a uniform tag shift is ILL-DEFINED in the residual corner

"Bump the lambda body's sublevel from `lvl` to `lvl+1`" needs `HasType lvl (x::Γ) lbody retTy εb`
re-typed as `HasType (lvl+1) …` with the SAME `retTy`/`εb`. That is the weakening G6 already flagged
false. The proposed fix (rename the inner `let_poly`'s vars via a tag shift `substAt lvl (·↦var f)`)
runs into a **representation entanglement**:

- The **outer** lambda's generalized vars live at level `lvl` in `retTy`/`εb` (e.g. `perform`'s effect
  tail, or an escaped inner var — see Finding 2). `genAtV lvl defnTy` MUST quantify these ⇒ they must
  STAY at `lvl`.
- The **inner** `let_poly`'s generalized vars ALSO live at level `lvl`. To decouple from the outer's
  `substAt lvl`, they must MOVE to a fresh `f`.
- Both are the identical leaf `var lvl i` — **indistinguishable by tag**. Any `substAt lvl (·↦var f)`
  moves BOTH (breaking the outer generalization / the fixed `defnTy`); leaving both fixed keeps the
  collision. There is no tag-uniform shift that moves one and fixes the other.

`CtxWfV lvl Γ_inner` (a premise of every `HasType.let_poly`) guarantees the inner let's *context* has
no level-`lvl` vars, so the inner's gen vars are all "born inside" its subtree — which would make
renaming-within-the-subtree well-defined **were it not** that those vars can re-surface in the let's
RESULT type `retTy` (Finding 2). When they do, renaming the subtree changes `retTy`, breaking the
interface. So `CtxWfV` localizes the inner vars to the subtree but does NOT keep them out of the
result type.

## Finding 2: the escape occurs in *sound, RT-valid* derivations — HasTypeRT does not exclude it

Witness `\x. (let h = \z.z in h)`. `h : ∀β. β → β` (inner `let_poly` at `lvl`, `genAtV lvl (fun
(var lvl 0) e (var lvl 0))`, arity 1). The let-body is the variable `h`, instantiated (identity) so
its type is `fun (var lvl 0) e (var lvl 0)`. Hence the outer lambda's `retTy` = `β → β` **contains the
level-`lvl` var** — the inner's gen var, re-surfaced. So `defnTy = fun argTy εb (β→β)` has
`arity(genAtV lvl defnTy) ≥ 1` (the residual `arity ≠ 0` corner) AND an inner `let_poly` at exactly
`lvl`. This is a perfectly sound polymorphic lambda `\x. id : α → (β → β)`.

Crucially it is **`HasTypeRT`**: `HasTypeRT.let_poly` recurses only into the let-body, which is the var
`h` with instantiation args `[var lvl 0]` whose level `lvl = h.level` satisfies `HasTypeRT.var`'s
`l = 0 ∨ l = s.level` bound. So the gap-1 groundness invariant does NOT prevent the escape — it is a
*legitimate* runtime shape, not adversarial noise. (This also independently re-confirms G5's Route-A
refutation: demanding `NoGenAt lvl` as an invariant would reject this valid program.)

## Finding 3: the precise mechanical obstruction is same-level non-commutation

Even though the escape is semantically **benign** (specializing the inner `id` when the outer lambda is
called is sound), the keystone's `substAt lvl` cannot be pushed through the inner `genAtV lvl` node. The
same-level instantiation commutation would require

    substAt lvl σ ((genAtV lvl d).instantiateV args)
      =?= (substSchemeVAt lvl σ (genAtV lvl d)).instantiateV (args.map (substAt lvl σ))

whose two sides reduce (via the new `substAt_substAt_same`, committed this session) to
`substAt lvl (i ↦ substAt lvl σ (args.getD i _)) d` vs `substAt lvl (i ↦ mapped.getD i _)
(substAt lvl σ d)` — the outer-specialization `σ` and the inner-instantiation `args` are applied in
**opposite orders** and do not agree in general. This order-dependence is exactly *why*
`hasType_substAt_le`'s `let_poly` arm demands `ℓ ≠ lvl`: distinct levels commute
(`substAt_substAt_comm`, with `hclean`); the same level does not.

## Re-characterization of the correct metatheorem (redirects future work)

The fix is therefore **NOT** a global "shift levels ≥ ℓ by 1" theorem (ill-defined, Finding 1). It is a
**per-`let_poly` fresh-level normalization**: rewrite the derivation so that *every* `let_poly`
generalizes at a **globally unique** level, strictly greater than every level occurring in the
interface (`Γ`/`τ`/`ε`) and than every other `let_poly`'s level. Under that normal form, a tag DOES
identify its binder, `substAt`-based instantiation never collides, and `noGenAt_of_lt` discharges the
wrapper premise for free (all inner gen levels `> lvl`). The induction allocates a fresh level per
`let_poly` top-down, threading "max level used so far"; the per-node renaming is
`substAt oldLevel (·↦ var freshLevel)` and its bookkeeping is exactly `substAt_substAt_same` +
`substAt_substAt_comm`. This is the genuine multi-session deliverable; it wants live LSP (a ~21-arm
induction with genAtV/instantiateV renaming-commutation, error-prone under batch `lake env lean`).

The alternative narrow route — prove the escape-into-result-type cannot force the residual corner *at
the actual Soundness site* via a value/normal-form argument on the runtime closure — was examined and
is NOT obviously easier: the escape is a sound RT-valid shape (Finding 2), so the argument would need a
genuine principal-type/normal-form fact about runtime closures, comparable in size to the
fresh-allocation induction.

## Finding 4 (refinement — argues route (a) is likely TRUE after all, via a case split)

Findings 1–3 show a *tag-uniform* shift fails, but a case split on whether the inner gen var escapes
recovers a plausible general argument:

- **Non-escaping inner `let_poly`** (its level-`lvl` gen var is used only at concrete / non-`lvl`
  types, e.g. `let h = \z.z in pair (h 1) (h "a")`): the gen var occurs in `defnInner` and in the
  instantiations only, **never in `retTy`/`εb`**. So `substAt lvl (·↦var f)` (fresh `f`) applied to the
  let's subtree renames it cleanly, leaving the interface `Γ`/`τ`/`ε` untouched. The renaming IS
  well-defined here — Finding 1's obstruction does not bite.
- **Escaping inner `let_poly`** (the witness of Finding 2, `let h = \z.z in h`, gen var re-surfaces in
  `retTy` at tag `lvl`): here the inner generalization is **HM-flattened-redundant** — `h` is used at
  exactly the pinned type `fun (var lvl 0) e (var lvl 0)`, and the OUTER `genAtV lvl` already quantifies
  `var lvl 0`. So the SAME judgment is derivable with `h` bound by a **monomorphic `let_`** at type
  `fun (var lvl 0) e (var lvl 0)` — **no inner `let_poly` at `lvl` at all**, whence `NoGenAt lvl` holds
  directly (mono `let_` has no `let_poly`). By proof irrelevance this discharges the wrapper premise for
  the runtime's `let_poly` derivation of the same judgment.

So `noGenAt_normalize` (route (a), fully general) is **plausibly TRUE**: at every inner `let_poly` at
`lvl`, either freshen (non-escaping) or mono-ize (escaping). This is a cleaner and more optimistic
target than "the renaming is false / ill-defined." Caveats before banking it: (i) the mono-ize step is
a genuine principal-types argument (must show every use of `h` is consistent with the single pinned
type when the var escapes); (ii) both steps still compose into an induction over the derivation that is
multi-session and wants live LSP. But the mathematical picture is now: **route (a) is likely true, and
the two sub-cases are individually tractable**, not blocked by a representation wall.

## Landed this session

`Ty.substAt_substAt_same` (`Scheme.lean`, commit `c50bbfe9`): same-level substitution composition,
unconditional. The building block for the per-`let_poly` renaming step. Per-file green, no `sorry`,
axioms unchanged.

## Tree state at stop

- HEAD `c50bbfe9` (one commit above `21251080`). Per-file green: Scheme (incl. the new lemma), Typing,
  Runtime, Machine, Substitution, Generation, Generalization.
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6 partial migration, **untouched**
  this session — only Read), uncommitted. Untracked `.claude/`, this note + plan update.
- `grep sorry Eyg/Types/*.lean`: none (committed HEAD *and* working tree). Whole-project `lake build`
  still fails only on `Soundness.lean`. Caveat 5 remains OPEN.
