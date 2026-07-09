---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G11". Sharpens G10's "single generalization-level-shift
  sub-lemma" into a precise TWO-theorem architecture for the derivation-level raise, resolves the
  escaped-var/inner-gen conflation (G7 Finding 1) via var-arm arg-padding (types stay literally fixed),
  and REFUTES a natural shortcut: `hasType_subst` cannot serve the defn-relabel (its σ-range is pinned
  to levels {0,ℓ}, excluding a relabel-to-fresh map). One green additive commit (`26e1f566`, Scheme.lean).
status: PARTIAL. One green additive commit (`26e1f566`, `instantiateV_congr_getD` +
  `instantiateV_pad_default` in Scheme.lean — the var-arm padding congruence). Soundness.lean left
  exactly as found (uncommitted partial migration, untouched). Caveat 5 OPEN. The raise induction NOT
  proved (the two 21-arm inductions + a level-bound remain). Full green NOT reached. No LSP/MCP (canary
  failed: Read/Grep/Edit + `lake env lean` only).
kind: progress
component: lean (Eyg/Types/Scheme.lean)
---

# G1 Phase 6 (Session G11): the raise is a TWO-theorem re-elaboration; `hasType_subst` can't relabel

No LSP/MCP this session (canary failed). Read/Grep/Edit + `lake env lean` only.

## Headline

G10 left the frontier as "the `hasType_subst`-scale generalization-level-shift induction on the body
derivation." This session pins its exact shape and finds it is **two** coupled re-elaborations, not one,
with a specific reason the obvious reuse of `hasType_subst` fails. The pure var-arm building block is
banked green.

## The wrapper only needs an ambient RAISE (no `NoGenAt` premise, no `_le` keystone)

`genAtV_closure_ready_value_node` (`Substitution.lean:167`) currently takes `hng : NoGenAt lvl h`.
The clean wire-in that eliminates it: from `inv_lambda h` get `hbody : HasType lvl' ((x,.mono argTy)::Γ)
lbody retTy εb`, `lvl ≤ lvl'`, `argTy.levels < lvl'`, `defnTy ≈ .fun argTy εb retTy`. **Raise `hbody`'s
ambient `lvl' → L` for any fresh `L > lvl`, keeping context, `retTy`, `εb` LITERALLY FIXED.** Then:

- `noGenAt_of_lt hbody' (lvl < L) : NoGenAt lvl hbody'` — **for free** (no external witness); or, better,
- skip `NoGenAt` entirely: reconstruct the lambda with stored sublevel `L` (`lvl ≤ L`, `argTy.levels <
  lvl' ≤ L`) and fire the **strict** keystone `genAtV_instantiate_lam_ready` (`lvl < L`), then finish via
  `instantiateV_genAtV_tyEquiv` exactly as the current body does.

`CtxWfV lvl' ((x,.mono argTy)::Γ)` (the raise's context precondition) holds: `Γ`'s levels `< lvl ≤ lvl'`
(from `hΓwf`), `argTy.levels < lvl'` (from `hfv`). So the wrapper's `hng`/`hΓpa` premises are dropped;
the runtime site (`Soundness.lean:243`) never supplies them. This is G9 Finding 3's shape, now exact.

## The raise keeps the conclusion type LITERALLY FIXED (resolving G7 Finding 1)

The transformation is `hasType_raise : HasType j Γ e τ ε → CtxWfV j Γ → HasType (j+o) (raiseCtx t o Γ)
e τ ε` — **same `e`, same `τ`, same `ε`**, ambient bumped by a uniform offset `o`, context relabeled.
Two facts make "type fixed" correct despite G7's escaped-var/inner-gen tag conflation:

- **All conclusion types contain only AMBIENT level tags, never bound-inner-gen tags.** A `let_poly`'s
  conclusion is its body's type; its inner generalized variables (level = its ambient) are quantified by
  `genAtV` and only re-enter a result type via *instantiation args* (which reference enclosing/ambient
  vars). So level-`k` tags in any conclusion type are ambient and STAY.
- **`var` nodes absorb the collision by padding args.** The looked-up scheme in the raised context is
  `raiseCtx`-relabeled (`genAtV k d ↦ genAtV (k+o) (substAt k (·↦var(k+o)) d)` for `k ≥ t`). The var
  node produces `(relabelled s).instantiateV args'`; choosing `args' = pad(args)` (extend with the
  scheme's own default leaves so coverage holds) gives, via **`instantiateV_genAtV_relabel`** (G10) and
  the new **`instantiateV_pad_default`** (this session), `(relabelled s).instantiateV args' =
  s.instantiateV args' = s.instantiateV args = τ`. Type fixed. The escaped var (from an unchanged arg)
  stays at its original level; the inner-gen var (in the relabeled *scheme body*) moves — same tag,
  different syntactic position, no uniform type-function needed. G7's "ill-defined tag shift" is not a
  wall once the transformation is derivation-structural (a re-elaboration), as G8 anticipated.

## The `let_poly` arm needs a SECOND theorem — and `hasType_subst` CANNOT be it (refuted shortcut)

At a `let_poly` node (ambient `k ≥ t`), `HasType.let_poly` ties the node ambient = gen level = the stored
scheme's level. Raising the node to ambient `k+o` forces the stored scheme to `genAtV (k+o) defnTy'`
where — for the body's re-instantiations to reproduce their types — `defnTy'` must be
`substAt k (·↦var(k+o)) defnTy` (**relabeled**, level-`k` vars → `k+o`). Hence `hdefn'` must have the
*relabeled* type, NOT the fixed `defnTy` the type-fixed main raise delivers. So the arm needs a
**second** re-typing: raise the defn's ambient `k → k+o` AND relabel its type's level-`k` vars to `k+o`.

**Natural shortcut, and why it fails:** "run the main type-fixed raise on `hdefn`, then apply the existing
`hasType_subst` at level `k` with `σ = (·↦ var (k+o))` to relabel." `hasType_subst`
(`Typing.lean:341`) requires `hσ : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ` — the substitution range may
only introduce levels `0` or the opening level `ℓ = k`. A relabel-to-fresh map produces `var (k+o)`,
level `k+o ∉ {0, k}`. So `hasType_subst` (and `hasType_substAt_le`) is **inapplicable** to the
defn-relabel: it is the *instantiation* direction (range collapses INTO `{0,ℓ}`), whereas the raise's
defn-relabel is the *anti-instantiation / fresh-introduction* direction (range is a FRESH level ABOVE
everything). This is the same orthogonality the plan noted between `hasType_subst` (LevelMap-only) and the
readiness keystone's instantiation substitution — here it bites the defn-relabel specifically.

⟹ A dedicated **fresh-level relabel re-typing theorem** is required:
`hasType_relabel_raise (k o) : HasType j Γ e τ ε → … → HasType (j+o) (raiseCtx t o Γ) e
(substAt k (·↦var(k+o)) τ) (substAt k (·↦var(k+o)) ε)`. Its arm structure mirrors `hasType_subst`'s 21
arms, but with the `{0,ℓ}`-range precondition **replaced by a freshness precondition** (`σ`'s introduced
level is fresh w.r.t. every level in the derivation) — under which `substAt_instantiateV_scheme`
(`Scheme.lean:1273`, already general in `σ`, needing only the disjointness `h`) discharges its `var` arm,
and the fresh target's `≠ k`/`∉ levels` discharge the `let_poly`/`lam` bounds. It ALSO bumps the ambient
(coupled: `let_poly` ties ambient=genlevel), so it is genuinely a distinct induction from `hasType_subst`,
not a specialization. Main (`hasType_raise`, type-fixed) and this companion are mutually recursive (each
`let_poly` arm calls the other on the defn / recurses on the body).

## The freshness bound needs a threaded global level cap

Both inductions relabel `k ↦ k+o` and need `k+o ∉ (that node's defnTy).levels`. A single global offset
`o ≥ N`, with `N` a strict upper bound on EVERY type-level tag anywhere in the derivation, works
uniformly (`k+o ≥ o ≥ N > d.levels`, and `k+o ≠ k`). `N` is a property of the whole derivation (inner
discarded `defnTy`s do not appear in `Γ`/`τ`/`ε`), so it wants a `NoGenAt`-shaped inductive
`LevelsBelow N h` + `∃ N, LevelsBelow N h` (each finite node contributes finitely many levels; take the
max). This is additional mirror machinery (deferred — speculative to land before the inductions consume
it; its exact shape depends on which arms need which local bounds).

## Banked green (commit `26e1f566`, Scheme.lean) — the var-arm padding congruence

- `instantiateV_congr_getD {ℓ d args args'} (h : ∀ i, args'.getD i (var ℓ i) = args.getD i (var ℓ i)) :
  (genAtV ℓ d).instantiateV args' = (genAtV ℓ d).instantiateV args` — a level-`ℓ` scheme's instantiation
  depends on `args` only through the padded lookup `fun i => args.getD i (var ℓ i)`.
- `instantiateV_pad_default {ℓ d} (args extra) : (genAtV ℓ d).instantiateV (args ++ (range extra).map
  (fun j => var ℓ (args.length + j))) = (genAtV ℓ d).instantiateV args` — padding with the scheme's own
  default leaves is instantiation-invariant and extends the length arbitrarily, so the caller meets
  `instantiateV_genAtV_relabel`'s coverage bound (Session G9 Finding 2(a)/(c)) without changing the
  produced type.

Together with G10's `instantiateV_genAtV_relabel`, these fully equip the raise's `var` arm to keep the
conclusion type literally fixed while the looked-up scheme is relabeled. Per-file green (`lake env lean
Eyg/Types/Scheme.lean` EXIT 0), axioms unchanged, no `sorry`.

## Remaining to close Caveat 5 (frontier, now with a concrete architecture)

1. `LevelsBelow N h` inductive + `exists_levelsBelow` (the global level cap).
2. `raiseCtx t o Γ` (relabel `genAtV k` bindings at `k ≥ t`; mono/below-`t` fixed) + lookup/cons lemmas.
3. `hasType_raise` (type-fixed, ambient `+o`) — 21-arm induction; `var` arm via the padding lemmas +
   `instantiateV_genAtV_relabel`; `let_poly` arm delegates the defn to (4).
4. `hasType_relabel_raise` (fresh-level relabel + ambient `+o`) — 21-arm mirror of `hasType_subst` with a
   freshness precondition replacing `{0,ℓ}`; mutually recursive with (3).
5. Drop `NoGenAt`/`PolyAboveFV`-lambda premises from `genAtV_closure_ready_value_node`: raise `hbody` to
   `L > lvl`, use the STRICT keystone `genAtV_instantiate_lam_ready`.
6. Then the mechanical two-engine `Soundness.lean` grind + Phase 7.

The mathematics is now fully de-risked and the architecture precise; steps 3–4 are large, error-prone
21-arm dependent inductions best done with live LSP goal-state (as every prior session has flagged), not
batch `lake env lean`.

## Tree state at stop

- HEAD `26e1f566` (one commit above `59a313cb`). Per-file green: Scheme (incl. the two new lemmas).
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6 partial migration,
  **untouched** this session — only its `:243` call site + the wrapper referenced), uncommitted.
  Untracked `.claude/`, this note + plan update.
- `grep sorry Eyg/Types/*.lean`: none. Whole-project `lake build` still fails only on `Soundness.lean`.
  Caveat 5 remains OPEN.
