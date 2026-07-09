---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G10". Seriously evaluated (and rejected, with proof) the
  finding-3 "fresh-high-level shortcut" that would sidestep the generalization-level-shift sub-lemma;
  landed Session G9 recommendation 1 (the pure re-instantiation equality) as an additive green commit.
status: PARTIAL. One green additive commit (63ed5a67, three lemmas in Scheme.lean). Soundness.lean left
  exactly as found (uncommitted partial migration, untouched). Caveat 5 OPEN. hasType_raise_sublevel /
  generalization-level-shift sub-lemma NOT proved. Full green NOT reached. No LSP/MCP (canary failed:
  Read/Grep/Edit + lake env lean only).
kind: progress
component: lean (Eyg/Types/Scheme.lean)
---

# G1 Phase 6 (Session G10): the shortcut does not sidestep the sub-lemma; equality core banked

No LSP/MCP this session (canary failed). Read/Grep/Edit + `lake env lean` only.

## Task, and the headline result

The parent asked, before diving into the hard `let_poly` re-instantiation arm, to seriously check
whether `genAtV_closure_ready_value_node`'s `NoGenAt`/collision problem can be sidestepped by choosing
a sufficiently fresh/high level (via `Nat`'s unboundedness) plus the already-proven commutation, rather
than a general "raise this derivation" theorem. **It cannot.** Below is the precise obstruction. Then I
banked the genuine, reusable building block (G9 rec 1) that the eventual sub-lemma consumes.

## Why the fresh-level shortcut fails (the decisive argument)

The call site (`Soundness.lean:243`, `preservation_E`'s polymorphic-`let` case) must produce, from the
runtime lambda-node derivation `hdefn : HasType lvl Γ ⟨.Lambda x lbody, la⟩ defnTy ε`,

    ∀ args (level-bounded), HasTypeV (Closure x lbody env) ((genAtV lvl defnTy).instantiateV args).

The generalization level in `(genAtV lvl defnTy)` is **pinned at `lvl` by `HasType.let_poly`** — the
rule *stores* `genAtV lvl defnTy` and types the let-body under it; we are not free to generalize `defnTy`
at some other level. From `inv_lambda hdefn`: body `hbody : HasType lvl' ((x,.mono argTy)::Γ) lbody retTy
εb` with `lvl ≤ lvl'` and `defnTy ≈ .fun argTy εb retTy`.

- `lvl < lvl'`: the strict keystone `genAtV_instantiate_lam_ready` fires (no `NoGenAt`). Already fine.
- `lvl = lvl'` (the residual corner, e.g. `defnPerf`, `advPerf`, `escLam`): the strict keystone needs
  gen-level `< body-sublevel`, i.e. `lvl < lvl` — unavailable.

Every candidate escape re-tags the body's inner `let_poly` schemes, i.e. hits G9 Finding 1's wall:

1. **Raise the body's sublevel** `lvl' → L > lvl` (keep `defnTy` fixed): an inner `let_poly` at the
   body's ambient must move to `L`, forcing its stored `genAtV lvl' innerTy → genAtV L innerTy`.
2. **Relabel `defnTy`'s gen level to a fresh `f`** and instantiate `genAtV f (relabel defnTy)`: to run
   the keystone the *body* must be re-typed with the relabeled `argTy`/`retTy`, which relabels its
   inner gens `lvl → f` while their ambient stays `lvl` — ill-typed unless the ambient shifts too.
3. **Shift the body's levels up uniformly**: same re-tag of inner `genAtV`.

"Pick a fresh high level" specifically fails because the strict keystone requires the gen level to be
**strictly below** the body sublevel: a fresh `f` *above* everything breaks `f < lvl'`; a fresh `f`
*below* `lvl` still collides with the body's inner `let_poly` (all at levels `≥ lvl'` `= lvl`). The
`substAt_substAt_comm` route additionally needs its `hclean` (`σ` avoids the target level), which the
*relabel* map `(·↦ var f)` and the collision args both violate. So the unbounded-`Nat` shortcut has no
purchase on the pinned level.

Proof irrelevance (Session G6) reframes the goal to "*exhibit some* re-derivation of the same lambda
judgment satisfying `NoGenAt lvl`" (`NoGenAt lvl h` is a `Prop` over a `Prop`-index, so defeq across
derivations of the same judgment). Real, but not a shortcut: **constructing** that normalized
re-derivation is exactly the raise. No free lunch. The generalization-level-shift sub-lemma is
irreducibly required — a genuine obstruction, documented, not forced.

## What was banked (green, commit 63ed5a67) — G9 recommendation 1

The pure-equality core of a generalization-level shift, on top of G9's `substAt_congr_freeVarsAt`:

- `Ty.length_filter_levels_relabel {ℓ f d} (hf : f ∉ d.levels)` :
  relabeling `ℓ→f` maps the level-`ℓ` occurrence count to the level-`f` count. The `genAtV`
  arity-preservation core for a *relabel* (complements `length_filter_levels_substAt`, which preserves
  an *untouched* level's count under a level-clean `σ`; a relabel deliberately introduces `f`).
- `Ty.substAt_relabel_getD {ℓ f} (hne : f ≠ ℓ) {d} (hf : f ∉ d.levels) {args}
  (hcov : ∀ i ∈ freeVarsAt ℓ d, i < args.length)` :
  `substAt f (i↦args.getD i (var f i)) (substAt ℓ (·↦var f) d) = substAt ℓ (i↦args.getD i (var ℓ i)) d`.
  The body-level heart. The **coverage** hypothesis `hcov` is exactly G9 Finding 2(a)/(c): under
  application would leave the two sides' *default* leaves at different levels (`var f i` vs `var ℓ i`),
  so the caller must extend `args` to cover every generalized index. Proved by the same leaf-analysis
  induction as `substAt_congr_freeVarsAt` (no `hclean` needed — the coverage kills the defaults).
- `Scheme.instantiateV_genAtV_relabel {ℓ f} (hne) {d} (hf) {args} (hcov)` :
  `(genAtV f (substAt ℓ (·↦var f) d)).instantiateV args = (genAtV ℓ d).instantiateV args`.
  Scheme-level packaging (handles both `arity`-branches via `length_filter_levels_relabel`). The
  `escLam_lvl1/lvl2` and `advPerf_lvl1/lvl2` witnesses in `Typing.lean`'s `section Examples` are its
  by-hand `arity ≤ 2` instances; this is the general statement.

Per-file green: Scheme.lean (incl. the three new lemmas) and Typing.lean both `lake env lean`-clean
(pre-existing warnings only). `grep sorry Eyg/Types/*.lean`: none. Axioms unchanged.

## Remaining to close Caveat 5 (unchanged frontier, now with the equality core in hand)

1. The `hasType_subst`-scale **generalization-level-shift induction on the body derivation** (G9 rec 2):
   raise a body typed at `lvl' = lvl` to a fresh sublevel, re-tagging inner `let_poly` schemes. Its
   `var`/`builtin` arms now consume `substAt_relabel_getD` / `instantiateV_genAtV_relabel` with an
   explicitly-constructed coverage-respecting `args'` (extend each under-applied use with the floating
   `var lvl i`); its `let_poly` arm re-tags the stored scheme with the same equality. This is the large,
   error-prone induction G9 flagged as multi-session under batch `lake` and wanting live LSP.
2. Wire-in per G9 finding 3's shape: drop `NoGenAt` from `genAtV_closure_ready_value_node` (raise the
   body when `lvl' = lvl`, then use the *strict* keystone), which makes the `Soundness.lean:243` call
   site — already written to pass `hdefn` directly, not a `NoGenAt` witness — type-check.
3. Then the mechanical `Soundness.lean` grind + Phase 7.

## Tree state at stop

- HEAD `63ed5a67` (one commit above `f2b1d556`). Per-file green: Scheme (incl. new lemmas), Typing.
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6 partial migration,
  **untouched** this session — only its `:243` call site referenced), uncommitted. Untracked `.claude/`,
  this note. Plan Phase 6 updated with the Session G10 entry.
- `grep sorry Eyg/Types/*.lean`: none. Whole-project `lake build` still fails only on `Soundness.lean`.
  Caveat 5 remains OPEN.
