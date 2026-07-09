---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G9". Sharpens G8's single-lemma target. Establishes that
  plain structural `induction h` is *provably insufficient* for `hasType_raise_sublevel`'s `let_poly`
  arm (the recursor fixes the stored generalized scheme, but a `let_poly` at the raised ambient
  requires that scheme re-tagged), so the arm needs a dedicated `hasType_subst`-scale re-instantiation
  sub-lemma — not a one-liner over the two commutation facts. Identifies two concrete edge cases the
  single `escLam` witness does NOT exhibit that make the naive "relabel to lvl+1" subtly wrong.
  One green additive commit (8696f55b, Scheme.lean building block).
status: PARTIAL. One green additive commit (8696f55b, `substAt_congr_freeVarsAt` in Scheme.lean).
  Soundness.lean left exactly as found (uncommitted partial migration, untouched). Caveat 5 OPEN.
  `hasType_raise_sublevel` NOT proved. Full green NOT reached. No LSP/MCP this session (canary failed:
  Read/Grep/Edit + `lake env lean` only).
kind: progress
component: lean (Eyg/Types/Scheme.lean)
---

# G1 Phase 6 (Session G9): why `hasType_raise_sublevel` is not a structural-induction one-liner

No LSP/MCP this session (canary failed). Read/Grep/Edit + `lake env lean` only, as G8 warned.

## What was asked

Prove G8's single target
`hasType_raise_sublevel : HasType lvl Γ e τ ε → CtxWfV lvl Γ → HasType (lvl+1) Γ e τ ε`
(same `Γ`, `τ`, `ε`; only the ambient level bumps) by induction on the derivation, mirroring
`hasType_substAt_le`'s 21-arm structure, with the `let_poly` arm using the `escLam` re-instantiation
mechanism as its template; then wire it into `genAtV_closure_ready_value_node` to discharge the
`NoGenAt lvl` premise in full generality, and grind Soundness.

## Finding 1 (decisive): plain `induction h` cannot do the `let_poly` arm

`induction h` on `HasType lvl Γ e τ ε` (motive generalized over all indices) hands the `let_poly` case:

- `hdefn  : HasType lvl Γ ⟨lam⟩ defnTy ε`
- `hcw    : CtxWfV lvl Γ`
- `hbody  : HasType (lvl+1) ((x, genAtV lvl defnTy) :: Γ) body bodyTy ε`
- `ihdefn : CtxWfV lvl Γ → HasType (lvl+1) Γ ⟨lam⟩ defnTy ε`        -- **defnTy fixed**
- `ihbody : CtxWfV (lvl+1) ((x, genAtV lvl defnTy) :: Γ) →
            HasType (lvl+2) ((x, genAtV lvl defnTy) :: Γ) body bodyTy ε`  -- **scheme fixed**

Goal: `HasType (lvl+1) Γ ⟨Let x lam body⟩ bodyTy ε`.

The **only** rules typing `⟨.Let x (lambda) body⟩` are `let_` (mono), `let_poly`, and `conv`.
`let_` is unsound here (the original `body` is typed under a *polymorphic* `genAtV lvl defnTy`; a mono
rebind rejects any `body` that uses `x` at two types). So we must use `HasType.let_poly` at the raised
ambient `lvl+1` — whose constructor **requires** the stored scheme to be `genAtV (lvl+1) _`
(generalize at *exactly* the ambient). But `ihbody` delivers `body` still under `genAtV lvl defnTy`
(the scheme is an *index* of the sub-derivation, fixed by the recursor — Lean's IH cannot change it).
There is no rule accepting a stored scheme whose generalization level is *below* the ambient. So the
raised body derivation `ihbody` gives is **not usable** to form the `let_poly` node the goal needs.

⟹ The arm genuinely needs a **separate re-instantiation sub-lemma** that rewrites the body's *uses*
of the let-bound `x` — swapping the context binding `genAtV lvl defnTy → genAtV (lvl+1) defnTy₁` and
adjusting the per-use instantiation `args` so each use's type is preserved. That is a
`hasType_subst`-scale induction over `body` (a "generalization-level shift on a context binding"),
**not** a one-liner over `substAt_substAt_same`/`substAt_substAt_comm` as G8's sketch read. G8's
`escLam` witness validated the *equation on the one node*, but hid that the surrounding derivation must
be re-elaborated by a dedicated lemma.

## Finding 2: two edge cases the single `escLam` witness does not exhibit

The `escLam` witness (`escH_body` instantiates `h` at the fully-applied `[var 1 0, var 1 0]`) is a
*best-case* input. A general induction receives arbitrary derivations, where two subtleties bite:

**(a) Under-application leaks a floating level-`lvl` var.** If `body` uses the polymorphic `x` with
**fewer args than its arity**, `instantiateV` leaves the un-provided quantifier slots as `var lvl i`
(its default), and those level-`lvl` leaves flow into `bodyTy`. Minimal case: `let h = \z.z in h`
at ambient `lvl=1` with `h` used at `args = []` types `h : var 1 0 → var 1 0` (a leaked quantifier
var, coincidentally level 1 = gen level). Raising to ambient 2 with `h` re-generalized at level 2
(`genAtV 2 (var 2 0 → var 2 0)`) can only reproduce the *fixed* result `var 1 0 → var 1 0` by
**explicitly instantiating at `args' = [var 1 0]`** — the floating var must be *supplied*, not left as
the (now level-2) default. So the re-instantiation must **extend** each under-applied use's arg list
with the floating `var lvl i`. (`escH_body`'s `[var 1 0, var 1 0]` is exactly this extension already
done by hand; the general lemma must construct it.)

**(b) Pre-existing level-`(lvl+1)` vars in `defnTy` inflate the relabeled arity.** The naive relabel
`defnTy₁ := substAt lvl (·↦ var (lvl+1)) defnTy` is only arity-preserving when `defnTy` has **no**
level-`(lvl+1)` leaves. But `defnTy` is a lambda type whose body sublevel may be `≥ lvl+2`, and an
inner under-applied `let_poly` there can leak a `var (lvl+1) k` into `retTy ⊆ defnTy`. Then relabeling
`lvl → lvl+1` *merges* the generalized set with those pre-existing leaves, so
`genAtV (lvl+1) defnTy₁` has **strictly larger arity** than `genAtV lvl defnTy` — the schemes no
longer correspond and the body cannot re-instantiate. ⟹ The internal relabel must target a
**genuinely fresh** level `f` (greater than every level occurring in the whole derivation), not `lvl+1`
mechanically. (The *ambient* still goes to `lvl+1` for `noGenAt_of_lt`'s sake; the inner
generalization's *own* level is a separate free choice `≥ f`. These two "+1"s are independent, which
G8's "single +1 raise" framing conflated.)

**(c) `genAtV` arity is a *count*, not a max-index.** `genAtV ℓ d`'s arity is
`(d.levels.filter (·=ℓ)).length` (occurrence count), but `instantiateV` indexes the arg list by each
leaf's *own* de-Bruijn index. For `d = var ℓ 5` the arity is `1` while the referenced index is `5`, so
the reconstructed `args'` for (a) must cover **every level-`ℓ` index appearing in `d`**, i.e. its list
length must exceed the *max* such index, not the arity. Any list-based re-instantiation construction
must account for this (or bypass the list interface and work at the `substAt` map level).

## Consequence for the wrapper restructuring (does not dodge the wall)

An attractive alternative to feeding `NoGenAt lvl h`: restructure `genAtV_closure_ready_value_node`
to raise only the lambda *body* `hbody` from `lvl' = lvl` to `lvl+1` (fixed `argTy`/`retTy`/`εb`),
then use the **strict** keystone `genAtV_instantiate_lam_ready` (needs `ℓ < lvl'`, no `NoGenAt`).
`genAtV lvl (.fun argTy εb retTy).instantiateV args` is then unchanged (the arrow components are
fixed). This *would* drop the `NoGenAt` premise entirely — but raising `hbody` is still exactly
`hasType_raise_sublevel` on a body that may itself contain a colliding `let_poly` (e.g. `advPerfBody`,
`escBody`), so it funnels through Finding 1's wall. It does, however, confirm the *right shape* of the
eventual wire-in: **no `NoGenAt` hypothesis at all** — just raise the body and use the strict keystone.

## Why `NoGenAt lvl h` for the runtime's `h` is genuinely not derivable directly

Worth pinning (corrects any lingering "just prove `NoGenAt`" reading): `NoGenAt lvl h` for the
*specific* derivation `h` the runtime hands the wrapper is **false** whenever `h`'s body has a
`let_poly` colliding at `lvl` — its `let_poly` arm demands `lvl ≠ lvl`. Proof irrelevance only helps
*across derivations of the same judgment*, and the raised derivation lives at a **different ambient
level index** (`lvl+1` vs `lvl`), so `HasType (lvl+1) …` and `HasType lvl …` are distinct types and
`NoGenAt lvl` cannot be cast between them. Hence the fix must **re-derive** (raise + strict keystone),
never "prove `NoGenAt` of the given `h`".

## What was banked (green, committed 8696f55b)

`Scheme.substAt_congr_freeVarsAt` — the level-native analog of `subst_congr_free`: two `substAt ℓ`
maps agreeing on `freeVarsAt ℓ t` give equal results. Exactly the congruence the re-instantiation
equality (matching two instantiation maps on the generalized indices) will consume. Per-file green,
axioms unchanged, no `sorry`.

## Recommendation for the next session (wants live LSP)

1. Prove the **pure re-instantiation equality** first, fresh-level form, at the `substAt` map level
   (bypassing the arity/list wart): for `f ≠ ℓ`, `d` with no level-`f` leaves, and maps `g₁ g₂`
   agreeing on the level-`ℓ`/level-`f` correspondence,
   `substAt f g₂ (substAt ℓ (·↦var f) d) = substAt ℓ g₁ d` via `substAt_substAt_comm` +
   `substAt_congr_freeVarsAt` (now available). Then lift to `instantiateV` with an explicit
   `args'` construction respecting Finding 2(a)/(c).
2. Prove the **context-binding generalization-level-shift** sub-lemma for the body (rewrites `x`'s
   uses), by induction over `body` — the genuine `hasType_subst`-scale piece.
3. Assemble `hasType_raise_sublevel` with the easy arms (var/lam/let_/app/literals/conv — each a
   near-verbatim copy of `hasType_substAt_le`'s shape, `lam`/`let_` case-splitting on `lvl' ≥ lvl+1`
   vs `lvl' = lvl` and recursing to raise the body in the latter) plus the `let_poly` arm from (2).
4. Wire in per the "restructured wrapper" shape above: drop `NoGenAt` from
   `genAtV_closure_ready_value_node`, raise the body, use the strict keystone.

The mathematics is a fresh-level generalization-shift substitution lemma (well-posed, and now with its
congruence building block landed), not the single-`+1`-raise the G8 note framed. It is genuinely
multi-session and error-prone under batch `lake env lean`; it wants interactive goal-state.

## Tree state at stop

- HEAD `8696f55b` (one commit above `a370ef17`). Per-file green: Scheme (incl. new lemma), Typing,
  Runtime, Machine, Substitution, Generation, Generalization.
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6 partial migration, **untouched**
  this session — only referenced), uncommitted. Untracked `.claude/`, this note + plan update.
- `grep sorry Eyg/Types/*.lean`: none (committed HEAD *and* working tree). Whole-project `lake build`
  still fails only on `Soundness.lean`. Caveat 5 remains OPEN.
