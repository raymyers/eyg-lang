---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G15". Built the derivation-level generalization-level
  raise (`hasType_raise`) far enough to MACHINE-CONFIRM that the two-modes conflict is real and is
  NOT dodged by the existence/proof-irrelevance framing G14 proposed. The wall is isolated to exactly
  one arm (`let_poly` defn-type relabel) and definitively characterized: relabeling free level-`t`
  tags in a derivation IS the raise itself (self-referential), not reducible to substitution.
status: PARTIAL. Salvaged + committed `ctxWfV_raiseCtx` (per-file green, real infra). `hasType_raise`
  NOT landed (all arms compile except `let_poly`). Soundness.lean left EXACTLY as found. Caveat 5 OPEN.
  Full green NOT reached.
kind: progress
component: lean (Eyg/Types/Typing.lean raise induction + scratch; wall isolated to `let_poly` arm)
---

# G1 Phase 6 (Session G15): the raise induction, built; the two-modes wall, machine-confirmed and isolated

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake env lean`
on a scratch file importing `Eyg.Types.Typing`. This session took G14's recommendation seriously and
actually BUILT `hasType_raise` arm-by-arm to see whether the judgment-fixed existence framing dodges
the G13 two-modes conflict. It does not — but the failure is now precise, isolated, and characterized.

## What was built (and compiles)

`ctxWfV_raiseCtx : CtxWfV lvl Γ → CtxWfV (lvl+o) (raiseCtx t o Γ)` — landed in `Typing.lean`,
per-file green, no `sorry`. Genuine reusable infra: keeps the `let_poly` rule's recorded `CtxWfV`
side-condition valid at the raised ambient. Committed.

`hasType_raise` (in scratch, NOT committed): the derivation-level generalization-level raise
```
theorem hasType_raise {t o N} (ht : 1 ≤ t) (hoN : N ≤ o) (ho : 1 ≤ o)
    {lvl Γ e τ ε} {h : HasType lvl Γ e τ ε} (hlb : LevelsBelow N h) (htlvl : t ≤ lvl)
    (hcf : ∀ b ∈ Γ, t ≤ b.2.level → b.2 = Scheme.genAtV b.2.level b.2.body ∧ ∀ l ∈ b.2.body.levels, l < N) :
    HasType (lvl + o) (raiseCtx t o Γ) e τ ε
```
Output type `τ`, `ε` **held fixed**; ambient `lvl ↦ lvl+o`; context re-tagged by `raiseCtx t o`.
The canonical-context invariant `hcf` threads cleanly through EVERY arm:
- initial `Γ`: vacuous under `CtxWfV t Γ` (a non-vacuous `genAtV k d` has `k ∈ d.levels`, so `k < t`);
- `lam`/`let_`: add `mono` (level 0 `< t`, vacuous);
- `let_poly`: adds `genAtV lvl defnTy` (canonical by defn; `defnTy.levels < N` from `LevelsBelow`).

**All ~20 arms compile except `let_poly`.** `var` (fixed branch via `raiseScheme_of_level_lt`; raised
branch via `raiseScheme_genAtV_instantiateV` reproducing the SAME instantiated type at padded `args'`),
`lam`/`let_` (reconstruct at sublevel `lvl'+o`, `mono` binding fixed by `raiseScheme_mono`), `app`/
`conv`/all atoms are all mechanical and check.

## The wall (machine-confirmed at the `let_poly` arm)

Reconstructing the `let_poly` node at ambient `lvl+o` requires its bound-variable scheme to be
`raiseScheme t o (genAtV lvl defnTy) = genAtV (lvl+o) (substAt lvl (·↦var (lvl+o)) defnTy)` — the raise
re-tags the scheme BODY. So the **defn** sub-derivation must be produced at the RELABELED type
`substAt lvl (·↦var (lvl+o)) defnTy`. But the defn IH (output-fixed) hands the defn back at the
ORIGINAL `defnTy`. Type mismatch — the exact error the compiler reports (`genAtV (lvl+o) defnTy` vs
`genAtV (lvl+o) (substAt lvl … defnTy)`).

**Why no uniform policy fixes it (the two modes, characterized).**
- Within `defnTy`, EVERY level-`lvl` tag is generalized by this `let_poly` (`genAtV lvl` captures all
  level-`lvl` occurrences) ⇒ ALL must relabel `lvl ↦ lvl+o`.
- Within the `let_poly`'s OUTPUT type `bodyTy`, level-`lvl` tags are FREE — escaped via the body's
  instantiation ARGS (e.g. `escRetTy = var 1 0 → var 1 0`, reproduced by re-instantiating the scheme
  at `[var 1 0]`) ⇒ they must STAY.
- Identical tag value `lvl`, opposite requirements, **indistinguishable at the type level**. Hence
  neither "keep output fixed" (breaks the defn) nor "relabel output by `substAt t (·↦var (t+o))`"
  (breaks `escRetTy`, and the outer-lambda/wrapper reconstruction that needs `escDefnTy` FIXED) closes
  both obligations.

**Why it is not reducible to substitution (self-referential).** Relabeling the defn's free level-`lvl`
tags `lvl ↦ lvl+o` cannot go through `hasType_substAt_le`: that lemma requires `σ`'s levels `∈ {0,ℓ}`,
but `σ = (·↦var (lvl+o))` introduces a fresh level `lvl+o ∉ {0,lvl}`. Relabeling free level-`t` tags in
a derivation IS precisely the generalization-level raise at the type level — so the `let_poly` arm of
the raise needs the raise. The `escLam_lvl2`/`advPerf_lvl2` witnesses sidestep this ONLY because their
inner defn is a LEAF (`\z.z`, `\y.y`) trivially re-derivable FRESH at the target level; a general
theorem must relabel free level-`t` tags in an ARBITRARY defn subtree.

## Corrected assessment of G14's framing

G14 conjectured the existence framing "needs NO `raiseCtx` and dodges the two-modes conflict." That is
false: reconstructing an alternate same-judgment lambda whose inner `let_poly` sits above `lvl` still
requires raising the body derivation, whose `let_poly` arm re-tags internally-introduced contexts
(`raiseCtx` DOES appear) and hits the identical defn-relabel wall. The judgment being fixed at the TOP
(outer lambda type) does not fix the judgments of INTERNAL defn sub-derivations, which must move.

## Recommended next step (with LSP)

Formulate the raise as a **mutual pair**:
- (a) `hasType_relabelFree`: relabel free level-`t` tags `t ↦ t+o` in a derivation that has no
  `let_poly` generalizing at `t` inside (`NoGenAt t`-below), producing the type with those tags shifted;
- (b) `hasType_raise` proper (bumps ambient + gen levels, output fixed), whose `let_poly` arm calls (a)
  on the defn to obtain the relabeled `substAt lvl (·↦var (lvl+o)) defnTy` typing.

OR fold the re-instantiation directly into `genAtV_closure_ready_value_node` (G6 shape), re-deriving the
defn fresh at a fresh level rather than transforming an existing derivation — dropping the `NoGenAt lvl`
premise from the wrapper so the Soundness site never has to supply it.

Both want live LSP goal-state for the mutual induction. The arm-by-arm scaffolding, the canonical-ctx
invariant, and `ctxWfV_raiseCtx` are now in place; the residual is purely the (a)/(b) mutual defn arm.

## Tree state at stop

- HEAD advanced by one commit: `ctxWfV_raiseCtx` added to `Typing.lean` + this note + plan update.
- `Typing.lean`, `Substitution.lean`: per-file green. `Soundness.lean`: left EXACTLY as found
  (pre-existing uncommitted 53-line partial migration; ~85 error sites; full green far off — needs the
  raise landed, `mStateWf_E`'s `HasTypeRT` exposure, and the residual `sc.instantiate`/RT re-threading).
- `grep -rn sorry Eyg/Types/*.lean`: none. Axioms unchanged. Caveat 5 OPEN.
