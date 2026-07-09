---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G8". Sharpens/corrects G7's freshen/mono-ize case
  split. The "escaping" inner let_poly (gen var re-surfaces in retTy) is NOT a separate mono-ize
  case — it is freshenable via re-instantiation, exactly like the non-escaping case. Machine-checked
  with a genuine arity != 0 escape witness. The general metatheorem is thereby a SINGLE lemma
  (`hasType_raise_sublevel`), not a case split. One green additive commit (68f207d3, Typing.lean).
status: PARTIAL. One green additive commit (68f207d3, Typing.lean section Examples). Soundness.lean
  left exactly as found (uncommitted partial migration, untouched — only referenced). Caveat 5 OPEN.
  Full green NOT reached. The residual-corner metatheorem is re-characterized (single re-instantiation
  level-raising induction, not a freshen/mono-ize dichotomy) and remains a multi-session deliverable,
  best with live LSP.
kind: progress
component: lean (Eyg/Types/Typing.lean)
---

# G1 Phase 6 (Session G8): the escaping inner `let_poly` is freshenable via re-instantiation

No LSP/MCP this session (canary failed: Read/Grep/Edit + `lake env lean` only).

## What was asked

Formalize G7's Finding-4 **freshen/mono-ize case split** on whether an inner `let_poly`'s generalized
variable "escapes" into the enclosing lambda's result type: (a) non-escaping ⇒ *freshen* (bump the
inner level, harmless), (b) escaping ⇒ *mono-ize* (rebind the let monomorphically, arguing the escaping
use pins it to one type so generalization was HM-redundant). Then combine into a `NoGenAt`-normalization
induction that discharges `genAtV_closure_ready_value_node`'s residual `NoGenAt lvl` premise.

## Finding (decisive, corrects G7): the "escape ⇒ mono-ize" dichotomy is imprecise — escape is also
freshenable

The mono-ize branch is **not needed**. The escaping case is freshenable by the *same* mechanism as the
non-escaping case, once one accounts for **re-instantiation**.

G7's escape witness is `\x. (let h = \z.z in h)`, where the returned `h`'s scheme's generalized
variable re-surfaces in `retTy = β → β`. G7 read this as: the inner gen var *is* the level-`lvl` var in
`retTy`, so bumping the inner level would move it and break `retTy` — hence mono-ize instead. **But the
level-`lvl` variable in `retTy` is produced by *instantiating* the inner scheme at a lower/outer
variable**, and that instantiation argument is chosen *independently* of the inner scheme's own
generalization level. So the inner level can be moved fresh while the identical argument reproduces the
identical `retTy`:

- **Un-normalized (`lvl' = 1`, escaping):** inner `let_poly` generalizes `h` at level `1`;
  `h : genAtV 1 (var 1 0 → var 1 0)` (`arity 2`); the body `h` is `HasType.var` instantiating that
  scheme at `[var 1 0, var 1 0]`, yielding `retTy = var 1 0 → var 1 0`. Here the level-`1` var in
  `retTy` collides with the gen level.
- **Freshened (`lvl' = 2`):** inner `let_poly` generalizes `h` at level `2`;
  `h : genAtV 2 (var 2 0 → var 2 0)`; the body `h` instantiates that scheme at the **identical**
  `[var 1 0, var 1 0]` (level `1 ≠ 2`), yielding the **identical** `retTy = var 1 0 → var 1 0`.

Both derivations prove the **same judgment** `HasType 1 [] (\x.(let h=\z.z in h))
(integer → (var 1 0 → var 1 0)) empty`. `genAtV 1` of that type is `arity 2` (residual corner), and the
escape is genuine (the inner scheme's gen var truly re-surfaces in the un-normalized `retTy`) — unlike
`advPerf`, whose inner `let_poly` is *vacuous* (`h : int→int`, `arity 0`). The freshened derivation
gives `NoGenAt 1` for free via `noGenAt_of_lt`; by proof irrelevance this discharges `NoGenAt 1` of the
escaping derivation. **No mono-ize, no principal-types argument.**

Landed as permanent green witnesses in `Typing.lean`'s `section Examples`
(`escLam`/`escRetTy`/`escDefnTy`/`escH_defn`/`escH_body`/`escBodyAt`/`escLam_lvl1`/`escLam_lvl2`/
`escLam_lvl2_noGenAt`/`escLam_lvl1_noGenAt`, commit `68f207d3`).

## Why re-instantiation dissolves G7's representation wall

G7 (Finding 1) argued a *tag-uniform* level shift `substAt lvl (·↦ var f)` is ill-defined in the
residual corner because the OUTER lambda's gen vars and the INNER `let_poly`'s gen vars are the
identical leaf `var lvl i` and cannot be separated by tag. That is true **as a syntactic type
substitution**. But the correct transformation is not a substitution on types — it is a *re-elaboration*
of the derivation: at the inner `let_poly` we (i) re-tag its own generalization level to fresh `f` (a
`substAt lvl (·↦ var f)` on its *defn* subtree only — well-defined there, since `CtxWfV lvl Γ` forbids
any level-`lvl` var in the *context*, so the only level-`lvl` vars in the defn are this node's own gen
vars) and (ii) re-instantiate each *use* of the inner var at the same arguments as before. Because the
result type of a use depends only on the instantiation **arguments** (outer/ground types, unchanged),
never on the inner scheme's gen level (bound-and-gone after instantiation), `retTy` is preserved
regardless of whether an outer var re-surfaces there. The outer gen vars in `retTy`/`Γ` are never
touched. There is no tag collision because we never substitute at `lvl` in the *interface*, only in the
inner node's own defn subtree.

## Re-characterization of the correct metatheorem (supersedes G7's split)

The residual corner does **not** need a freshen/mono-ize case split. It needs a **single**
level-raising lemma — the freshen mechanism is universal at lambda-body sites:

    hasType_raise_sublevel :
      HasType lvl Γ e τ ε → CtxWfV lvl Γ → HasType (lvl + 1) Γ e τ ε   -- SAME Γ, τ, ε

Its `let_poly` arm rebuilds the node at ambient `lvl+1`, re-tagging the stored `genAtV lvl d` to
`genAtV (lvl+1) (substAt lvl (·↦var (lvl+1)) d)` on the defn, and threading the identical instantiation
args through the body's `var` uses; the re-instantiation commutation is exactly `substAt_substAt_same`
(G7, `Scheme.lean`) + `substAt_substAt_comm`. The `CtxWfV lvl Γ` precondition (`Typing.lean:51`:
`∀ b ∈ Γ, ∀ l ∈ b.2.body.levels, l < ℓ`) guarantees the context has **no** level-`lvl` binding, so the
raise never has to touch a context scheme — the one fact that makes the induction clean. Applied at the
wrapper's residual `lvl' = lvl` case, one raise gives `lvl' = lvl + 1 > lvl`, whence `noGenAt_of_lt`
discharges `NoGenAt lvl` with zero soundness narrowing.

This is a *cleaner, smaller* target than G7's two-branch split: no mono-ize principal-types argument, no
escape/non-escape predicate to define, no per-`let_poly` global fresh-level allocation bookkeeping — a
single `+1` raise per wrapper invocation. It remains a full (~21-arm) induction with
`genAtV`/`instantiateV` re-instantiation commutation, so it is still multi-session and wants live LSP
(error-prone under batch `lake env lean`); but the *mathematics* is now a single well-posed lemma, not
a dichotomy with a doubtful second branch.

## Caveat (honest)

`hasType_raise_sublevel` was **not** proved this session — only its statement pinned and its `let_poly`
arm's re-instantiation mechanism validated on the concrete witness. The batch-mode risk of a 21-arm
induction (genAtV/instantiateV commutation across every rule) is high; landing it wants interactive
goal-state. What is *banked* this session is the machine-checked refutation of the mono-ize necessity
and the reduction of the residual corner to one lemma.

## Tree state at stop

- HEAD `68f207d3` (one commit above `fba0732c`). Per-file green: Typing (incl. the new witnesses),
  Scheme, Runtime, Machine, Substitution, Generation, Generalization.
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6 partial migration, **untouched**
  this session — only referenced), uncommitted. Untracked `.claude/`, this note + plan update.
- `grep sorry Eyg/Types/*.lean`: none (committed HEAD *and* working tree). Whole-project `lake build`
  still fails only on `Soundness.lean`. Axioms of the touched declarations unchanged (`[propext]`).
  Caveat 5 remains OPEN.
