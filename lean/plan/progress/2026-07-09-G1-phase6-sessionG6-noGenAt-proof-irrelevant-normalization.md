---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G6". NoGenAt reframed as a JUDGMENT-level property via
  proof irrelevance (correcting the G5 derivation-specific framing); the hardest known residual-corner
  witness shown to satisfy the wrapper's NoGenAt premise via level-normalization. One green additive
  commit: 865d8ac0 (Typing.lean).
status: PARTIAL. One green additive commit (865d8ac0, Typing.lean). Soundness.lean left exactly as
  found (uncommitted partial migration, untouched — only Read). Caveat 5 OPEN. Full green NOT reached;
  the general level-renaming metatheorem is a pinned multi-session deliverable.
kind: progress
component: lean (Eyg/Types/Typing.lean)
---

# G1 Phase 6 (Session G6): `NoGenAt` is judgment-level; residual corner closes via normalization

No LSP/MCP this session (canary failed: Read/Grep/Edit + `lake env lean` only).

## The central question, resolved on the merits

The task asked whether **route (a)** closes the wrapper's residual `NoGenAt lvl hbody` corner
(`arity ≠ 0 ∧ lvl' = lvl`): "if a `lam`/`let_` binder stores body sublevel `lvl' = lvl`, every
`let_poly` reachable in that body must itself generalize at a level `> lvl`" — which would collapse the
residual into the already-solved `lvl' > lvl` case (`noGenAt_of_lt`).

### Finding 1 (structural, decisive): `NoGenAt` is PROOF-IRRELEVANT

`NoGenAt ℓ : HasType lvl Γ e τ ε → Prop` is an inductive `Prop` **indexed by a `HasType` proof**, and
`HasType` is itself a `Prop`. Lean 4's *definitional* proof irrelevance makes any two proofs of the same
`HasType` judgment defeq, so `NoGenAt ℓ h₁` and `NoGenAt ℓ h₂` are the **same type** whenever `h₁`, `h₂`
type the same judgment. Therefore:

- `NoGenAt ℓ h` depends only on the **judgment** `(lvl, Γ, e, τ, ε)`, not on the derivation tree `h`.
  It means exactly: *"this judgment admits SOME derivation none of whose reachable `let_poly` nodes
  generalize at exactly `ℓ`."*
- **This supersedes the G5 note's framing**, which treated `NoGenAt` as a fact about the specific
  runtime derivation and concluded the residual corner needs a genuine external witness. It does not:
  the wrapper's `NoGenAt lvl hdefn` premise is discharged by exhibiting *any* good derivation of the
  same lambda judgment.
- A blocking `cases`/inversion on `NoGenAt` to prove `¬ NoGenAt` is **impossible** (the proof-term index
  is irrelevant — the Lean elaborator refuses to discharge the mismatched `let_`/`conv` alternatives).
  Concretely, the G5-style "the inner `let_poly` at exactly `lvl` makes `NoGenAt lvl` false" claim is
  itself **false**: the same `let h = \y.y in …` body also has a monomorphic-`let` (or higher-level)
  derivation with no `let_poly`-at-`lvl` at all.

### Finding 2 (machine-checked): the hardest known residual-corner witness satisfies `NoGenAt`

Witness (permanent `private` examples in `Typing.lean`'s `section Examples`):
`advPerfLam = \x. (let h = \y.y in perform "op" x)`.

- `advPerf_lvl1 : HasType 1 [] advPerfLam defnPerf .empty` — the residual corner: `genAtV 1 defnPerf`
  has `arity ≠ 0` (effect tail `μ = var 1 0`), stored `lvl' = 1 = lvl`, inner `let_poly` present.
- `advPerf_lvl2 : HasType 1 [] advPerfLam defnPerf .empty` — the SAME judgment, stored `lvl' = 2`,
  inner `let_poly` at level `2`.
- `advPerf_lvl2_noGenAt : NoGenAt 1 advPerf_lvl2` — via `noGenAt_of_lt` (body at level `2 > 1`).
- `advPerf_lvl1_noGenAt : NoGenAt 1 advPerf_lvl1 := advPerf_lvl2_noGenAt` — **type-checks by proof
  irrelevance** (the two derivations are defeq). This is the load-bearing line: the wrapper's premise
  for the un-normalized `lvl' = 1` derivation the runtime hands us is discharged by the normalized one.

So **route (a) holds for this witness**; it is not adversarial.

## Scope: what is settled, what is open

The witness's inner `let_poly` is *vacuous* — `h : int → int` is ground, `genAtV n (int→int)` is
`arity 0` for every `n`, so bumping `lvl'` is a free "renaming" and the observable type `defnPerf` is
untouched. The **general** theorem needs level **RENAMING**, not mere weakening:

> **Level-weakening `HasType n Γ e τ ε → HasType (n+1) Γ e τ ε` (fixed `Γ,τ,ε`) is FALSE** once an
> inner `let_poly` generalizes real level-`n` vars, because `genAtV n d ≠ genAtV (n+1) d` (different
> generalized var-sets ⇒ different arity ⇒ the let-body's instantiation no longer type-checks).

The correct statement is a **`≥ℓ`-level SHIFT** of the whole derivation (types and derivation together).
The informal argument that it preserves observable types — hence route (a)-via-renaming is TRUE in
general:

1. An inner `let_poly` generalizing at level `k` binds all its level-`k` vars via `genAtV k`; after
   generalization those vars are **bound-and-gone** — they do not occur free in the stored scheme.
2. The let-body consumes the scheme only through **instantiation**, whose result depends on the
   instantiation **args**, not on the gen level `k`. Shifting `k ↦ k+1` (and the defn's fresh vars
   correspondingly) leaves every instantiation result unchanged.
3. The outer fixed type `defnTy`/`retTy`/`εb` may mention level `lvl` (e.g. `defnPerf`'s effect tail
   `var 1 0`), but that is a **separate free occurrence** the inner generalization's internal shift
   never touches (the inner vars are bound). So the collision `inner-let_poly-at-lvl` ∧
   `defnTy-mentions-lvl` is resolved by shifting only the inner generalization up.

Proving it is a real metatheorem: a ~21-arm induction over `HasType` applying a level-shift renaming to
`Ty`/`Ctx`/`Scheme`, with `genAtV`/`instantiateV`-shift commutation lemmas (analogous to, but simpler
than, the `substAt` machinery already built). Multi-session, wants live LSP.

## Recommended integration (next session, with LSP)

Fold the normalization **into** `genAtV_closure_ready_value_node` (`Substitution.lean`): prove a
`noGenAt_normalize : ∀ {lvl Γ x lbody la defnTy ε} (h : HasType lvl Γ ⟨.Lambda x lbody, la⟩ defnTy ε),
NoGenAt lvl h` from the level-shift metatheorem, and **drop the wrapper's `NoGenAt lvl h` premise** so
the Soundness `let_poly` preservation site (`Soundness.lean:243`) never has to supply it. This is the
gap-2 residual; gap-1 (`HasTypeRT`) is already wired (Session G2). Then the ~90-error two-engine
`Soundness.lean` mechanical grind (still on old magnitude `HasType` in the B-engine, `soundness_evalR`
still on the old statement) remains — not blind-reachable, per every prior Phase-6 session.

## Tree state at stop

- HEAD `865d8ac0` (one commit above `aa1d8077`). Per-file green: Typing (incl. the new witnesses),
  Runtime, Machine, Substitution, Scheme, Generation, Generalization.
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6 partial migration, **untouched**
  this session — only Read), uncommitted. Untracked `.claude/`, this note + plan update.
- `grep sorry Eyg/Types/*.lean`: none (committed HEAD *and* working tree). Whole-project `lake build`
  still fails only on `Soundness.lean`. Caveat 5 remains OPEN.
