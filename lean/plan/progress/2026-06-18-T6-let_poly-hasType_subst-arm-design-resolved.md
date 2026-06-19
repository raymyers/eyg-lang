---
date: 2026-06-18
milestone: T6 — `let_poly`: `hasType_subst` arm design RESOLVED + `CtxWf` infra delivered
status: DELIVERED (CtxWf free-var infra, green) + DESIGN RESOLVED (the arm + a refined item-1 nuance)
---

# `let_poly` — `hasType_subst` `let_poly` arm fully designed; `CtxWf` infra green

Continues `2026-06-18-T6-let_poly-levelmap-mono-and-wfbelow-decision.md`. With `LevelMap.mono` and the
constructive `genAt` algebra in hand, this session built the remaining substitution-stability
infrastructure (`CtxWf` + scheme/context free-var metatheory, all green, gen branch) and **worked the
`hasType_subst` `let_poly` arm end-to-end on paper**, resolving exactly what it needs — plus a refinement
to the item-1 "engines never see the level" claim.

## Delivered green (committed, axioms `propext`/`Quot.sound`, build 1772 + spec 104/104)

`Eyg/Types/Generalization.lean`:
- **`Ty.mem_freeVars_shift`** — `i ∈ (shift k t).freeVars ↔ ∃ w ∈ t.freeVars, i = w + k`.
- **`Scheme.freeVars`** (ambient free vars: body vars `≥ arity`, shifted down) + **`Scheme.mem_freeVars`**
  (`m ∈ s.freeVars ↔ m + arity ∈ s.body.freeVars`).
- **`Scheme.substScheme_eq_of_fixes_free`** — a `σ` fixing a scheme's ambient free vars fixes the scheme.
- **`Scheme.mem_freeVars_substScheme`** — `m ∈ (substScheme σ s).freeVars ↔ ∃ p ∈ s.freeVars, m ∈ (σ p).freeVars`.
- **`CtxWf n Γ`** (every binding's ambient free vars `< n`) + **`CtxWf.mono`** (level-monotone) +
  **`ctxWf_cons`** (cons bookkeeping) + **`ctxWf_substCtx`** (`CtxWf n Γ → LevelMap n σ → CtxWf n (substCtx σ Γ)`)
  + **`ctxWf_fixed`** (`CtxWf n Γ` ⟹ the keystone's context-fixing premise `∀σ' fixing [0,n), substCtx σ' Γ = Γ`).

## The `hasType_subst` `let_poly` arm — exactly what it needs (resolved)

State `hasType_subst` with the level-map premise (the let_poly constructor pins its scheme to
`genAt n_lp defnTy` and **stores its own** `CtxWf n_lp Γ`):

```
hasType_subst : HasType Γ e τ ε → Ty.LevelMap n σ → (side: MinLetLevel n e) →
                HasType (substCtx σ Γ) e (Ty.subst σ τ) (Ty.subst σ ε)
```

Induction on the derivation; the **`let_poly` arm** reconstructs `HasType.let_poly` at `substCtx σ Γ`:
- `defnTy' = subst σ defnTy` (from `ihdefn`); the term is unchanged so the value restriction survives.
- scheme `genAt n_lp (subst σ defnTy)` via **`genAt_substScheme`** — needs **`LevelMap n_lp σ`**.
- stored `CtxWf n_lp Γ ⟹ CtxWf n_lp (substCtx σ Γ)` via **`ctxWf_substCtx`** — needs **`LevelMap n_lp σ`**.
- `hbody'` from `ihbody`, rewriting the binding scheme by the same `genAt_substScheme`.

**The only beyond-the-stored-data requirement is `LevelMap n_lp σ`**, obtained from `LevelMap n σ` +
`n ≤ n_lp` via **`LevelMap.mono`**. Notably: **no global `CtxWf` and no `TyWf` hypothesis are needed** —
the `lam`/`app`/`let` arms recurse with the *same* `σ` (the `lam` arm does NOT need `CtxWf` for its
context extension, because `CtxWf` is consumed **only** at `let_poly` nodes, each carrying its own). This
kills the earlier worry that intermediate types (function arg types, let defn types) would need a global
type-var bound: they don't, because `hasType_subst`'s non-`let_poly` arms never consume `CtxWf`.

## ⚠ Refined item-1 nuance: a LIGHT, UNCHANGING let-level invariant the engines do carry

The single residual gate is `n ≤ n_lp` for every `let_poly` reached — i.e. **nested lets have levels ≥
the enclosing substitution level** (`MinLetLevel n e` above). This is *not* derivable from plain
`HasType`; it is a well-formedness of the (static) program's let-levels. The good news that keeps it
cheap:

- The AST nodes reduction walks are **static** — every `let_poly` encountered during reduction is a node
  of the *original* closed program, with its level fixed at typing time. So the let-level-monotonicity is
  a property of the **fixed program**, threadable through preservation as an **unchanging global
  hypothesis** (a constant, re-established trivially each step — reduction creates no new `let_poly` nodes
  with fresh levels).

This **refines** the level-redesign note's optimistic "the engines never mention `n`": the engines must
carry one *light, constant* program-level invariant (let-levels monotone, supplying `n ≤ n_lp` at the
readiness keystone) — far lighter than full `HasTypeAt n` level-indexing (no per-rule level threading, no
type-var bounds in the engine proofs; it is a single unchanging side hypothesis on `MStateWf`). The
keystone `genAt_closure_ready` gains this `MinLetLevel`/`LevelMap`-discharge premise; the push supplies it
from the program invariant. The value-aware `StackWfV` machine coupling is otherwise unchanged.

## Remaining for the slice (now fully specified)

1. **Import + defs**: relocate `substCtx`/`Generalizes`/`genAt` (+ `genArity`/`reindexGen`/`CtxWf`) so
   `Typing.lean` can reference them for the constructor (coupling note's import-ordering resolution).
2. **`HasType.let_poly` constructor** (Typing.lean): value-restricted, scheme `genAt n_lp defnTy`, stores
   `CtxWf n_lp Γ` + `hdefn` + `hbody`. Cascade `hasType_ctxConv` (via `generalizes_ctxConv`),
   `inv_let`(unified)/`hasType_expr_form` (Generation), `weakenEff` (Soundness:57).
3. **`hasType_subst`** re-stated with `LevelMap n σ` + the `MinLetLevel` side; the `let_poly` arm as above
   (Substitution.lean / gen branch only).
4. **Light program let-level invariant** on `MStateWf` (constant, unchanging) supplying `n ≤ n_lp` to the
   readiness keystone at the push. The keystone `genAt_closure_ready` gains the discharge premise.
5. **Machine coupling**: generalized `StackWf.assign` (store a scheme) + value-aware `StackWfV`
   (+ `toStackWf`/inversions/`conv`) + `MStateWf` value case → `StackWfV`; re-green `preservation_E`/`_V`/
   `progress`; **mirror in the B engine**. Example: `let id = \x.x in pair (id 1) (id "a")`.

Items 2–5 remain the all-or-nothing cascade through the two-engine `Soundness.lean` (no standalone-green
sub-increment). This session banked the substitution-stability infra (items needed by 3) and resolved the
arm + the program-invariant question (item 4), so the cascade's proof obligations are now fully pinned.
