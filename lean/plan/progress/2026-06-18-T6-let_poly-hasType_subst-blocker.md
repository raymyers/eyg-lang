---
date: 2026-06-18
milestone: T6 — `let_poly` implementation attempt, STALLED at `hasType_subst`
status: BLOCKER FINDING (typing-layer cascade green up to Generation; hard wall at term-level substitution)
---

# `let_poly` implementation attempt — STALLED at `hasType_subst` (Generalizes is not substitution-stable)

Implemented the typing-layer cascade from the settled design
(`2026-06-18-T6-let_poly-coupling-design-sharpened.md`) and hit a **hard mathematical wall** —
not proof engineering — at step 3 (`hasType_subst`). Reverted to green; WIP saved as
`2026-06-18-T6-let_poly-WIP.patch`.

## What got done (green in isolation, in the patch)
- **Typing.lean** — moved `substCtx`/`substScheme_id`/`substCtx_id`/`Generalizes`/`generalizes_mono`/
  `substCtx_eq_self_iff`/`generalizes_ctxConv` above `HasType` (the import-wrinkle fix); added the
  `HasType.let_poly` constructor; added the `hasType_ctxConv` `let_poly` arm (uses
  `generalizes_ctxConv` — works). `lake build Eyg.Types.Typing` **green**.
- **Generation.lean** — unified `inv_let` to the scheme form `∃ s defnTy, HasType Γ defn defnTy ε ∧
  Generalizes s Γ defnTy ∧ HasType ((x,s)::Γ) body τ ε` (mono arm → `generalizes_mono`; poly arm →
  its `hgen`); added the `hasType_expr_form` `let_poly` arm. `lake build Eyg.Types.Generation`
  **green**.
- **Substitution.lean / Generalization.lean** — deleted the moved defs (kept their other lemmas).

## The wall: `hasType_subst` is FALSE for `let_poly`

`hasType_subst (σ : Nat → Ty) : HasType Γ e τ ε → HasType (substCtx σ Γ) e (subst σ τ) (subst σ ε)`
is proved by induction on the term, for an **arbitrary** σ. The `let_poly` arm must produce
`HasType (substCtx σ Γ) (Let x ⟨λ⟩ body) (subst σ bodyTy) (subst σ ε)`. The body IH types `body`
under `(x, substScheme σ sc)`, so the result scheme is forced to be `substScheme σ sc`, and the
`let_poly` constructor then demands

```
Generalizes (substScheme σ sc) (substCtx σ Γ) (subst σ defnTy)   -- "generalizes_subst"
```

**This is false.** Machine-verifiable counterexample (de Bruijn indices):
- `sc = ⟨1, var 0⟩` (one quantifier, body = the quantified var), `Γ = [(y, .mono (var 1))]`,
  `defnTy = var 0`. `Generalizes sc Γ defnTy` **holds**: `sc.instantiate [t] = t = subst [0↦t] (var
  0)`, and `[0↦t]` fixes `Γ` (it only touches `var 0`, and `FV(Γ) = {1}`).
- Apply `σ = [0 ↦ var 1]` (maps the generalized `var 0` onto `var 1 ∈ FV(Γ)`). Then `substScheme σ
  sc = ⟨1, var 0⟩` (the body var is *bound*, untouched) and `subst σ defnTy = var 1`.
- `Generalizes ⟨1, var 0⟩ (substCtx σ Γ) (var 1)` requires `∀t ∃σ'', t = σ'' 1 ∧ σ'' fixes FV(Γ)
  = {1}`, i.e. `σ'' 1 = t` **and** `σ'' 1 = var 1` for arbitrary `t` — contradiction.

So substituting σ can **collide a generalized variable into `FV(Γ)`**, destroying the
generalization. The condition "σ fixes `FV(Γ)`" does **not** save it either (a second counterexample:
`σ = [0 ↦ var 1]` already fixes `FV(Γ)={1}` yet still collides). The genuinely-needed side condition
is *"σ does not map any generalized variable of `sc` into `FV(Γ) ∪ FV(subst σ defnTy)`"* — a
**freshness / de-Bruijn-level discipline**, exactly the "context-freshness invariant" the PLAN's T6
gen bullet flagged as "comparable to the `fix`/`Handle` invariants", now pinned to its precise site.

## Why this blocks the slice
`hasType_subst` feeds `closure_typed_of_lambda_subst` → `generalizes_closure_ready` (the keystone
that establishes readiness at the `let_poly` push). The keystone substitutes the let-bound lambda's
type; if that lambda's body contains a (nested) `let_poly`, `hasType_subst` must recurse through it
— and cannot, soundly, without the freshness discipline. The induction must be *total* over
`let_poly`, so there is no "skip it" — and a downgrade-to-mono is unsound (the body uses `x`
polymorphically).

## Resolution options (for the next session — this is now the real T6 gen crux)
1. **De-Bruijn *levels* for generalization** — index `Generalizes` by a level `n` (generalize only
   vars `≥ n`, with `σ` in `hasType_subst` constrained to act below `n`), so collisions are
   impossible by construction. Cleanest but threads a level through `HasType`/`hasType_subst`/the
   `StackWf.assign` frame — a structural change.
2. **Restrict `hasType_subst`** with a hypothesis `σ` fixes the generalizable region (or a
   `freeVars`-disjointness premise), and discharge it at every call site (the keystone's σ is a
   *generalizing* substitution — it may itself violate this, so this needs care).
3. **A substitution-stable reformulation of `Generalizes`** — quantify so that the predicate is
   preserved under σ (e.g. carry the generalized variables explicitly as fresh names disjoint from a
   tracked support). Likely equivalent in weight to (1).

`generalizes_subst` being false is the load-bearing discovery: it means the **declarative
`Generalizes` + term-level `hasType_subst` combination chosen in the keystone is not closed under
substitution**, so the value-restriction keystone alone does not suffice — the freshness invariant
the PLAN deferred is *mandatory* and must be designed in (option 1 is the recommended route).

## State
- Reverted; `lake build` 1772 + `lake exe spec` 104/104 green.
- The committed standalone lemmas (`fixes_free_of_subst_eq`, `freeVars_tyEquiv`, `generalizes_ctxConv`)
  remain valid and are reused in the patch.
- WIP diff: `2026-06-18-T6-let_poly-WIP.patch` (Typing+Generation green; Substitution/Generalization
  def-moves; does **not** include Machine/Soundness — the attempt stopped at the `hasType_subst`
  wall before those).
