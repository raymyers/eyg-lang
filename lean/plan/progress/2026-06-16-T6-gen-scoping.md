---
date: 2026-06-16
milestone: T6 (let-generalization `gen`)
status: scoped (analyzed, not started — milestone-scale)
---

# T6 `gen`: let-generalization — the type-substitution prerequisite

## Why this isn't a quick slice

The monomorphic `HasType.let_` (`Typing.lean:81`) binds `(x, .mono defnTy)`. Generalizing
means binding `(x, gen Γ ε defnTy)` where `gen` quantifies the type variables free in
`defnTy` but **not** free in `Γ`/`ε` (effect-safe, mirroring `binding.close`/`close_eff`).

Soundness then needs, at the runtime `Assign` frame: when the let's `defn` evaluates to a
value `v` with `HasTypeV v defnTy`, the polymorphic `EnvWf.cons` clause demands
`∀ args, HasTypeV v ((gen …).instantiate args)`. Discharging this requires a **type
substitution lemma** over the *mutual* judgment:

```
HasTypeV v τ        → HasTypeV v (Ty.subst σ τ)
HasType Γ e τ ε     → HasType (Γ.map (substScheme σ)) e (Ty.subst σ τ) (Ty.subst σ ε)
EnvWf env Γ         → EnvWf env (Γ.map (substScheme σ))
```

by mutual induction. The leaves transport via the existing `Ty.subst_tyEquiv`
(`Scheme.lean:69`); the hard cases are the **scheme** ones (`HasType.var`,
`HasType.builtin`, `HasTypeV.partialBuiltin`, `EnvWf.cons`), which go through
`Scheme.instantiate`.

## ⚠ The blocker: the de Bruijn scheme-substitution convention

`Scheme.instantiate ⟨arity, body⟩ args = Ty.subst (fun i => if i < arity then args[i]
else .var i) body` (`Scheme.lean:107`). So **every** `var i` with `i < arity` is treated
as quantified, and `i ≥ arity` as free/ambient. For a type substitution `σ` on the
ambient scope to commute with `instantiate`, `substScheme σ ⟨arity, body⟩` must:

* leave the quantified `var 0 … var (arity-1)` **fixed**, and
* apply `σ` to the free vars `var i` (`i ≥ arity`) **shifted by `arity`** — i.e.
  `substScheme σ ⟨arity, body⟩ = ⟨arity, Ty.subst (fun i => if i < arity then .var i
  else (σ (i - arity)).shift arity) body⟩`, needing a `Ty.shift` (add `arity` to all
  vars) that does **not yet exist**.

The required commutation lemma is roughly
`(s.instantiate args).subst σ = (substScheme σ s).instantiate (args.map (subst σ))`,
whose proof is the standard — but non-trivial — de Bruijn "substitution commutes with
instantiation under a binder" lemma, with the shift bookkeeping.

**Deeper issue surfaced:** `instantiate` clobbers *all* `var i` with `i < arity`, so its
correctness silently assumes the ambient context `Γ` never uses type vars `< (max scheme
arity)` — a convention that is **not enforced anywhere** in the current encoding (T3–T5
never generalized, so no scheme had `arity > 0` outside the closed `Builtins.scheme`
table, and the monomorphic judgment never substituted types). Before `gen`, this
convention must be pinned down (either a global freshness invariant on `Γ`'s vars, or a
reworked scheme encoding with explicit binders/level-indexed vars).

## Recommended plan for next session (one dedicated slice)

1. Decide the type-variable convention (recommended: quantified vars `0..arity-1`, ambient
   vars shifted above — add `Ty.shift` + its `subst`/`tyEquiv` lemmas).
2. `substScheme` + the `instantiate`-commutes-with-`subst` lemma.
3. The mutual type-substitution lemma (the three judgments above).
4. `gen Γ ε defnTy` (effect-safe close) + `HasType.let_poly` rule + `inv_let_poly`.
5. Re-green `preservation`/`progress`: the `Assign` frame for a polymorphic scheme uses
   the type-substitution lemma to discharge `EnvWf.cons`'s `∀ args` clause. **Value
   restriction:** generalize only when `defn` is a syntactic value (lambda/literal), or
   rely on EYG's effect row to gate it (mirror `close_eff` — only generalize effect tails
   that don't escape, Open Question #3).

This is comparable in size to `fix` and `Handle` — its own focused slice. The monomorphic
`let` already in place keeps every existing theorem green; `gen` is purely additive
(a second `let` rule + the subst infrastructure).
