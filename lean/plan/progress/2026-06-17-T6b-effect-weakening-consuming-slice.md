---
date: 2026-06-17
milestone: T6b (fix) / Open Question 3 — effect weakening
status: DELIVERED — green, sorry-free, axioms clean
implements: the consuming slice of 2026-06-17-T6b-effect-weakening-architecture.md
---

# Effect weakening: consuming slice DELIVERED

The `EffSub` foundation's consuming slice (the irreducible `StackWf` application-frame
change + the generalized-`app` surface, per
`2026-06-17-T6b-effect-weakening-architecture.md`) is now in the tree, green and
axiom-clean (`propext`/`Classical.choice`/`Quot.sound`; zero `sorry`; `lake build` +
`lake exe spec` 104/104). The effectful fragment finally has effect weakening, so a
**pure function (latent `∅`) can be applied under any ambient** — the gap `fix`'s pure
builder and pure builtins both hit (finding 3, `2026-06-16-T6b-fix-scoping.md`).

## The premise shape that actually works (refines the architecture note's correction)

The architecture note's correction settled on the substitution-stable premise
`εf = ε ∨ εf = .empty`. **Implemented as the slightly stronger, cleaner**

```
def Ty.EffWeaken (εf ε : Ty) : Prop := TyEquiv εf ε ∨ TyEquiv εf .empty
```

(`Eyg/Types/Ty.lean`). Using `TyEquiv` rather than syntactic `=` is what makes the
term-level `weakenEff` **admissible without** a `tyEquiv_empty_inv` lemma: the `conv`
rule moves the ambient up to `TyEquiv`, and `EffWeaken`'s disjuncts absorb that move
(`effWeaken_trans (.inl hε) …` in both `weakenEff`'s and `inv_app`'s `conv` arms). It is
still substitution-stable (`subst_effWeaken`, `Eyg/Types/Scheme.lean`: `subst σ ε` /
`subst σ .empty = .empty`), so `hasType_subst` survives — the property `gen`/`let_poly`
depend on. Lemmas: `effWeaken_refl`, `effWeaken_empty` (the `∅`-key), `effWeaken_trans`,
`effWeaken_tyEquiv_right`.

## What changed (7 files, one atomic slice — no green intermediate)

1. **`Ty.lean`** — `EffWeaken` + its 4 lemmas (new home, since `TyEquiv` lives here and
   `Typing` must see it; `EffSub.lean` stays the membership relation for closed
   effect-safety reasoning).
2. **`Scheme.lean`** — `subst_effWeaken` (additive, axiom-free).
3. **`Typing.lean`** — generalized `HasType.app`: function latent `εf`, premise
   `Ty.EffWeaken εf ε`. In-file `example`s use `refine HasType.app … (Ty.effWeaken_refl _) …`
   (the weakening must be solved *first* to pin `εf`, else the lambda body's `εb` is an
   unresolved metavar — `apply` left it open).
4. **`Machine.lean`** — `StackWf.arg`/`applyf`/`callwith` decouple latent `εf` from
   ambient `ε`, carrying `Ty.EffWeaken εf ε`; `stackWf_append` arms + the example fixed.
5. **`Generation.lean`** — `inv_app` now yields `∃ argTy εf, EffWeaken εf ε ∧ …`
   (the only inversion that changed — the generalize-`app`-not-`subEff` choice paid off).
6. **`Substitution.lean`** — `hasType_subst`'s `app` arm threads `subst_effWeaken`.
7. **`Soundness.lean`** (the bulk):
   - `weakenEff` (admissible, by `weakenEffAux` induction with the target row explicit —
     a clean motive, sidesteps the revert-the-hypothesis subtlety of
     `induction … generalizing`);
   - `perform_op_mem_ambient` — the effect-safety hinge across weakening: a function whose
     latent is `TyEquiv`-headed by `l` cannot have an *empty*-weakened latent, so the op is
     in the (weakened) ambient `ε`. Used in `reduceCall_perform_wait` (now takes
     `EffWeaken εf ε`) and both progress effect-escape arms;
   - the closure-application **crux** re-types the body at the ambient via
     `weakenEff (HasType.conv hbody hR (.refl _)) (effWeaken_trans (.inl hE) hw)` —
     replacing the old `HasType.conv hbody hR hE`, which only worked because exact
     `applyf` forced `εclo ~ ε`;
   - the `Case`/`partialMatchTwo` pushes its branch via the frame's `hw` (the branch
     latent `= εf`, weakened to `ε`), not `effWeaken_refl`;
   - all `cases hst | arg/applyf/callwith` match arms + the explicit-`@` progress arms
     (`@applyf … hf hwk hrest`, named `hwk` to avoid shadowing progress's value `hw`).

## Builtin-saturation hypotheses: **decoupled, no `EffWeaken` needed**

A builtin partial reaches an application frame at its *scheme* latent (e.g. `∅` for the
pure `pure2` builtins), which the generalized `app` lets differ from the ambient. The
isolated `BuiltinAppPreserves`/`FixPreserves` hypotheses tied function-latent = stack-
ambient, so they no longer matched. **Resolution:** decouple the function-type latent
(`.fun argTy εf retTy`) from the `StackWf` ambient `ε` in `BuiltinAppPreserves` /
`FixPreserves` — *no* `EffWeaken` premise required, because the discharge
(`builtinAppPreserves`) **never uses the function latent** (builtins don't perform; the
result type is read off the codomain only). `BuiltinAppNoBadCrash`/`FixNoBadCrash` carry
no `StackWf`, so their function-latent binder was already free — unchanged. So the
`run_*`/arity-driver machinery (T6a/T6b) is untouched; only the four hypothesis
signatures' latent binders moved.

## ⚠ Finding: `hasTypeV_funWeaken` is NOT a general value lemma — and not needed

The architecture checklist (step 4) listed `hasTypeV_funWeaken : HasTypeV v (.fun a ε₁ r)
→ EffWeaken ε₁ ε₂ → HasTypeV v (.fun a ε₂ r)` for the `fix` slice. **It is false for
operator partials**: `HasTypeV.partialConsNil` (and every operator/builtin partial) pins
its arrow's latent *rigidly* to the scheme's (`∅` for `Cons`/`Select`/…), via the
constructor's `TyEquiv` to the rigid scheme arrow. So a `Partial .Cons []` typed at
`.fun a ε₁ r` forces `ε₁ ~ ∅`, and it **cannot** be re-typed at a non-empty `ε₂` — our
`HasTypeV` is stricter than the analyzer (which would let a pure value take any latent).
The **closure case is fine** (re-type the body via `weakenEff`, rebuild the arrow at
`ε₂`), and that is the only shape `fix`'s builder is.

**But `hasTypeV_funWeaken` is not actually needed**: when `fix`'s `fixed` partial applies
the builder, it does so by **pushing an application frame** (`applyf`/`callwith`), and
those frames already carry `EffWeaken εf ε`, so the closure-application crux weakens the
builder's body directly — no standalone value-weakening lemma. So `hasTypeV_funWeaken` is
**dropped** from the deliverable; the `fix` slice gets weakening from the frames it
pushes. (If a value-level weakener is ever wanted, it must be scoped to closures.)

## Remaining for `fix` (unchanged, now unblocked)

`partialFixed` (`2026-06-16-T6b-fix-scoping.md`): a bespoke `HasTypeV.partialFixed` rule
+ ~5-site `HasTypeV` cascade, discharging `FixPreserves`/`FixNoBadCrash`. The pure builder
is applied under the recursion's effectful ambient via the now-`EffWeaken`-carrying
`applyf` frame with `effWeaken_empty` — no further `StackWf` work.
