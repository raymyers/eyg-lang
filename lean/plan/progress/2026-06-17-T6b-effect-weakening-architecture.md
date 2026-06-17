---
date: 2026-06-17
milestone: T6b (fix) / Open Question 3 — effect weakening
status: architecture settled (irreducibility proven); execution checklist ready
supersedes: the "consuming slice" design in 2026-06-17-T6b-effsub-foundation.md
---

# Effect weakening: the irreducible core + the chosen architecture

Building on the `EffSub` foundation (`Eyg/Types/EffSub.lean`), this note settles *how*
to consume it, having rigorously traced every option against the actual proofs. Two
results sharpen the earlier scoping:

## Result 1 — the `StackWf` application-frame change is **irreducible**

For *any* surface design, the application frames must allow the applied function's
latent row to be an `EffSub` of the ambient. Proof that you cannot avoid it:

* **Term-level `weakenEff` (`HasType Γ e τ ε₁ → EffSub ε₁ ε₂ → HasType Γ e τ ε₂`) is
  NOT admissible while `app` is exact-match.** Induction's `app` case has
  `f : (argTy →⟨ε₁⟩ retTy)` at ambient `ε₁`; the IH weakens the *ambient* to `ε₂` but
  leaves the function type's embedded latent at `ε₁`, while exact `app` demands
  `f : (argTy →⟨ε₂⟩ retTy)`. Re-deriving `f` with a weakened *embedded* latent is
  covariant type weakening, not available from the IH, and false for `var`/`builtin`
  (their scheme arrows have fixed latents). This is the covariance wall.
* Hence `fix`'s pure builder (`α →⟨∅⟩ α`, builder body arbitrary) cannot be re-typed
  at the effectful ambient by any admissible lemma; the only place the smaller latent
  can be *accepted* is the frame that applies it.

So `StackWf.arg`/`applyf`/`callwith` must carry `EffSub εf ε` (function latent `εf`,
frame ambient `ε`), decoupling the two. **This is the genuine core of Open Question 3.**

## Result 2 — generalize the `app` rule; do NOT add a `subEff` constructor

Two surface designs both work once the frames carry `EffSub`:

* **(chosen) Generalize `HasType.app`:**
  `HasType Γ f (.fun argTy εf retTy) ε → EffSub εf ε → HasType Γ arg argTy ε →
   HasType Γ ⟨.Apply f arg⟩ retTy ε`.
  With this, term-level `weakenEff` **becomes admissible** (the `app` case threads
  `effSub_trans`; `var`/`lam`/literals/data/`perform` are already `ε`-polymorphic;
  `let_`/`conv` chain the IH — all cases check). Among the inversion lemmas, **only
  `inv_app` changes** (it now yields `∃ argTy εf, EffSub εf ε ∧ …`); the other ~17
  inversions never case on `app`, so they are untouched.
* **(rejected) Add a `HasType.subEff` constructor.** Sound, but it cascades through
  **every** inversion in `Generation.lean` (each `induction h`/`cases h` needs a
  `subEff` arm) and through `hasType_subst`, `hasType_expr_form` — far wider surface
  for the same power. The earlier note (`…effsub-foundation.md`) recommended this;
  Result 2 supersedes it.

## Execution checklist (next session — one atomic slice, no green intermediate)

1. **`Typing.lean`**: `import Eyg.Types.EffSub`; change `app` to the generalized form
   (add the `EffSub εf ε` premise, decouple `εf` from the ambient/`retTy` latent). Fix
   the in-file `example`s (`HasType.app … (Ty.effSub_refl _) …`).
2. **`Machine.lean`**: change `StackWf.arg`/`applyf`/`callwith` to carry `EffSub εf ε`
   (latent `εf`, ambient `ε`). Fix `stackWf_append` and `stackWf_doPerformR_unhandled`
   match arms (`| applyf _ _ ih`→`| applyf _ _ _ ih`, etc.). Mirror in
   `Runtime.lean` `StackSegWf` only if a kept-green proof references those arms.
3. **`Generation.lean`**: rewrite `inv_app` to `∃ argTy εf, Ty.EffSub εf ε ∧
   HasType Γ f (.fun argTy εf τ) ε ∧ HasType Γ arg argTy ε` (the `app` arm gives
   `εf, effSub_refl`; the `conv` arm composes via `effSub_tyEquiv_right` + `congrFun`).
4. **`Soundness.lean`** (the bulk):
   - add `weakenEff` (admissible, by induction on `HasType`; needs the generalized `app`);
   - add `hasTypeV_funWeaken : HasTypeV v (.fun a ε₁ r) → EffSub ε₁ ε₂ →
     HasTypeV v (.fun a ε₂ r)` — closure case via `weakenEff` on the body; the
     operator/builtin `Partial` cases by re-`he` at the weakened arrow (they are pure,
     latent absorbs `EffSub` against `effSub_empty`/the scheme latent);
   - fix every `StackWf.arg/applyf/callwith` construction site (add `effSub_refl _`);
   - fix the `cases hst | arg/applyf/callwith` match arms at `preservation_V` (~435),
     `progress` (~1118), `reduce1Run_done_value_typed`, and `preservation_E`'s `Apply`
     consumer (now `⟨argTy, εf, hsub, hf, harg⟩`; push the `arg` frame with `hsub`);
   - the closure-application crux: fire under ambient `ε` with the body re-typed via
     `weakenEff … hsub` (replacing the current `HasType.conv … hE`, which only worked
     because exact `applyf` gave `TyEquiv εclo ε`).
5. **`Substitution.lean`**: `hasType_subst`'s `app` arm gets the `EffSub` premise
   (needs `subst_effSub : EffSub e₁ e₂ → EffSub (Ty.subst σ e₁) (Ty.subst σ e₂)` — an
   additive lemma, provable since `subst` preserves `EffContains` structure and
   `subst_tyEquiv` preserves the lift/reply equivalences).

After this, `fix`'s `partialFixed` slice (`2026-06-16-T6b-fix-scoping.md`) uses
`hasTypeV_funWeaken` (with `effSub_empty` for the pure builder) at the `Apply builder`
frame — no further `StackWf` work — and `FixPreserves`/`FixNoBadCrash` follow.

The same weakening also closes the standing gap that a **pure builtin can currently
only be applied in a pure ambient** (finding 3, `…fix-scoping.md`): once the frames
accept `εf ⊑ ε`, the effectful fragment finally has effect weakening.

## ⚠ CRITICAL CORRECTION (2026-06-17, found while implementing step 1)

**The membership-based `EffSub` is NOT substitution-stable, so it cannot be the
generalized `app` rule's premise as written above.** Verified with a machine-checked
counterexample (`lake build`, then reverted):

```
EffSub (.var 0) .empty                                    -- HOLDS (a bare row var has
                                                          --   no EffContains members)
¬ EffSub (.effectExtend "a" .string unit .empty) .empty   -- HOLDS
```

So under `σ = [0 ↦ ⟨a:(…)⟩]`, the true `EffSub (var 0) .empty` maps to the **false**
`EffSub ⟨a⟩ .empty`. Hence `subst_effSub : EffSub e₁ e₂ → EffSub (subst σ e₁)
(subst σ e₂)` is **false**, and `hasType_subst`'s `app` arm cannot reconstruct the
weakening premise — the generalized-`app` rule with a bare `Ty.EffSub εf ε` premise
**breaks the existing substitution lemma** that `gen`/`let_poly` (T6) depend on. (A
real derivation hits this: `\y.y` types at latent `var 0`, applied at ambient `.empty`
with the vacuous `EffSub (var 0) .empty`; substitution then has no valid premise.)

Root cause: membership treats a bare row *variable* as carrying no operations, so
`EffSub _ _` goes vacuously true on open tails — correct for the **closed**
effect-safety argument (preservation reasons about closed ambient rows, where
membership is exactly right, and `effSub_empty`/`tyEquiv_effSub` are all
substitution-stable *instances*), but wrong as a *typing-rule premise* that must
survive substitution.

### Revised resolution — use a **substitution-stable** weakening premise

Two viable forms; `fix` needs only the first:

* **(minimal, sufficient for `fix`) empty-restricted weakening.** Allow the function
  latent to be `.empty` (pure function in any ambient): premise `εf = ε ∨ εf = .empty`
  (or a dedicated pure-application path). Both disjuncts are substitution-stable
  (`subst σ ε = subst σ ε`; `subst σ .empty = .empty`), so `hasType_subst` reconstructs
  the `app` arm cleanly. This covers `fix`'s pure builder (latent `∅`) and pure-builtin
  application — i.e. **everything the `fix` slice and finding 3 need**. `EffSub` is still
  the right vehicle (`effSub_empty` is its substitution-stable core); the rule just must
  not admit the vacuous open-variable case.
* **(general, future) row-variable-aware subsumption.** A structural `EffSub'` that does
  **not** go vacuous on a tail variable (Koka/Links-style `ε₁ <: ε₂` preserving the
  shared tail var), which *is* substitution-stable. Larger; only needed for a function
  with a non-empty proper sub-row latent (`⟨a⟩ ⊑ ⟨a,b⟩`), which `fix` does not require.

So the corrected step-1 premise is the empty-restricted form, and the irreducibility
result (Result 1) and the "generalize `app`, not `subEff`" choice (Result 2) **stand** —
only the *premise shape* changes from bare `EffSub εf ε` to the substitution-stable
`εf = ε ∨ εf = .empty`. The membership `EffSub` foundation (`EffSub.lean`) is unaffected
and still used for the closed effect-safety reasoning.
