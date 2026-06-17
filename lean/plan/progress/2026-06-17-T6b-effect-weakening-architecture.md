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
