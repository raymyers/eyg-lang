import Eyg.Types.EffRow

/-!
# Effect-row subsumption `EffSub` (Milestone T5/T6 — effect weakening)

The exact-match application frames `StackWf.applyf`/`callwith`
(`Eyg/Types/Machine.lean`) require an applied function's *latent* effect row to
**equal** the frame's ambient row (mirroring gleam's `unify(test_eff, eff)`). That
is sound and sufficient for T3–T5, where every applied function's latent row *was*
the ambient by construction. But two later obligations apply a function whose latent
row is genuinely *smaller* than the ambient:

* **`fix`** (T6b, finding 3 in `progress/2026-06-16-T6b-fix-scoping.md`): the
  fixpoint unrolling applies the **pure** builder (`α →⟨∅⟩ α`) inside the recursion's
  effectful ambient `⟨Log|μ⟩` — exact match would demand `∅ = ⟨Log|μ⟩`.
* a **pure builtin** applied under a non-empty ambient — the same gap, latent `∅`.

Both need **effect weakening / row subsumption**: a function with latent `ε_f` may be
applied at ambient `ε` whenever `ε_f ⊑ ε`. This file supplies that relation and its
metatheory, additively and in isolation (the `StackWf` integration is the consuming
slice). The notion is **semantic / membership-based** — `EffSub ε₁ ε₂` says every
operation of `ε₁` is in `ε₂` (lift/reply up to `TyEquiv`) — which is exactly the
property the soundness argument needs: an op a weakened function emits is in `ε_f`,
hence (by `EffSub`) in the ambient `ε`, so **effect safety survives weakening**.

It is the effect analog of subtyping-by-membership and the natural companion to
`EffContains`/`tyEquiv_effContains` (`Eyg/Types/EffRow.lean`).
-/

namespace Eyg.Types.Ty

/-- `EffSub e₁ e₂`: effect row `e₁` is subsumed by `e₂` — every operation `l`
carried by `e₁` (at its first occurrence) is also carried by `e₂`, with lift and
reply types matching up to `TyEquiv`. The empty row is subsumed by everything; a
`TyEquiv` pair subsume each other (it is the reflexive-symmetric core plus genuine
weakening). -/
def EffSub (e₁ e₂ : Ty) : Prop :=
  ∀ l a b, EffContains e₁ l a b →
    ∃ a' b', EffContains e₂ l a' b' ∧ TyEquiv a a' ∧ TyEquiv b b'

/-- Inversion for `EffContains` on an explicit `effectExtend` head: a membership in
`⟨l':(a',b')|t⟩` is either the head (label `l'`) or a strictly-distinct member of the
tail. Stated on a *variable* head (not a string literal) so the case split never trips
dependent elimination on distinct literals. -/
theorem effContains_extend_inv {l' : String} {a' b' t : Ty} {l : String} {a b : Ty}
    (hc : EffContains (.effectExtend l' a' b' t) l a b) :
    (l = l' ∧ a = a' ∧ b = b') ∨ (l ≠ l' ∧ EffContains t l a b) := by
  cases hc with
  | head => exact .inl ⟨rfl, rfl, rfl⟩
  | tail hne hc' => exact .inr ⟨hne, hc'⟩

/-- Unfolding ergonomics: transport a membership across a subsumption. -/
theorem effContains_mono {e₁ e₂ : Ty} (hs : EffSub e₁ e₂) {l : String} {a b : Ty}
    (hc : EffContains e₁ l a b) :
    ∃ a' b', EffContains e₂ l a' b' ∧ TyEquiv a a' ∧ TyEquiv b b' :=
  hs l a b hc

/-- Reflexivity. -/
theorem effSub_refl (e : Ty) : EffSub e e :=
  fun _ a b hc => ⟨a, b, hc, .refl _, .refl _⟩

/-- Transitivity (compose two weakenings; lift/reply equivalences chain). -/
theorem effSub_trans {e₁ e₂ e₃ : Ty} (h₁ : EffSub e₁ e₂) (h₂ : EffSub e₂ e₃) :
    EffSub e₁ e₃ := by
  intro l a b hc
  obtain ⟨a', b', hc', ha', hb'⟩ := h₁ l a b hc
  obtain ⟨a'', b'', hc'', ha'', hb''⟩ := h₂ l a' b' hc'
  exact ⟨a'', b'', hc'', ha'.trans ha'', hb'.trans hb''⟩

/-- **The empty effect row is subsumed by any row** — the key fact for applying a
*pure* function (latent `∅`) under an effectful ambient (`fix`'s pure builder; pure
builtins). The empty row carries no operations, so the obligation is vacuous. -/
theorem effSub_empty (e : Ty) : EffSub .empty e :=
  fun _ _ _ hc => nomatch hc

/-- A `TyEquiv` pair subsume each other (forward direction). Lets `EffSub` absorb the
row reorderings the typing judgment already reasons up to. -/
theorem tyEquiv_effSub {e₁ e₂ : Ty} (h : TyEquiv e₁ e₂) : EffSub e₁ e₂ :=
  fun l a b hc => (tyEquiv_effContains h).1 l a b hc

/-- Weaken on the left by a `TyEquiv` (rewrite the smaller row). -/
theorem effSub_tyEquiv_left {e₁ e₁' e₂ : Ty} (h : TyEquiv e₁ e₁') (hs : EffSub e₁' e₂) :
    EffSub e₁ e₂ :=
  effSub_trans (tyEquiv_effSub h) hs

/-- Weaken on the right by a `TyEquiv` (rewrite the larger row). -/
theorem effSub_tyEquiv_right {e₁ e₂ e₂' : Ty} (hs : EffSub e₁ e₂) (h : TyEquiv e₂ e₂') :
    EffSub e₁ e₂' :=
  effSub_trans hs (tyEquiv_effSub h)

/-- **Extension by a fresh operation is a weakening.** If `l` does not already occur
in `tail`, then `tail ⊑ ⟨l:(a,b)|tail⟩` — every operation of `tail` survives in the
extended row (it cannot be shadowed by the new head `l`). The freshness guard is
load-bearing: without it, a duplicate `l` in `tail` would be shadowed by the head and
the lift/reply types need not match (Leijen scoped labels). -/
theorem effSub_extend {l : String} {a b tail : Ty}
    (hfresh : ∀ a' b', ¬ EffContains tail l a' b') :
    EffSub tail (.effectExtend l a b tail) := by
  intro l' a' b' hc
  by_cases hll : l' = l
  · subst hll; exact absurd hc (hfresh a' b')
  · exact ⟨a', b', .tail hll hc, .refl _, .refl _⟩

/-! ## Sanity checks -/

-- The empty row (a pure function's latent effect) is subsumed by any ambient row —
-- the `fix` pure-builder case: `∅ ⊑ ⟨Log:(String,unit)⟩`.
example : EffSub .empty (.effectExtend "Log" .string Ty.unit .empty) :=
  effSub_empty _

-- Membership transports across a subsumption (the effect-safety hinge).
example {e₁ e₂ : Ty} (hs : EffSub e₁ e₂) (hc : EffContains e₁ "abort" .string .never) :
    ∃ a' b', EffContains e₂ "abort" a' b' ∧ TyEquiv .string a' ∧ TyEquiv .never b' :=
  effContains_mono hs hc

-- Extending with a fresh head weakens: `⟨abort⟩ ⊑ ⟨log, abort⟩` (log ∉ ⟨abort⟩).
example : EffSub
    (.effectExtend "abort" .string .never .empty)
    (.effectExtend "log" .string Ty.unit (.effectExtend "abort" .string .never .empty)) :=
  effSub_extend (l := "log") (by
    intro a' b' hc
    rcases effContains_extend_inv hc with ⟨h, _, _⟩ | ⟨_, hc'⟩
    · exact absurd h (by decide)
    · nomatch hc')

end Eyg.Types.Ty
