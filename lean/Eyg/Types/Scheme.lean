import Eyg.Types.Ty

/-!
# Type substitution, schemes & the builtin table (Milestone T2)

Type substitution (`Ty.subst`), polymorphic schemes (`Scheme`) with
`instantiate`, and the primitive/builtin scheme tables — transcribed from
`packages/gleam_analysis/src/eyg/analysis/inference/levels_j/contextual.gleam`
(`pure1`/`pure2`/`pure3`, `q`, `builtins()`) and `.../type_/binding.gleam`
(`instantiate`).

## Substitution is capture-free *by construction*

EYG `Ty` has **no internal binders** — every `var i` (de Bruijn) refers to one
flat scope (a `Scheme`'s quantifier prefix, or the ambient typing context).
Quantification lives only at the `Scheme` boundary. So substitution is a plain
structural `var`-replacement with **no index shifting and no capture-avoidance** —
the simplification de Bruijn-at-the-leaves buys us.

## Monomorphic first (plan T2/T6)

`instantiate` (open a scheme by substituting its quantified vars) is delivered
here; **generalization `gen` is deferred to T6**. Slices T3–T5 use monomorphic
`let` plus these polymorphic *builtin* schemes, which exercises everything except
let-polymorphism.
-/

namespace Eyg.Types

namespace Ty

/-! ## Type substitution -/

/-- Apply a type-variable substitution `σ` structurally. No shifting is needed
(`Ty` has no internal binders). -/
def subst (σ : Nat → Ty) : Ty → Ty
  | .var 0 i => σ i
  | .var (l+1) i => .var (l+1) i
  | .fun a e r => .fun (subst σ a) (subst σ e) (subst σ r)
  | .binary => .binary
  | .integer => .integer
  | .string => .string
  | .list a => .list (subst σ a)
  | .record r => .record (subst σ r)
  | .union r => .union (subst σ r)
  | .empty => .empty
  | .rowExtend l f t => .rowExtend l (subst σ f) (subst σ t)
  | .effectExtend l a b t => .effectExtend l (subst σ a) (subst σ b) (subst σ t)
  | .never => .never
  | .promise a => .promise (subst σ a)

@[simp] theorem subst_var (σ : Nat → Ty) (i : Nat) : subst σ (.var 0 i) = σ i := rfl

/-- Composition of substitutions (`subst` is functorial in `σ`). -/
theorem subst_subst (σ τ : Nat → Ty) (t : Ty) :
    subst σ (subst τ t) = subst (fun i => subst σ (τ i)) t := by
  induction t with
  | var l i => cases l <;> simp_all [subst]
  | _ => simp_all [subst]

/-- Identity substitution is the identity. -/
theorem subst_id (t : Ty) : subst (fun i => .var 0 i) t = t := by
  induction t with
  | var l i => cases l <;> simp_all [subst]
  | _ => simp_all [subst]

/-- **Substitution preserves row equivalence** (plan T2: `subst` commutes with
`RowEquiv`). Labels and the `l ≠ l'` swap guards are untouched by `subst`, so
every `TyEquiv` derivation transports through it. -/
theorem subst_tyEquiv (σ : Nat → Ty) {s t : Ty} (h : TyEquiv s t) :
    TyEquiv (subst σ s) (subst σ t) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congrFun _ _ _ iha ihe ihr => exact .congrFun iha ihe ihr
  | congrList _ ih => exact .congrList ih
  | congrRecord _ ih => exact .congrRecord ih
  | congrUnion _ ih => exact .congrUnion ih
  | congrPromise _ ih => exact .congrPromise ih
  | congrRow _ _ ihf iht => exact .congrRow ihf iht
  | congrEff _ _ _ iha ihb iht => exact .congrEff iha ihb iht
  | swapRow hne => simp only [subst]; exact .swapRow hne
  | swapEff hne => simp only [subst]; exact .swapEff hne

/-- **`EffWeaken` is substitution-stable.** Both disjuncts survive: `subst` preserves
`TyEquiv` (`subst_tyEquiv`), and `subst σ .empty = .empty` definitionally. This is what
lets `hasType_subst` reconstruct the generalized `app` rule's weakening premise — the
reason `EffWeaken` (not the membership `EffSub`) is the rule's premise. -/
theorem subst_effWeaken (σ : Nat → Ty) {e₁ e₂ : Ty} (h : EffWeaken e₁ e₂) :
    EffWeaken (subst σ e₁) (subst σ e₂) := by
  rcases h with h | h
  · exact .inl (subst_tyEquiv σ h)
  · exact .inr (subst_tyEquiv σ h)

/-! ### Index shifting (`Ty.shift`)

`Ty` has no internal binders, so a *shift* (renumber every variable up by `k`) is
just the substitution `var i ↦ var (i + k)`. It is the bookkeeping a scheme's
ambient (free) variables need when a substitution crosses the scheme's quantifier
prefix: ambient var `j` lives at de Bruijn index `j + arity` inside the body, so a
substitute supplied for it must be shifted up by `arity`. -/

/-- Shift every type variable up by `k` (`Ty` has no internal binders). -/
def shift (k : Nat) (t : Ty) : Ty := subst (fun i => .var 0 (i + k)) t

@[simp] theorem shift_zero (t : Ty) : shift 0 t = t := by
  unfold shift; simpa using subst_id t

/-- Substituting through a shift: `subst σ (shift k t) = subst (σ ∘ (· + k)) t`. -/
theorem subst_shift (σ : Nat → Ty) (k : Nat) (t : Ty) :
    subst σ (shift k t) = subst (fun i => σ (i + k)) t := by
  simp only [shift, subst_subst, subst_var]

/-! ### Free variables

The de Bruijn type variables occurring in a type. A substitution that **agrees with
the identity** on every free variable of `t` leaves `t` unchanged — the fact that
lets `gen` conclude its generalizing substitution fixes the surrounding context
(whose free variables are disjoint from the generalized ones). -/

/-- The list of type variables occurring in a type (with multiplicity; membership
is what matters). -/
def freeVars : Ty → List Nat
  | .var 0 i => [i]
  | .fun a e r => freeVars a ++ freeVars e ++ freeVars r
  | .list a => freeVars a
  | .record r => freeVars r
  | .union r => freeVars r
  | .promise a => freeVars a
  | .rowExtend _ f t => freeVars f ++ freeVars t
  | .effectExtend _ a b t => freeVars a ++ freeVars b ++ freeVars t
  | _ => []

/-- Generalization **arity** at level `n`: one quantifier slot per generalized variable (`≥ n`) of
`d`, sized so every such variable fits (`v - n < genArity` for `v ≥ n` free in `d`). Closed-below-`n`
types get arity `0` (monomorphic). (T6 `let_poly` generalization; relocated here so the `let_poly`
typing rule can reference `Scheme.genAt`.) -/
def genArity (n : Nat) (d : Ty) : Nat := (d.freeVars.map (fun v => v + 1 - n)).foldr Nat.max 0

/-- The re-indexing turning `d` into a level-`n` scheme body with `arity` quantifiers: ambient vars
(`< n`) shift up past the prefix; generalized vars (`≥ n`) become quantifier `v - n`. -/
def reindexGen (n arity : Nat) : Nat → Ty :=
  fun v => if v < n then .var 0 (v + arity) else .var 0 (v - n)

/-- **A substitution that fixes every free variable fixes the type.** -/
theorem subst_eq_of_fixes_free {σ : Nat → Ty} {t : Ty}
    (h : ∀ i ∈ freeVars t, σ i = .var 0 i) : subst σ t = t := by
  induction t with
  | var l i =>
      cases l with
      | zero => exact h i (by simp [freeVars])
      | succ n => rfl
  | «fun» a e r iha ihe ihr =>
      simp only [freeVars, List.mem_append] at h
      simp only [subst, iha (fun i hi => h i (Or.inl (Or.inl hi))),
        ihe (fun i hi => h i (Or.inl (Or.inr hi))), ihr (fun i hi => h i (Or.inr hi))]
  | list a ih => simp only [subst, ih (fun i hi => h i hi)]
  | record r ih => simp only [subst, ih (fun i hi => h i hi)]
  | union r ih => simp only [subst, ih (fun i hi => h i hi)]
  | promise a ih => simp only [subst, ih (fun i hi => h i hi)]
  | rowExtend l f t ihf iht =>
      simp only [freeVars, List.mem_append] at h
      simp only [subst, ihf (fun i hi => h i (Or.inl hi)), iht (fun i hi => h i (Or.inr hi))]
  | effectExtend l a b t iha ihb iht =>
      simp only [freeVars, List.mem_append] at h
      simp only [subst, iha (fun i hi => h i (Or.inl (Or.inl hi))),
        ihb (fun i hi => h i (Or.inl (Or.inr hi))), iht (fun i hi => h i (Or.inr hi))]
  | _ => rfl

/-- **Converse of `subst_eq_of_fixes_free`.** If a substitution fixes a type, it fixes
each of its free variables pointwise: a free var sits at a leaf, so for the substituted
type to match it must map to itself. The pair characterizes `subst σ t = t` exactly, and
is what `let_poly`'s `generalizes_ctxConv` needs (rewriting a context binding up to
`TyEquiv` preserves the free-var set, so a context-fixing `σ` keeps fixing it). -/
theorem fixes_free_of_subst_eq {σ : Nat → Ty} {t : Ty}
    (h : subst σ t = t) : ∀ i ∈ freeVars t, σ i = .var 0 i := by
  induction t with
  | var l j =>
      cases l with
      | zero =>
          intro i hi; simp only [freeVars, List.mem_singleton] at hi; subst hi
          simpa only [subst] using h
      | succ n => intro i hi; simp only [freeVars] at hi; nomatch hi
  | «fun» a e r iha ihe ihr =>
      simp only [subst, Ty.fun.injEq] at h
      intro i hi; simp only [freeVars, List.mem_append] at hi
      rcases hi with (hi | hi) | hi
      · exact iha h.1 i hi
      · exact ihe h.2.1 i hi
      · exact ihr h.2.2 i hi
  | list a ih =>
      simp only [subst, Ty.list.injEq] at h; intro i hi; exact ih h i hi
  | record r ih =>
      simp only [subst, Ty.record.injEq] at h; intro i hi; exact ih h i hi
  | union r ih =>
      simp only [subst, Ty.union.injEq] at h; intro i hi; exact ih h i hi
  | promise a ih =>
      simp only [subst, Ty.promise.injEq] at h; intro i hi; exact ih h i hi
  | rowExtend l f t ihf iht =>
      simp only [subst, Ty.rowExtend.injEq] at h
      intro i hi; simp only [freeVars, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ihf h.2.1 i hi
      · exact iht h.2.2 i hi
  | effectExtend l a b t iha ihb iht =>
      simp only [subst, Ty.effectExtend.injEq] at h
      intro i hi; simp only [freeVars, List.mem_append] at hi
      rcases hi with (hi | hi) | hi
      · exact iha h.2.1 i hi
      · exact ihb h.2.2.1 i hi
      · exact iht h.2.2.2 i hi
  | _ => intro i hi; simp only [freeVars] at hi; nomatch hi

/-- **`TyEquiv` preserves the free-variable set.** Row equality only swaps distinct
labels and is a congruence, so it neither introduces nor removes type variables. -/
theorem freeVars_tyEquiv {s t : Ty} (h : TyEquiv s t) :
    ∀ i, i ∈ freeVars s ↔ i ∈ freeVars t := by
  induction h with
  | refl => intro i; exact Iff.rfl
  | symm _ ih => intro i; exact (ih i).symm
  | trans _ _ ih1 ih2 => intro i; exact (ih1 i).trans (ih2 i)
  | congrFun _ _ _ iha ihe ihr =>
      intro i; simp only [freeVars, List.mem_append]; rw [iha i, ihe i, ihr i]
  | congrList _ ih => intro i; simp only [freeVars]; exact ih i
  | congrRecord _ ih => intro i; simp only [freeVars]; exact ih i
  | congrUnion _ ih => intro i; simp only [freeVars]; exact ih i
  | congrPromise _ ih => intro i; simp only [freeVars]; exact ih i
  | congrRow _ _ ihf iht =>
      intro i; simp only [freeVars, List.mem_append]; rw [ihf i, iht i]
  | congrEff _ _ _ iha ihb iht =>
      intro i; simp only [freeVars, List.mem_append]; rw [iha i, ihb i, iht i]
  | swapRow _ => intro i; simp only [freeVars, List.mem_append]; tauto
  | swapEff _ => intro i; simp only [freeVars, List.mem_append]; tauto

/-- **Two substitutions agreeing on every free variable produce the same result.**
The generalization of `subst_eq_of_fixes_free` (which is the `σ₂ = id` case). -/
theorem subst_congr_free {σ₁ σ₂ : Nat → Ty} {t : Ty}
    (h : ∀ i ∈ freeVars t, σ₁ i = σ₂ i) : subst σ₁ t = subst σ₂ t := by
  induction t with
  | var l i =>
      cases l with
      | zero => exact h i (by simp [freeVars])
      | succ n => rfl
  | «fun» a e r iha ihe ihr =>
      simp only [freeVars, List.mem_append] at h
      simp only [subst, iha (fun i hi => h i (Or.inl (Or.inl hi))),
        ihe (fun i hi => h i (Or.inl (Or.inr hi))), ihr (fun i hi => h i (Or.inr hi))]
  | list a ih => simp only [subst, ih (fun i hi => h i hi)]
  | record r ih => simp only [subst, ih (fun i hi => h i hi)]
  | union r ih => simp only [subst, ih (fun i hi => h i hi)]
  | promise a ih => simp only [subst, ih (fun i hi => h i hi)]
  | rowExtend l f t ihf iht =>
      simp only [freeVars, List.mem_append] at h
      simp only [subst, ihf (fun i hi => h i (Or.inl hi)), iht (fun i hi => h i (Or.inr hi))]
  | effectExtend l a b t iha ihb iht =>
      simp only [freeVars, List.mem_append] at h
      simp only [subst, iha (fun i hi => h i (Or.inl (Or.inl hi))),
        ihb (fun i hi => h i (Or.inl (Or.inr hi))), iht (fun i hi => h i (Or.inr hi))]
  | _ => rfl

/-- **Free variables of a substituted type.** A variable is free in `subst σ t` iff
it is free in `σ v` for some `v` free in `t`. The standard characterization needed to
track how a substitution moves the free-variable set (used for the generalization
arity's stability under level-map substitution). -/
theorem mem_freeVars_subst {σ : Nat → Ty} {t : Ty} {i : Nat} :
    i ∈ freeVars (subst σ t) ↔ ∃ v ∈ freeVars t, i ∈ freeVars (σ v) := by
  induction t with
  | var l j =>
      cases l with
      | zero =>
          simp only [subst, freeVars, List.mem_singleton]; constructor
          · intro h; exact ⟨j, rfl, h⟩
          · rintro ⟨v, rfl, h⟩; exact h
      | succ n =>
          simp [subst, freeVars]
  | «fun» a e r iha ihe ihr =>
      simp only [subst, freeVars, List.mem_append, iha, ihe, ihr]; constructor
      · rintro ((⟨v,hv,hi⟩|⟨v,hv,hi⟩)|⟨v,hv,hi⟩)
        · exact ⟨v, Or.inl (Or.inl hv), hi⟩
        · exact ⟨v, Or.inl (Or.inr hv), hi⟩
        · exact ⟨v, Or.inr hv, hi⟩
      · rintro ⟨v, (hv|hv)|hv, hi⟩
        · exact Or.inl (Or.inl ⟨v, hv, hi⟩)
        · exact Or.inl (Or.inr ⟨v, hv, hi⟩)
        · exact Or.inr ⟨v, hv, hi⟩
  | list a ih => simpa only [subst, freeVars] using ih
  | record r ih => simpa only [subst, freeVars] using ih
  | union r ih => simpa only [subst, freeVars] using ih
  | promise a ih => simpa only [subst, freeVars] using ih
  | rowExtend l f t ihf iht =>
      simp only [subst, freeVars, List.mem_append, ihf, iht]; constructor
      · rintro (⟨v,hv,hi⟩|⟨v,hv,hi⟩)
        · exact ⟨v, Or.inl hv, hi⟩
        · exact ⟨v, Or.inr hv, hi⟩
      · rintro ⟨v, hv|hv, hi⟩
        · exact Or.inl ⟨v, hv, hi⟩
        · exact Or.inr ⟨v, hv, hi⟩
  | effectExtend l a b t iha ihb iht =>
      simp only [subst, freeVars, List.mem_append, iha, ihb, iht]; constructor
      · rintro ((⟨v,hv,hi⟩|⟨v,hv,hi⟩)|⟨v,hv,hi⟩)
        · exact ⟨v, Or.inl (Or.inl hv), hi⟩
        · exact ⟨v, Or.inl (Or.inr hv), hi⟩
        · exact ⟨v, Or.inr hv, hi⟩
      · rintro ⟨v, (hv|hv)|hv, hi⟩
        · exact Or.inl (Or.inl ⟨v, hv, hi⟩)
        · exact Or.inl (Or.inr ⟨v, hv, hi⟩)
        · exact Or.inr ⟨v, hv, hi⟩
  | binary => simp [subst, freeVars]
  | integer => simp [subst, freeVars]
  | string => simp [subst, freeVars]
  | empty => simp [subst, freeVars]
  | never => simp [subst, freeVars]

/-! ### Level-tagged substitution (`substAt`), ported from the G1 spike onto the real `Ty`

`plan/eyg-g1-level-tagged-ty.md` Phase 3b: `Scheme.genAt`/`instantiate`/`substScheme` are to become
level-native, substituting only at one target level `ℓ` and leaving every other level's `var`
leaves untouched — no reindexing. `LevelTagSpike.lean` validated the two commutation facts this needs
on a toy `var`/`fn`-only model; this section ports both onto the **real**, 12-former `Ty` (the audit
flagged as still-open in `progress/2026-07-08-G1-phase3a-done-phase3b-scoped.md` continuation spec
step 5) — confirming, as expected, that none of the extra formers (`list`/`record`/`union`/`promise`/
row & effect extension) touch `var` specially, so both facts hold unconditionally the same way. -/

/-- The `(idx)` occurrences of `t` at exactly level `ℓ` — the level-parameterized generalization of
`freeVars` (which is `freeVarsAt 0`, see `freeVars_eq_freeVarsAt_zero`). -/
def freeVarsAt (ℓ : Nat) : Ty → List Nat
  | .var l i => if l = ℓ then [i] else []
  | .fun a e r => freeVarsAt ℓ a ++ freeVarsAt ℓ e ++ freeVarsAt ℓ r
  | .list a => freeVarsAt ℓ a
  | .record r => freeVarsAt ℓ r
  | .union r => freeVarsAt ℓ r
  | .promise a => freeVarsAt ℓ a
  | .rowExtend _ f t => freeVarsAt ℓ f ++ freeVarsAt ℓ t
  | .effectExtend _ a b t => freeVarsAt ℓ a ++ freeVarsAt ℓ b ++ freeVarsAt ℓ t
  | _ => []

theorem freeVars_eq_freeVarsAt_zero (t : Ty) : freeVars t = freeVarsAt 0 t := by
  induction t with
  | var l i => cases l <;> simp [freeVars, freeVarsAt]
  | _ => simp_all [freeVars, freeVarsAt]

/-- Every distinct level occurring anywhere in a type (own quantifiers and ambient references
alike) — the level-tag analog of the spike's `Ty2.levels`. Used by the `CtxWf`-style
freshness-threading bridge (`clean_of_levels_lt`). -/
def levels : Ty → List Nat
  | .var l _ => [l]
  | .fun a e r => levels a ++ levels e ++ levels r
  | .list a => levels a
  | .record r => levels r
  | .union r => levels r
  | .promise a => levels a
  | .rowExtend _ f t => levels f ++ levels t
  | .effectExtend _ a b t => levels a ++ levels b ++ levels t
  | _ => []

/-- Substitute at a single level `ℓ`: rewrite every `var ℓ i` leaf via `σ i`; leaves at any other
level are untouched. No shifting anywhere, unlike `subst`/`reindexGen` composed with magnitude
bookkeeping — this is the primitive Phase 3b's level-native `Scheme.genAt`/`instantiate`/
`substScheme` are built from. (`subst σ = substAt 0 σ` definitionally, `subst_eq_substAt_zero`.) -/
def substAt (ℓ : Nat) (σ : Nat → Ty) : Ty → Ty
  | .var l i => if l = ℓ then σ i else .var l i
  | .fun a e r => .fun (substAt ℓ σ a) (substAt ℓ σ e) (substAt ℓ σ r)
  | .binary => .binary
  | .integer => .integer
  | .string => .string
  | .list a => .list (substAt ℓ σ a)
  | .record r => .record (substAt ℓ σ r)
  | .union r => .union (substAt ℓ σ r)
  | .empty => .empty
  | .rowExtend l f t => .rowExtend l (substAt ℓ σ f) (substAt ℓ σ t)
  | .effectExtend l a b t => .effectExtend l (substAt ℓ σ a) (substAt ℓ σ b) (substAt ℓ σ t)
  | .never => .never
  | .promise a => .promise (substAt ℓ σ a)

theorem subst_eq_substAt_zero (σ : Nat → Ty) (t : Ty) : subst σ t = substAt 0 σ t := by
  induction t with
  | var l i => cases l <;> simp [subst, substAt]
  | _ => simp_all [subst, substAt]

/-- `substAt ℓ σ` never removes a leaf at a level other than `ℓ`. -/
theorem mem_freeVarsAt_substAt_of_ne {ℓ l' i : Nat} {σ : Nat → Ty} {t : Ty}
    (hl : l' ≠ ℓ) (h : i ∈ freeVarsAt l' t) : i ∈ freeVarsAt l' (substAt ℓ σ t) := by
  induction t with
  | var l j =>
      by_cases hlj : l = l'
      · subst hlj
        simpa only [substAt, if_neg hl] using h
      · simp only [freeVarsAt, if_neg hlj] at h
        exact absurd h (by simp)
  | «fun» a e r iha ihe ihr =>
      simp only [freeVarsAt, List.mem_append] at h
      simp only [substAt, freeVarsAt, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (iha h))
      · exact Or.inl (Or.inr (ihe h))
      · exact Or.inr (ihr h)
  | list a ih => simpa only [substAt, freeVarsAt] using ih h
  | record r ih => simpa only [substAt, freeVarsAt] using ih h
  | union r ih => simpa only [substAt, freeVarsAt] using ih h
  | promise a ih => simpa only [substAt, freeVarsAt] using ih h
  | rowExtend l f t ihf iht =>
      simp only [freeVarsAt, List.mem_append] at h
      simp only [substAt, freeVarsAt, List.mem_append]
      rcases h with h | h
      · exact Or.inl (ihf h)
      · exact Or.inr (iht h)
  | effectExtend l a b t iha ihb iht =>
      simp only [freeVarsAt, List.mem_append] at h
      simp only [substAt, freeVarsAt, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (iha h))
      · exact Or.inl (Or.inr (ihb h))
      · exact Or.inr (iht h)
  | _ => nomatch h

/-- **A level with no occurrence in `t` is untouched by a substitution at that level.** The
converse-shaped fact to `mem_freeVarsAt_substAt_of_ne`, and the key step in the cross-level
commutation below. -/
theorem substAt_eq_self_of_not_mem {ℓ : Nat} {σ : Nat → Ty} {t : Ty}
    (h : ∀ i, i ∉ freeVarsAt ℓ t) : substAt ℓ σ t = t := by
  induction t with
  | var l i =>
      by_cases hl : l = ℓ
      · subst hl; exact absurd (List.mem_singleton_self i) (by simpa [freeVarsAt] using h i)
      · simp only [substAt, if_neg hl]
  | «fun» a e r iha ihe ihr =>
      simp only [freeVarsAt, List.mem_append] at h
      simp only [substAt, iha (fun i hi => h i (Or.inl (Or.inl hi))),
        ihe (fun i hi => h i (Or.inl (Or.inr hi))), ihr (fun i hi => h i (Or.inr hi))]
  | list a ih => simp only [substAt, ih (fun i hi => h i hi)]
  | record r ih => simp only [substAt, ih (fun i hi => h i hi)]
  | union r ih => simp only [substAt, ih (fun i hi => h i hi)]
  | promise a ih => simp only [substAt, ih (fun i hi => h i hi)]
  | rowExtend l f t ihf iht =>
      simp only [freeVarsAt, List.mem_append] at h
      simp only [substAt, ihf (fun i hi => h i (Or.inl hi)), iht (fun i hi => h i (Or.inr hi))]
  | effectExtend l a b t iha ihb iht =>
      simp only [freeVarsAt, List.mem_append] at h
      simp only [substAt, iha (fun i hi => h i (Or.inl (Or.inl hi))),
        ihb (fun i hi => h i (Or.inl (Or.inr hi))), iht (fun i hi => h i (Or.inr hi))]
  | _ => rfl

/-- **Cross-level commutation, conditionally.** Substituting at `ℓ1` and at `ℓ2` commute — for `ℓ1 ≠
ℓ2` — *provided* `σ`'s range never mentions level `ℓ2` (`hclean`). Ported from the spike's
`Ty2.substAt_substAt_comm`; confirms the extra 10 formers (beyond the spike's `var`/`fn`) don't
disturb the argument, since none of them touch `var` specially. This is exactly `Scheme.
subst_instantiate`'s missing piece once `hasType_subst` is level-parameterized (Phase 3b step 6). -/
theorem substAt_substAt_comm {ℓ1 ℓ2 : Nat} (hne : ℓ1 ≠ ℓ2) {σ : Nat → Ty} (τ : Nat → Ty)
    (hclean : ∀ i, ∀ j, j ∉ freeVarsAt ℓ2 (σ i)) (t : Ty) :
    substAt ℓ1 σ (substAt ℓ2 τ t) = substAt ℓ2 (fun i => substAt ℓ1 σ (τ i)) (substAt ℓ1 σ t) := by
  induction t with
  | var l i =>
      by_cases h2 : l = ℓ2
      · simp [substAt, h2, if_neg (Ne.symm hne)]
      · by_cases h1 : l = ℓ1
        · have hne2 : l ≠ ℓ2 := h1 ▸ hne
          simp only [substAt, if_pos h1, if_neg hne2]
          exact (substAt_eq_self_of_not_mem (fun j => hclean i j)).symm
        · simp only [substAt, if_neg h1, if_neg h2]
  | «fun» a e r iha ihe ihr => simp only [substAt, iha, ihe, ihr]
  | list a ih => simp only [substAt, ih]
  | record r ih => simp only [substAt, ih]
  | union r ih => simp only [substAt, ih]
  | promise a ih => simp only [substAt, ih]
  | rowExtend l f t ihf iht => simp only [substAt, ihf, iht]
  | effectExtend l a b t iha ihb iht => simp only [substAt, iha, ihb, iht]
  | _ => rfl

/-- A level occurring as a free-variable's level (at any index) is among `t`'s `levels`. -/
theorem mem_levels_of_mem_freeVarsAt {t : Ty} {ℓ j : Nat} (hmem : j ∈ freeVarsAt ℓ t) :
    ℓ ∈ t.levels := by
  induction t with
  | var l k =>
      by_cases hlℓ : l = ℓ
      · subst hlℓ; simp only [levels, List.mem_singleton]
      · simp only [freeVarsAt, if_neg hlℓ] at hmem
        exact absurd hmem (by simp)
  | «fun» a e r iha ihe ihr =>
      simp only [freeVarsAt, List.mem_append] at hmem
      simp only [levels, List.mem_append]
      rcases hmem with (hmem | hmem) | hmem
      · exact Or.inl (Or.inl (iha hmem))
      · exact Or.inl (Or.inr (ihe hmem))
      · exact Or.inr (ihr hmem)
  | list a ih => exact ih hmem
  | record r ih => exact ih hmem
  | union r ih => exact ih hmem
  | promise a ih => exact ih hmem
  | rowExtend l f t ihf iht =>
      simp only [freeVarsAt, List.mem_append] at hmem
      simp only [levels, List.mem_append]
      rcases hmem with hmem | hmem
      · exact Or.inl (ihf hmem)
      · exact Or.inr (iht hmem)
  | effectExtend l a b t iha ihb iht =>
      simp only [freeVarsAt, List.mem_append] at hmem
      simp only [levels, List.mem_append]
      rcases hmem with (hmem | hmem) | hmem
      · exact Or.inl (Or.inl (iha hmem))
      · exact Or.inl (Or.inr (ihb hmem))
      · exact Or.inr (iht hmem)
  | _ => simp [freeVarsAt] at hmem

/-- **A substitution whose levels all sit below `n` is `ℓ`-clean for every `ℓ ≥ n`.** The bridge from
a `CtxWf`-style freshness bound to `substAt_substAt_comm`'s `hclean` hypothesis — the level-tag analog
of `LevelMap`. -/
theorem clean_of_levels_lt {σ : Nat → Ty} {n : Nat} (hlt : ∀ i, ∀ l ∈ (σ i).levels, l < n)
    {ℓ : Nat} (hge : n ≤ ℓ) : ∀ i, ∀ j, j ∉ freeVarsAt ℓ (σ i) := by
  intro i j hmem
  exact absurd (hlt i ℓ (mem_levels_of_mem_freeVarsAt hmem)) (by omega)

/-! ## Schemes & instantiation -/

end Ty

/-- A polymorphic type scheme. `level` is the generalization layer this scheme's own quantifiers
belong to (`plan/eyg-g1-level-tagged-ty.md` Phase 3b) — pinned to `0` everywhere for now (a pure
representation change, mirroring Phase 3a's `Ty.var` port): `genAt`/`instantiate`/`substScheme` still
use the old arity/`reindexGen` magnitude machinery below, ignoring this field entirely. Flipping them
to be level-native (no reindexing) is the remaining Phase 3b work; this field addition just clears the
field-arity mechanical churn out of that step's way. -/
structure Scheme where
  arity : Nat
  level : Nat
  body : Ty
  deriving DecidableEq, Repr, Inhabited

namespace Scheme

/-- A monomorphic scheme (no quantifiers). -/
def mono (t : Ty) : Scheme := ⟨0, 0, t⟩

/-- Instantiate a scheme by substituting its quantified variables with `args`
(`binding.instantiate`). The `arity` **quantified** variables (`var i`, `i <
arity`) are substituted with `args[i]`; an **ambient** (free) variable, living at
index `i ≥ arity` inside the body, refers to ambient scope variable `i - arity` —
the quantifier prefix shifts the ambient scope up by `arity`, so instantiation
shifts it back **down** by `arity`. (For a *closed* body — every current builtin
scheme — the ambient branch never fires, so this matches the old "leave it
untouched" reading; the down-shift only matters once `gen` produces schemes with
free ambient variables.) A *monomorphic* scheme (arity 0) is the identity on its
body, ignoring `args` — the property `EnvWf`'s polymorphic-readiness clause relies
on. The declarative typing rules pick `args` with `args.length = arity`. -/
def instantiate (s : Scheme) (args : List Ty) : Ty :=
  Ty.subst (fun i => if i < s.arity then args.getD i (.var 0 i) else .var 0 (i - s.arity)) s.body

/-- A monomorphic scheme instantiates to its body, ignoring `args`. -/
@[simp] theorem instantiate_mono (t : Ty) (args : List Ty) :
    (mono t).instantiate args = t := by
  unfold instantiate mono
  simp only [Nat.not_lt_zero, if_false, Nat.sub_zero]
  exact Ty.subst_id t

/-- Apply a type substitution `σ` (on the **ambient** scope) to a scheme. The
quantified variables `0 … arity-1` are left fixed; an ambient variable, occurring
at body-index `i ≥ arity`, is replaced by `σ (i - arity)` **shifted up by `arity`**
(so its own variables land back above the quantifier prefix). This is exactly the
map that makes substitution commute with instantiation (`subst_instantiate`). -/
def substScheme (σ : Nat → Ty) (s : Scheme) : Scheme :=
  ⟨s.arity, s.level,
    Ty.subst (fun i => if i < s.arity then .var 0 i else Ty.shift s.arity (σ (i - s.arity))) s.body⟩

@[simp] theorem substScheme_arity (σ : Nat → Ty) (s : Scheme) :
    (substScheme σ s).arity = s.arity := rfl

/-- The computed generalization of `d` at level `n`: quantify the generalized (`≥ n`) variables. The
generalized variables (`≥ n`) become the quantifier prefix `0 … arity-1` (via `v ↦ v - n`), and the
ambient variables (`< n`) shift up past the prefix (`v ↦ v + arity`). (T6 `let_poly`; relocated here so
the `let_poly` typing rule can reference it.) -/
def genAt (n : Nat) (d : Ty) : Scheme :=
  ⟨d.genArity n, 0, Ty.subst (Ty.reindexGen n (d.genArity n)) d⟩

@[simp] theorem genAt_arity (n : Nat) (d : Ty) : (genAt n d).arity = d.genArity n := rfl

/-- The **ambient** free variables of a scheme `⟨arity, body⟩`: the body variables sitting *above* the
quantifier prefix (`≥ arity`), shifted down by `arity` (matching `instantiate`/`substScheme`). Used by
`CtxWf` (the `let_poly` context-below-level side-invariant). -/
def freeVars (s : Scheme) : List Nat :=
  (s.body.freeVars.filter (fun j => decide (s.arity ≤ j))).map (· - s.arity)

/-- A monomorphic scheme's ambient free vars are exactly its body's free vars (arity `0`). -/
@[simp] theorem freeVars_mono (t : Ty) : freeVars (mono t) = t.freeVars := by
  simp only [freeVars, mono, Nat.zero_le, decide_true, List.filter_true, Nat.sub_zero, List.map_id']

/-- `substScheme` on a monomorphic scheme is `subst` on its body. -/
@[simp] theorem substScheme_mono (σ : Nat → Ty) (t : Ty) :
    substScheme σ (mono t) = mono (Ty.subst σ t) := by
  unfold substScheme mono
  simp only [Nat.not_lt_zero, if_false, Nat.sub_zero, Ty.shift_zero]

/-- **Substitution commutes with instantiation.** Applying an ambient substitution
`σ` to an instantiated scheme equals instantiating the substituted scheme with the
substituted arguments — provided the scheme is fully applied (`args.length =
arity`). The quantifier-prefix shift in `substScheme`/`instantiate` cancels: an
ambient substitute is shifted up by `arity` (into the body) and instantiation
shifts it back down. -/
theorem subst_instantiate (σ : Nat → Ty) (s : Scheme) (args : List Ty)
    (hlen : args.length = s.arity) :
    Ty.subst σ (s.instantiate args) = (substScheme σ s).instantiate (args.map (Ty.subst σ)) := by
  unfold instantiate substScheme
  rw [Ty.subst_subst, Ty.subst_subst]
  congr 1
  funext i
  by_cases hi : i < s.arity
  · -- quantified variable: both sides substitute `args[i]`
    have hi' : i < args.length := by rw [hlen]; exact hi
    simp only [hi, if_true, Ty.subst]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi']
    rfl
  · -- ambient variable: shift up by arity, instantiate shifts it back down
    have hge : s.arity ≤ i := Nat.le_of_not_lt hi
    rw [if_neg hi, if_neg hi]
    show σ (i - s.arity) = Ty.subst _ (Ty.shift s.arity (σ (i - s.arity)))
    rw [Ty.subst_shift]
    have hid : (fun j => (if j + s.arity < s.arity
        then (args.map (Ty.subst σ)).getD (j + s.arity) (.var 0 (j + s.arity))
        else (.var 0 (j + s.arity - s.arity) : Ty))) = (fun j => (.var 0 j : Ty)) := by
      funext j
      rw [if_neg (by omega), Nat.add_sub_cancel]
    rw [hid, Ty.subst_id]

/-- The instantiation arguments that make `subst` commute with `instantiate` for an
**arbitrarily-applied** scheme (the declarative `var`/`builtin` rules allow any
`args`). For each quantifier `i < arity`: if `args` supplies a `i`-th argument, use
its substitute `subst σ args[i]`; otherwise (an *under*-applied scheme leaves `var
i` in place) the ambient substitution would act on the leaked `var i`, so we feed
`σ i` directly. -/
def instArgs (σ : Nat → Ty) (s : Scheme) (args : List Ty) : List Ty :=
  (List.range s.arity).map (fun i => if i < args.length then Ty.subst σ (args.getD i (.var 0 i)) else σ i)

@[simp] theorem instArgs_length (σ : Nat → Ty) (s : Scheme) (args : List Ty) :
    (instArgs σ s args).length = s.arity := by simp [instArgs]

/-- **Substitution commutes with instantiation, unconditionally.** For *any* `args`
(no `length = arity` requirement — the declarative `var`/`builtin` rules pick `args`
freely), applying `σ` to an instantiated scheme equals instantiating the substituted
scheme at `instArgs σ s args`. The witness `instArgs` absorbs the under-application
mismatch (a leaked quantifier `var i` whose `σ`-image must be supplied directly). -/
theorem subst_instantiate' (σ : Nat → Ty) (s : Scheme) (args : List Ty) :
    Ty.subst σ (s.instantiate args) = (substScheme σ s).instantiate (instArgs σ s args) := by
  unfold instantiate substScheme
  rw [Ty.subst_subst, Ty.subst_subst]
  congr 1
  funext i
  by_cases hi : i < s.arity
  · -- quantified variable: read `instArgs` at index `i < arity`
    have hb : i < (List.range s.arity).length := by rw [List.length_range]; exact hi
    have hrng : ((List.range s.arity).map
        (fun i => if i < args.length then Ty.subst σ (args.getD i (.var 0 i)) else σ i)).getD i (.var 0 i)
        = if i < args.length then Ty.subst σ (args.getD i (.var 0 i)) else σ i := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hb]
      simp [List.getElem_range]
    simp only [hi, if_true, Ty.subst, instArgs, hrng]
    by_cases hlt : i < args.length
    · simp only [hlt, if_true]
    · simp only [hlt, if_false]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  · -- ambient variable: identical to `subst_instantiate`
    have hge : s.arity ≤ i := Nat.le_of_not_lt hi
    rw [if_neg hi, if_neg hi]
    show σ (i - s.arity) = Ty.subst _ (Ty.shift s.arity (σ (i - s.arity)))
    rw [Ty.subst_shift]
    have hid : (fun j => (if j + s.arity < s.arity
        then (instArgs σ s args).getD (j + s.arity) (.var 0 (j + s.arity))
        else (.var 0 (j + s.arity - s.arity) : Ty))) = (fun j => (.var 0 j : Ty)) := by
      funext j
      rw [if_neg (by omega), Nat.add_sub_cancel]
    rw [hid, Ty.subst_id]

end Scheme

/-! ## Scheme builders (`contextual.q`/`pure1`/`pure2`/`pure3`) -/

namespace Ty

/-- Quantified type variable `i` (`contextual.q`). -/
abbrev q (i : Nat) : Ty := .var 0 i

/-- A pure unary arrow `arg →⟨∅⟩ ret` (`contextual.pure1`). -/
def pure1 (arg ret : Ty) : Ty := .fun arg .empty ret

/-- A pure binary arrow (`contextual.pure2`). -/
def pure2 (a b ret : Ty) : Ty := .fun a .empty (.fun b .empty ret)

/-- A pure ternary arrow (`contextual.pure3`). -/
def pure3 (a b c ret : Ty) : Ty := .fun a .empty (.fun b .empty (.fun c .empty ret))

end Ty

/-! ## Builtin scheme table (`contextual.builtins()`)

Transcribed from `builtins()`. The arity is the count of distinct `q`-vars: the
`int_*`/`string_*` arithmetic and string builtins are monomorphic (arity 0);
`equal` is `∀α. α → α → bool` (arity 1); `fix` is `∀α β. (α →⟨β⟩ α) →⟨β⟩ α`
(arity 2). Grown per slice; completed in T6. -/

namespace Builtins

open Eyg.Types.Ty

/-- `int_compare`'s return: `Union(|Lt :: unit, Eq :: unit, Gt :: unit|)`. -/
def intCompareResult : Ty := union' [("Lt", unit), ("Eq", unit), ("Gt", unit)]

/-- The (partial) builtin scheme table — the T2 arithmetic/string/core subset of
`contextual.builtins()`. Returns `none` for builtins not yet transcribed. -/
def scheme : String → Option Scheme
  | "equal" => some ⟨1, 0, pure2 (q 0) (q 0) boolean⟩
  -- `fix : ((self →⟨∅⟩ self) →⟨∅⟩ self)` with `self = (q0 →⟨q2⟩ q3)` — fixpoint forced to a
  -- **function** type AND the **builder pinned pure** (`q1 = ∅`, left unused in the arity-4
  -- prefix): the analyzer-divergent narrowing that discharges `FixPreserves` via the pure-builder
  -- `partialFixed` (rejects builder-side-effecting recursion the reference analyzer accepts).
  | "fix" => some ⟨4, 0,
      .fun (.fun (.fun (q 0) (q 2) (q 3)) .empty (.fun (q 0) (q 2) (q 3)))
        .empty (.fun (q 0) (q 2) (q 3))⟩
  | "int_compare" => some (.mono (pure2 integer integer intCompareResult))
  | "int_add" => some (.mono (pure2 integer integer integer))
  | "int_subtract" => some (.mono (pure2 integer integer integer))
  | "int_multiply" => some (.mono (pure2 integer integer integer))
  | "int_divide" => some (.mono (pure2 integer integer (result integer unit)))
  | "int_absolute" => some (.mono (pure1 integer integer))
  | "int_parse" => some (.mono (pure1 string (result integer unit)))
  | "int_to_string" => some (.mono (pure1 integer string))
  | "string_append" => some (.mono (pure2 string string string))
  | "string_length" => some (.mono (pure1 string integer))
  | "string_uppercase" => some (.mono (pure1 string string))
  | "string_lowercase" => some (.mono (pure1 string string))
  | "string_starts_with" => some (.mono (pure2 string string boolean))
  | "string_ends_with" => some (.mono (pure2 string string boolean))
  | _ => none

/-- Every builtin scheme is **closed** (its body uses only quantified variables),
so an ambient substitution leaves it fixed. Used by the type-substitution lemma's
`builtin` case: the substituted builtin is still the *same* builtin scheme. -/
theorem scheme_substScheme {id : String} {s : Scheme} (σ : Nat → Ty)
    (h : scheme id = some s) : Scheme.substScheme σ s = s := by
  unfold scheme at h
  split at h <;> first | (cases h; rfl) | cases h

/-! ## Sanity checks -/

-- `int_add : Integer → Integer → Integer`, monomorphic.
example : scheme "int_add" = some (.mono (.fun .integer .empty (.fun .integer .empty .integer))) :=
  rfl

-- Instantiating `equal` at `Integer` gives `Integer → Integer → boolean`.
example : (Scheme.instantiate ⟨1, 0, Ty.pure2 (Ty.q 0) (Ty.q 0) Ty.boolean⟩ [Ty.integer])
    = Ty.pure2 Ty.integer Ty.integer Ty.boolean := rfl

-- `fix` instantiated at `q0:=Integer, q1:=∅, q2:=∅, q3:=Integer` (so `self = Integer →⟨∅⟩
-- Integer`): `((Integer→Integer) →⟨∅⟩ (Integer→Integer)) →⟨∅⟩ (Integer→Integer)`. The
-- fixpoint is a function type, as the hardened scheme requires.
example :
    (Scheme.instantiate
      ⟨4, 0, .fun (.fun (.fun (Ty.q 0) (Ty.q 2) (Ty.q 3)) (Ty.q 1) (.fun (Ty.q 0) (Ty.q 2) (Ty.q 3)))
        (Ty.q 1) (.fun (Ty.q 0) (Ty.q 2) (Ty.q 3))⟩
      [Ty.integer, Ty.empty, Ty.empty, Ty.integer])
    = .fun (.fun (.fun Ty.integer Ty.empty Ty.integer) Ty.empty
        (.fun Ty.integer Ty.empty Ty.integer)) Ty.empty
        (.fun Ty.integer Ty.empty Ty.integer) := rfl

end Builtins

end Eyg.Types
