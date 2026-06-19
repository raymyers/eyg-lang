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
  | .var i => σ i
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

@[simp] theorem subst_var (σ : Nat → Ty) (i : Nat) : subst σ (.var i) = σ i := rfl

/-- Composition of substitutions (`subst` is functorial in `σ`). -/
theorem subst_subst (σ τ : Nat → Ty) (t : Ty) :
    subst σ (subst τ t) = subst (fun i => subst σ (τ i)) t := by
  induction t with
  | var i => rfl
  | _ => simp_all [subst]

/-- Identity substitution is the identity. -/
theorem subst_id (t : Ty) : subst (fun i => .var i) t = t := by
  induction t with
  | var i => rfl
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
def shift (k : Nat) (t : Ty) : Ty := subst (fun i => .var (i + k)) t

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
  | .var i => [i]
  | .fun a e r => freeVars a ++ freeVars e ++ freeVars r
  | .list a => freeVars a
  | .record r => freeVars r
  | .union r => freeVars r
  | .promise a => freeVars a
  | .rowExtend _ f t => freeVars f ++ freeVars t
  | .effectExtend _ a b t => freeVars a ++ freeVars b ++ freeVars t
  | _ => []

/-- **A substitution that fixes every free variable fixes the type.** -/
theorem subst_eq_of_fixes_free {σ : Nat → Ty} {t : Ty}
    (h : ∀ i ∈ freeVars t, σ i = .var i) : subst σ t = t := by
  induction t with
  | var i => exact h i (by simp [freeVars])
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
    (h : subst σ t = t) : ∀ i ∈ freeVars t, σ i = .var i := by
  induction t with
  | var j =>
      intro i hi; simp only [freeVars, List.mem_singleton] at hi; subst hi
      simpa only [subst] using h
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
  | var i => exact h i (by simp [freeVars])
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
  | var j => simp only [subst, freeVars, List.mem_singleton]; constructor
             · intro h; exact ⟨j, rfl, h⟩
             · rintro ⟨v, rfl, h⟩; exact h
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

/-! ## Schemes & instantiation -/

end Ty

/-- A polymorphic type scheme: `∀ (arity de-Bruijn vars). body`. The quantified
variables are `var 0 … var (arity-1)` occurring in `body` (`binding.Poly`). -/
structure Scheme where
  arity : Nat
  body : Ty
  deriving DecidableEq, Repr, Inhabited

namespace Scheme

/-- A monomorphic scheme (no quantifiers). -/
def mono (t : Ty) : Scheme := ⟨0, t⟩

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
  Ty.subst (fun i => if i < s.arity then args.getD i (.var i) else .var (i - s.arity)) s.body

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
  ⟨s.arity, Ty.subst (fun i => if i < s.arity then .var i else Ty.shift s.arity (σ (i - s.arity)))
    s.body⟩

@[simp] theorem substScheme_arity (σ : Nat → Ty) (s : Scheme) :
    (substScheme σ s).arity = s.arity := rfl

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
        then (args.map (Ty.subst σ)).getD (j + s.arity) (.var (j + s.arity))
        else (.var (j + s.arity - s.arity) : Ty))) = (fun j => (.var j : Ty)) := by
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
  (List.range s.arity).map (fun i => if i < args.length then Ty.subst σ (args.getD i (.var i)) else σ i)

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
        (fun i => if i < args.length then Ty.subst σ (args.getD i (.var i)) else σ i)).getD i (.var i)
        = if i < args.length then Ty.subst σ (args.getD i (.var i)) else σ i := by
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
        then (instArgs σ s args).getD (j + s.arity) (.var (j + s.arity))
        else (.var (j + s.arity - s.arity) : Ty))) = (fun j => (.var j : Ty)) := by
      funext j
      rw [if_neg (by omega), Nat.add_sub_cancel]
    rw [hid, Ty.subst_id]

end Scheme

/-! ## Scheme builders (`contextual.q`/`pure1`/`pure2`/`pure3`) -/

namespace Ty

/-- Quantified type variable `i` (`contextual.q`). -/
abbrev q (i : Nat) : Ty := .var i

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
  | "equal" => some ⟨1, pure2 (q 0) (q 0) boolean⟩
  -- `fix : ((self →⟨∅⟩ self) →⟨∅⟩ self)` with `self = (q0 →⟨q2⟩ q3)` — fixpoint forced to a
  -- **function** type AND the **builder pinned pure** (`q1 = ∅`, left unused in the arity-4
  -- prefix): the analyzer-divergent narrowing that discharges `FixPreserves` via the pure-builder
  -- `partialFixed` (rejects builder-side-effecting recursion the reference analyzer accepts).
  | "fix" => some ⟨4,
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
example : (Scheme.instantiate ⟨1, Ty.pure2 (Ty.q 0) (Ty.q 0) Ty.boolean⟩ [Ty.integer])
    = Ty.pure2 Ty.integer Ty.integer Ty.boolean := rfl

-- `fix` instantiated at `q0:=Integer, q1:=∅, q2:=∅, q3:=Integer` (so `self = Integer →⟨∅⟩
-- Integer`): `((Integer→Integer) →⟨∅⟩ (Integer→Integer)) →⟨∅⟩ (Integer→Integer)`. The
-- fixpoint is a function type, as the hardened scheme requires.
example :
    (Scheme.instantiate
      ⟨4, .fun (.fun (.fun (Ty.q 0) (Ty.q 2) (Ty.q 3)) (Ty.q 1) (.fun (Ty.q 0) (Ty.q 2) (Ty.q 3)))
        (Ty.q 1) (.fun (Ty.q 0) (Ty.q 2) (Ty.q 3))⟩
      [Ty.integer, Ty.empty, Ty.empty, Ty.integer])
    = .fun (.fun (.fun Ty.integer Ty.empty Ty.integer) Ty.empty
        (.fun Ty.integer Ty.empty Ty.integer)) Ty.empty
        (.fun Ty.integer Ty.empty Ty.integer) := rfl

end Builtins

end Eyg.Types
