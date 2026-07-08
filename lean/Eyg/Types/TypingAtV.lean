import Eyg.Types.TypingAt

/-!
# Level-native typing judgment `HasTypeAtV` (G1 Phase 3b — the readiness-keystone deliverable)

`HasTypeAtV lvl Γ e τ ε` is the **level-native sibling** of `HasTypeAt` (`TypingAt.lean`). Where
`HasTypeAt` stores the *magnitude*-based `Scheme.genAt`/`CtxWf`/`Ty.subst` (the right tool for the
*ambient/weakening* substitution direction, `hasTypeAt_subst`), `HasTypeAtV` stores the *level*-native
`Scheme.genAtV`/`CtxWfV`/`Ty.substAt` — the right tool for the **instantiation** direction the
readiness keystone needs (open a scheme's *own* quantifiers at its generalization level `lvl`, moving
the generalized region while fixing the ambient one).

* `let_poly` generalizes at **exactly** `lvl` via `Scheme.genAtV lvl` (not the magnitude `genAt`),
  records `CtxWfV lvl Γ` (bounding `Ty.levels`, not `Scheme.freeVars`), types its body at `lvl + 1`,
  and carries **no `noLambdaLet`** — nested `Let`-binds-`Lambda` bodies are genuinely accepted.
* `lam`/`let_` store an explicit sublevel `lvl'` with `lvl ≤ lvl'` and the *level*-freshness premise
  `∀ l ∈ argTy.levels, l < lvl'` (the `CtxWfV`-shaped condition, differing from `HasTypeAt`'s
  `Scheme.freeVars`-shaped one).
* `var`/`builtin` instantiate via the level-native `Scheme.instantiateV` (consistent with the
  level-native schemes `let_poly` stores).

The payoff is `hasTypeAtV_substAt` (re-type a derivation under an **outer** instantiation `substAt ℓ`,
`ℓ ≠ 0`, `ℓ < lvl`, for a nested inner scheme at a *distinct* level) and — composing it with
`genAtV_generalizesAtV` — the level-native readiness keystone `genAtV_instantiate_lam_ready`: every
instantiation of a let-bound lambda's scheme `genAtV ℓ defnTy` is achieved by a genuine `substAt ℓ`
re-typing of the lambda's own derivation. This is the term-level ingredient the value-typing side
(obstruction B, `HasTypeVAt`/`EnvWfAt`, a future session) will consume; it does **not** wire in
`Value.Closure`/`HasTypeV`/`EnvWf` here.

Purely additive: `HasType`, `hasType_subst`, `HasTypeAt`/`hasTypeAt_subst`, `Runtime.lean`, and every
soundness declaration are untouched.
-/

namespace Eyg.Types

open Eyg.Ir

variable {m : Type}

namespace Ty

/-! ## Level-tagged substitution: `TyEquiv`/`EffWeaken` stability and level tracking -/

/-- **`substAt` preserves row equivalence** (level-native analog of `subst_tyEquiv`). -/
theorem substAt_tyEquiv (ℓ : Nat) (σ : Nat → Ty) {s t : Ty} (h : TyEquiv s t) :
    TyEquiv (substAt ℓ σ s) (substAt ℓ σ t) := by
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
  | swapRow hne => simp only [substAt]; exact .swapRow hne
  | swapEff hne => simp only [substAt]; exact .swapEff hne

/-- **`EffWeaken` is `substAt`-stable** (level-native analog of `subst_effWeaken`). -/
theorem substAt_effWeaken (ℓ : Nat) (σ : Nat → Ty) {e₁ e₂ : Ty} (h : EffWeaken e₁ e₂) :
    EffWeaken (substAt ℓ σ e₁) (substAt ℓ σ e₂) := by
  rcases h with h | h
  · exact .inl (substAt_tyEquiv ℓ σ h)
  · exact .inr (substAt_tyEquiv ℓ σ h)

/-- **Where a level in a substituted type comes from.** Every level occurring in `substAt ℓ σ t`
either already occurred in `t` or is introduced by `σ`'s range. Feeds the `lam`/`let_` level-freshness
reconstruction and `ctxWfV_substCtxAt`. -/
theorem mem_levels_substAt {ℓ l : Nat} {σ : Nat → Ty} {t : Ty}
    (h : l ∈ (substAt ℓ σ t).levels) : l ∈ t.levels ∨ ∃ i, l ∈ (σ i).levels := by
  induction t with
  | var l' i =>
      by_cases hl' : l' = ℓ
      · subst hl'; simp only [substAt] at h; exact Or.inr ⟨i, h⟩
      · simp only [substAt, if_neg hl', levels, List.mem_singleton] at h
        subst h; exact Or.inl (by simp [levels])
  | «fun» a e r iha ihe ihr =>
      simp only [substAt, levels, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · rcases iha h with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases ihe h with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases ihr h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | list a ih => simp only [substAt, levels] at h ⊢; exact ih h
  | record r ih => simp only [substAt, levels] at h ⊢; exact ih h
  | union r ih => simp only [substAt, levels] at h ⊢; exact ih h
  | promise a ih => simp only [substAt, levels] at h ⊢; exact ih h
  | rowExtend l' f t ihf iht =>
      simp only [substAt, levels, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases ihf h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases iht h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | effectExtend l' a b t iha ihb iht =>
      simp only [substAt, levels, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · rcases iha h with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases ihb h with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases iht h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | _ => simp only [substAt, levels] at h; exact absurd h (by simp)

/-- **Cross-level commutation for a body with no occurrence at the outer level.** Where
`substAt_substAt_comm` needs `σ` clean w.r.t. `ℓ2`, if `t` has no `ℓ1`-leaves at all the problematic
case never fires, so the commutation holds with **no** cleanness on `σ` — the version the closed
builtin schemes (whose bodies live at level `0`, substituted at `ℓ ≠ 0`) need. -/
theorem substAt_substAt_comm_of_no_mem {ℓ1 ℓ2 : Nat} (hne : ℓ1 ≠ ℓ2) {σ τ : Nat → Ty} {t : Ty}
    (hclosed : ∀ j, j ∉ freeVarsAt ℓ1 t) :
    substAt ℓ1 σ (substAt ℓ2 τ t)
      = substAt ℓ2 (fun i => substAt ℓ1 σ (τ i)) (substAt ℓ1 σ t) := by
  induction t with
  | var l i =>
      by_cases h2 : l = ℓ2
      · simp [substAt, h2, if_neg (Ne.symm hne)]
      · by_cases h1 : l = ℓ1
        · exact absurd (by simp [freeVarsAt, h1] : i ∈ freeVarsAt ℓ1 (Ty.var l i)) (hclosed i)
        · simp only [substAt, if_neg h1, if_neg h2]
  | «fun» a e r iha ihe ihr =>
      simp only [freeVarsAt, List.mem_append] at hclosed
      simp only [substAt, iha (fun j hj => hclosed j (Or.inl (Or.inl hj))),
        ihe (fun j hj => hclosed j (Or.inl (Or.inr hj))), ihr (fun j hj => hclosed j (Or.inr hj))]
  | list a ih => simp only [substAt, ih (fun j hj => hclosed j hj)]
  | record r ih => simp only [substAt, ih (fun j hj => hclosed j hj)]
  | union r ih => simp only [substAt, ih (fun j hj => hclosed j hj)]
  | promise a ih => simp only [substAt, ih (fun j hj => hclosed j hj)]
  | rowExtend l f t ihf iht =>
      simp only [freeVarsAt, List.mem_append] at hclosed
      simp only [substAt, ihf (fun j hj => hclosed j (Or.inl hj)),
        iht (fun j hj => hclosed j (Or.inr hj))]
  | effectExtend l a b t iha ihb iht =>
      simp only [freeVarsAt, List.mem_append] at hclosed
      simp only [substAt, iha (fun j hj => hclosed j (Or.inl (Or.inl hj))),
        ihb (fun j hj => hclosed j (Or.inl (Or.inr hj))), iht (fun j hj => hclosed j (Or.inr hj))]
  | _ => rfl

/-- **`substAt ℓ σ` (with `ℓ ≠ k`, `σ` clean w.r.t. `k`) preserves the count of level-`k`
occurrences.** The `genAtV`-arity-stability core: `substAt ℓ σ` neither removes existing level-`k`
leaves (it only rewrites level-`ℓ` ones) nor introduces new ones (σ is `k`-clean), so the multiset of
level-`k` occurrences — hence its length — is unchanged. -/
theorem length_filter_levels_substAt {ℓ k : Nat} (hne : ℓ ≠ k) {σ : Nat → Ty}
    (hclean : ∀ i, k ∉ (σ i).levels) (t : Ty) :
    ((substAt ℓ σ t).levels.filter (· = k)).length = (t.levels.filter (· = k)).length := by
  induction t with
  | var l i =>
      by_cases hl : l = ℓ
      · simp only [substAt, if_pos hl, levels]
        have hnil : (σ i).levels.filter (· = k) = [] := by
          rw [List.filter_eq_nil_iff]
          intro a ha hak
          simp only [decide_eq_true_eq] at hak; subst hak
          exact hclean i ha
        rw [hnil]
        simp [(by rw [hl]; exact hne : l ≠ k)]
      · simp only [substAt, if_neg hl]
  | «fun» a e r iha ihe ihr =>
      simp only [substAt, levels, List.filter_append, List.length_append, iha, ihe, ihr]
  | list a ih => simp only [substAt, levels, ih]
  | record r ih => simp only [substAt, levels, ih]
  | union r ih => simp only [substAt, levels, ih]
  | promise a ih => simp only [substAt, levels, ih]
  | rowExtend l f t ihf iht =>
      simp only [substAt, levels, List.filter_append, List.length_append, ihf, iht]
  | effectExtend l a b t iha ihb iht =>
      simp only [substAt, levels, List.filter_append, List.length_append, iha, ihb, iht]
  | _ => rfl

end Ty

/-! ## Level-native scheme commutations -/

/-- `substSchemeVAt` on a monomorphic scheme is `substAt` on its body. -/
@[simp] theorem substSchemeVAt_mono (ℓ : Nat) (σ : Nat → Ty) (t : Ty) :
    Scheme.substSchemeVAt ℓ σ (Scheme.mono t) = Scheme.mono (Ty.substAt ℓ σ t) := rfl

/-- **`genAtV` commutes with an outer level-`ℓ` substitution** (`ℓ ≠ k`, `σ` clean w.r.t. `k`) — the
level-native analog of `genAt_substScheme`, and the `let_poly`-arm context rewrite of
`hasTypeAtV_substAt`. Arity stability is `Ty.length_filter_levels_substAt`; the body carries through
`substAt`. Unlike the magnitude `genAt_substScheme` (which needs a `LevelMap`), the only conditions
are level-disjointness and freshness — the down-shift wall does not reappear. -/
theorem substSchemeVAt_genAtV {ℓ k : Nat} (hne : ℓ ≠ k) {σ : Nat → Ty}
    (hclean : ∀ i, k ∉ (σ i).levels) (d : Ty) :
    Scheme.substSchemeVAt ℓ σ (Scheme.genAtV k d) = Scheme.genAtV k (Ty.substAt ℓ σ d) := by
  refine Scheme.ext' ?_ rfl rfl
  simp only [Scheme.substSchemeVAt, Scheme.genAtV]
  exact (Ty.length_filter_levels_substAt hne hclean d).symm

/-- **General scheme-instantiation commutation under an outer level-`ℓ` substitution.** For a scheme
whose own level differs from `ℓ` (and `σ` clean w.r.t. that level), or which is monomorphic
(`arity = 0`, short-circuited unconditionally), `substAt ℓ σ` pushes through `instantiateV`. This is
the `var`-arm commutation of `hasTypeAtV_substAt` — it covers *every* scheme a well-formed context can
bind (mono via the left disjunct; `genAtV`-at-a-distinct-level via the right). Generalizes
`Scheme.substAt_instantiateV` off the `genAtV`-literal to an arbitrary scheme. -/
theorem substAt_instantiateV_scheme {ℓ : Nat} {σ : Nat → Ty} {s : Scheme}
    (h : s.arity = 0 ∨ (ℓ ≠ s.level ∧ ∀ i, ∀ j, j ∉ Ty.freeVarsAt s.level (σ i))) (args : List Ty) :
    Ty.substAt ℓ σ (s.instantiateV args)
      = (Scheme.substSchemeVAt ℓ σ s).instantiateV (args.map (Ty.substAt ℓ σ)) := by
  by_cases h0 : s.arity = 0
  · simp only [Scheme.instantiateV, Scheme.substSchemeVAt, h0, if_true]
  · obtain ⟨hne, hclean⟩ := h.resolve_left h0
    simp only [Scheme.instantiateV, Scheme.substSchemeVAt, h0, if_false]
    rw [Ty.substAt_substAt_comm hne _ hclean]
    congr 1
    funext i
    by_cases hi : i < args.length
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi]; rfl
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simpa using hi)]
      show Ty.substAt ℓ σ (Ty.var s.level i) = Ty.var s.level i
      simp only [Ty.substAt, if_neg (Ne.symm hne)]

/-- **Scheme-instantiation commutation for a closed body.** For a scheme whose body has no level-`ℓ`
occurrence (e.g. a builtin scheme, whose body lives entirely at level `0`, substituted at `ℓ ≠ 0`),
`substAt ℓ σ` pushes through `instantiateV` with **no** cleanness on `σ` — via
`Ty.substAt_substAt_comm_of_no_mem`. The `builtin`-arm commutation of `hasTypeAtV_substAt`, where the
general `substAt_instantiateV_scheme` is unavailable (a builtin's level `0` collides with the ambient
scope `σ` lives on). -/
theorem substAt_instantiateV_closed {ℓ : Nat} {σ : Nat → Ty} {s : Scheme}
    (hne : ℓ ≠ s.level) (hbody : ∀ j, j ∉ Ty.freeVarsAt ℓ s.body) (args : List Ty) :
    Ty.substAt ℓ σ (s.instantiateV args)
      = (Scheme.substSchemeVAt ℓ σ s).instantiateV (args.map (Ty.substAt ℓ σ)) := by
  have hbodyeq : Ty.substAt ℓ σ s.body = s.body := Ty.substAt_eq_self_of_not_mem hbody
  by_cases h0 : s.arity = 0
  · simp only [Scheme.instantiateV, Scheme.substSchemeVAt, h0, if_true, hbodyeq]
  · simp only [Scheme.instantiateV, Scheme.substSchemeVAt, h0, if_false, hbodyeq]
    rw [Ty.substAt_substAt_comm_of_no_mem hne hbody, hbodyeq]
    congr 1
    funext i
    by_cases hi : i < args.length
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi]; rfl
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simpa using hi)]
      show Ty.substAt ℓ σ (Ty.var s.level i) = Ty.var s.level i
      simp only [Ty.substAt, if_neg (Ne.symm hne)]

/-! ## Builtin schemes are level-`0`-closed -/

namespace Builtins

/-- Every builtin scheme carries `level = 0`. -/
theorem scheme_level {id : String} {s : Scheme} (h : scheme id = some s) : s.level = 0 := by
  unfold scheme at h
  split at h <;> first | (cases h; rfl) | cases h

/-- Every level occurring in a builtin scheme's body is `0` (builtin bodies use only `q i = var 0 i`
and base types). -/
theorem scheme_levels_zero {id : String} {s : Scheme} (h : scheme id = some s) :
    ∀ l ∈ s.body.levels, l = 0 := by
  unfold scheme at h
  split at h <;> first | (cases h; decide) | cases h

/-- A builtin scheme's body has no occurrence at any nonzero level `ℓ`. -/
theorem scheme_no_level {ℓ : Nat} (hℓ : ℓ ≠ 0) {id : String} {s : Scheme}
    (h : scheme id = some s) : ∀ j, j ∉ Ty.freeVarsAt ℓ s.body := by
  intro j hj
  exact hℓ (scheme_levels_zero h ℓ (Ty.mem_levels_of_mem_freeVarsAt hj))

/-- **A builtin scheme is fixed by any nonzero-level substitution.** Its body has no level-`ℓ`
occurrence, so `substAt ℓ σ` is the identity on it. -/
theorem scheme_substSchemeVAt {ℓ : Nat} (hℓ : ℓ ≠ 0) (σ : Nat → Ty) {id : String} {s : Scheme}
    (h : scheme id = some s) : Scheme.substSchemeVAt ℓ σ s = s :=
  Scheme.ext' rfl rfl (Ty.substAt_eq_self_of_not_mem (scheme_no_level hℓ h))

end Builtins

/-! ## Level-native context substitution `substCtxAt` and the `PolyAbove` invariant -/

/-- Apply a level-`ℓ` type substitution to every scheme in a typing context. -/
def substCtxAt (ℓ : Nat) (σ : Nat → Ty) (Γ : Ctx) : Ctx :=
  Γ.map (fun b => (b.1, Scheme.substSchemeVAt ℓ σ b.2))

@[simp] theorem substCtxAt_nil (ℓ : Nat) (σ : Nat → Ty) : substCtxAt ℓ σ [] = [] := rfl

@[simp] theorem substCtxAt_cons (ℓ : Nat) (σ : Nat → Ty) (x : String) (s : Scheme) (Γ : Ctx) :
    substCtxAt ℓ σ ((x, s) :: Γ) = (x, Scheme.substSchemeVAt ℓ σ s) :: substCtxAt ℓ σ Γ := rfl

/-- Context lookup commutes with `substCtxAt` (keys preserved). -/
theorem substCtxAt_lookup {ℓ : Nat} {σ : Nat → Ty} {Γ : Ctx} {x : String} {s : Scheme}
    (h : Γ.lookup x = some s) :
    (substCtxAt ℓ σ Γ).lookup x = some (Scheme.substSchemeVAt ℓ σ s) := by
  induction Γ with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
      obtain ⟨y, sy⟩ := hd
      simp only [substCtxAt_cons, List.lookup_cons] at h ⊢
      by_cases hxy : (x == y) = true
      · simp only [hxy] at h ⊢; cases h; rfl
      · simp only [hxy] at h ⊢; exact ih h

/-- Membership recovery from a successful lookup. -/
theorem lookup_mem {Γ : Ctx} {x : String} {s : Scheme} (h : Γ.lookup x = some s) : (x, s) ∈ Γ := by
  induction Γ with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
      obtain ⟨y, sy⟩ := hd
      simp only [List.lookup_cons] at h
      by_cases hxy : (x == y) = true
      · simp only [hxy] at h; cases h
        have : x = y := by simpa using hxy
        subst this; exact List.mem_cons_self
      · simp only [hxy] at h; exact List.mem_cons_of_mem _ (ih h)

/-- **`substCtxAt` fixes a context below the substitution level.** If every level in every binding of
`Γ` is `< ℓ`, then `substAt ℓ σ` — which only rewrites level-`ℓ` leaves — is the identity on it. The
structural replacement (for `ℓ ≠ 0`) of the magnitude keystone's `∀σ' fixing [0,n), substCtx σ' Γ = Γ`
premise. -/
theorem substCtxAt_fix {ℓ : Nat} {σ : Nat → Ty} {Γ : Ctx} (hΓ : CtxWfV ℓ Γ) :
    substCtxAt ℓ σ Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨y, s⟩ := hd
      have hbody : Ty.substAt ℓ σ s.body = s.body := by
        apply Ty.substAt_eq_self_of_not_mem
        intro i hi
        exact absurd (hΓ (y, s) (by simp) ℓ (Ty.mem_levels_of_mem_freeVarsAt hi)) (lt_irrefl ℓ)
      have htl : CtxWfV ℓ tl := fun b hb => hΓ b (List.mem_cons_of_mem _ hb)
      simp only [substCtxAt_cons, ih htl]
      exact congrArg (fun z => (y, z) :: tl) (Scheme.ext' rfl rfl hbody)

/-- **`CtxWfV` is stable under a level-`ℓ` substitution** (`ℓ < L`, `σ`'s levels `≤ ℓ`). Substituting
keeps every binding's body levels `< L`: an existing level was `< L`; a level introduced by `σ` is
`≤ ℓ < L`. -/
theorem ctxWfV_substCtxAt {ℓ L : Nat} {σ : Nat → Ty} (hlt : ℓ < L)
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l ≤ ℓ) {Γ : Ctx} (hΓ : CtxWfV L Γ) :
    CtxWfV L (substCtxAt ℓ σ Γ) := by
  intro b hb l hl
  simp only [substCtxAt, List.mem_map] at hb
  obtain ⟨⟨y, s⟩, hmem, rfl⟩ := hb
  simp only [Scheme.substSchemeVAt] at hl
  rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
  · exact hΓ (y, s) hmem l hl'
  · exact Nat.lt_of_le_of_lt (hσ i l hi) hlt

/-- **The `let_poly` context rewrite.** `substCtxAt ℓ σ` on a context extended with a level-`k`
generalized binding (`k ≠ ℓ`, `σ` clean w.r.t. `k`) equals extending the substituted context with the
generalization of the substituted type — via `substSchemeVAt_genAtV`. -/
theorem substCtxAt_cons_genAtV {ℓ k : Nat} (hne : ℓ ≠ k) {σ : Nat → Ty}
    (hclean : ∀ i, k ∉ (σ i).levels) (x : String) (d : Ty) (Γ : Ctx) :
    substCtxAt ℓ σ ((x, Scheme.genAtV k d) :: Γ)
      = (x, Scheme.genAtV k (Ty.substAt ℓ σ d)) :: substCtxAt ℓ σ Γ := by
  simp only [substCtxAt_cons, substSchemeVAt_genAtV hne hclean]

/-- **Context invariant for the `substAt ℓ` re-typing induction.** Every polymorphic
(`arity ≠ 0`) binding sits at a level *strictly above* the opening level `ℓ`. Mono bindings
(`arity = 0`) are unconstrained. Preserved by `lam`/`let_` (add mono) and `let_poly` (adds a
level-`lvl > ℓ` generalization), and — with `hℓ : ℓ ≠ 0` — it is exactly the fact the `var` arm needs
to invoke `substAt_instantiateV_scheme` for the looked-up scheme. -/
def PolyAbove (ℓ : Nat) (Γ : Ctx) : Prop := ∀ b ∈ Γ, b.2.arity = 0 ∨ ℓ < b.2.level

theorem polyAbove_cons_mono {ℓ : Nat} {x : String} {t : Ty} {Γ : Ctx}
    (hΓ : PolyAbove ℓ Γ) : PolyAbove ℓ ((x, Scheme.mono t) :: Γ) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Or.inl rfl
  · exact hΓ b hb

/-! ## The level-native typing judgment -/

/-- The declarative typing judgment with an explicit ambient de-Bruijn **level**, built on the
level-native `Scheme.genAtV`/`CtxWfV`/`Ty.substAt`. Mirrors `HasTypeAt` except that schemes are
level-native (`var`/`builtin` instantiate via `instantiateV`; `let_poly` generalizes via `genAtV lvl`
and records `CtxWfV lvl`), and `lam`/`let_` use the `Ty.levels`-shaped freshness premise. -/
inductive HasTypeAtV {m : Type} : Nat → Ctx → Tree.Node m → Ty → Ty → Prop where
  | var {lvl Γ x s args ε a} :
      Γ.lookup x = some s →
      HasTypeAtV lvl Γ ⟨.Variable x, a⟩ (s.instantiateV args) ε
  | lam {lvl lvl' Γ x body argTy εb retTy ε a} :
      lvl ≤ lvl' →
      (∀ l ∈ argTy.levels, l < lvl') →
      HasTypeAtV lvl' ((x, .mono argTy) :: Γ) body retTy εb →
      HasTypeAtV lvl Γ ⟨.Lambda x body, a⟩ (.fun argTy εb retTy) ε
  | app {lvl Γ f arg argTy εf retTy ε a} :
      HasTypeAtV lvl Γ f (.fun argTy εf retTy) ε →
      Ty.EffWeaken εf ε →
      HasTypeAtV lvl Γ arg argTy ε →
      HasTypeAtV lvl Γ ⟨.Apply f arg, a⟩ retTy ε
  | let_ {lvl lvl' Γ x defn body defnTy bodyTy ε a} :
      HasTypeAtV lvl Γ defn defnTy ε →
      lvl ≤ lvl' →
      (∀ l ∈ defnTy.levels, l < lvl') →
      HasTypeAtV lvl' ((x, .mono defnTy) :: Γ) body bodyTy ε →
      HasTypeAtV lvl Γ ⟨.Let x defn body, a⟩ bodyTy ε
  | let_poly {lvl Γ x lx lbody la body defnTy bodyTy ε a} :
      HasTypeAtV lvl Γ ⟨.Lambda lx lbody, la⟩ defnTy ε →
      CtxWfV lvl Γ →
      HasTypeAtV (lvl + 1) ((x, Scheme.genAtV lvl defnTy) :: Γ) body bodyTy ε →
      HasTypeAtV lvl Γ ⟨.Let x ⟨.Lambda lx lbody, la⟩ body, a⟩ bodyTy ε
  | int {lvl Γ n ε a} : HasTypeAtV lvl Γ ⟨.Integer n, a⟩ .integer ε
  | str {lvl Γ s ε a} : HasTypeAtV lvl Γ ⟨.String s, a⟩ .string ε
  | bin {lvl Γ b ε a} : HasTypeAtV lvl Γ ⟨.Binary b, a⟩ .binary ε
  | builtin {lvl Γ id s args ε a} :
      Builtins.scheme id = some s →
      HasTypeAtV lvl Γ ⟨.Builtin id, a⟩ (s.instantiateV args) ε
  | tail {lvl Γ elem ε a} : HasTypeAtV lvl Γ ⟨.Tail, a⟩ (.list elem) ε
  | cons {lvl Γ elem ε a} :
      HasTypeAtV lvl Γ ⟨.Cons, a⟩ (.fun elem .empty (.fun (.list elem) .empty (.list elem))) ε
  | tag {lvl Γ l elem tail ε a} :
      HasTypeAtV lvl Γ ⟨.Tag l, a⟩ (.fun elem .empty (.union (.rowExtend l elem tail))) ε
  | nocases {lvl Γ ret ε a} :
      HasTypeAtV lvl Γ ⟨.NoCases, a⟩ (.fun (.union .empty) .empty ret) ε
  | case_ {lvl Γ l inner eff ret tail ε a} :
      HasTypeAtV lvl Γ ⟨.Case l, a⟩
        (.fun (.fun inner eff ret) .empty
          (.fun (.fun (.union tail) eff ret) .empty
            (.fun (.union (.rowExtend l inner tail)) eff ret))) ε
  | select {lvl Γ l fieldTy tail ε a} :
      HasTypeAtV lvl Γ ⟨.Select l, a⟩ (.fun (.record (.rowExtend l fieldTy tail)) .empty fieldTy) ε
  | extend {lvl Γ l fieldTy row ε a} :
      HasTypeAtV lvl Γ ⟨.Extend l, a⟩ (.fun fieldTy .empty
        (.fun (.record row) .empty (.record (.rowExtend l fieldTy row)))) ε
  | overwrite {lvl Γ l newTy oldTy tail ε a} :
      HasTypeAtV lvl Γ ⟨.Overwrite l, a⟩ (.fun newTy .empty
        (.fun (.record (.rowExtend l oldTy tail)) .empty
          (.record (.rowExtend l newTy tail)))) ε
  | empty {lvl Γ ε a} : HasTypeAtV lvl Γ ⟨.Empty, a⟩ (.record .empty) ε
  | perform {lvl Γ l a b μ ε ann} :
      HasTypeAtV lvl Γ ⟨.Perform l, ann⟩ (.fun a (.effectExtend l a b μ) b) ε
  | handle {lvl Γ l lift reply tail ret ε ann} :
      HasTypeAtV lvl Γ ⟨.Handle l, ann⟩ (handleTy l lift reply tail ret) ε
  | conv {lvl Γ e τ τ' ε ε'} :
      HasTypeAtV lvl Γ e τ ε → Ty.TyEquiv τ τ' → Ty.TyEquiv ε ε' →
      HasTypeAtV lvl Γ e τ' ε'

/-! ## The instantiation-direction re-typing lemma -/

/-- **Instantiation-direction type substitution for `HasTypeAtV`.** A derivation re-types under an
**outer** level-`ℓ` substitution `substAt ℓ σ` (`ℓ ≠ 0`, `ℓ < lvl`, `σ`'s levels `≤ ℓ`, context
polymorphic bindings above `ℓ`). Unlike `hasTypeAt_subst` (an *ambient/weakening* `LevelMap`
substitution), this **opens** at a nonzero level distinct from every enclosed generalization level, so
the `let_poly` arm reconstructs via `substCtxAt_cons_genAtV` (level-native, no `LevelMap`) and the
`var` arm via `substAt_instantiateV_scheme`. Fires non-vacuously for arbitrarily deep nesting. -/
theorem hasTypeAtV_substAt {ℓ : Nat} (hℓ : ℓ ≠ 0) (σ : Nat → Ty)
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l ≤ ℓ)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    (h : HasTypeAtV lvl Γ e τ ε) (hlt : ℓ < lvl) (hΓ : PolyAbove ℓ Γ) :
    HasTypeAtV lvl (substCtxAt ℓ σ Γ) e (Ty.substAt ℓ σ τ) (Ty.substAt ℓ σ ε) := by
  revert hlt hΓ
  induction h with
  | @var lvl Γ x s args ε a hl =>
      intro hlt hΓ
      have hdisj : s.arity = 0 ∨ (ℓ ≠ s.level ∧ ∀ i, ∀ j, j ∉ Ty.freeVarsAt s.level (σ i)) := by
        by_cases h0 : s.arity = 0
        · exact Or.inl h0
        · have hlvl : ℓ < s.level := (hΓ (x, s) (lookup_mem hl)).resolve_left h0
          exact Or.inr ⟨Nat.ne_of_lt hlvl,
            Ty.clean_of_levels_lt (fun i l hl' => Nat.lt_succ_of_le (hσ i l hl')) hlvl⟩
      rw [substAt_instantiateV_scheme hdisj args]
      exact HasTypeAtV.var (substCtxAt_lookup hl)
  | @builtin lvl Γ id s args ε a hs =>
      intro hlt hΓ
      rw [substAt_instantiateV_closed (by rw [Builtins.scheme_level hs]; exact hℓ)
            (Builtins.scheme_no_level hℓ hs) args,
          Builtins.scheme_substSchemeVAt hℓ σ hs]
      exact HasTypeAtV.builtin hs
  | @lam lvl lvl' Γ x body argTy εb retTy ε a hle hfv hbody ih =>
      intro hlt hΓ
      simp only [Ty.substAt]
      refine HasTypeAtV.lam hle ?_ ?_
      · intro l hl
        rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
        · exact hfv l hl'
        · exact Nat.lt_of_le_of_lt (hσ i l hi) (Nat.lt_of_lt_of_le hlt hle)
      · have hb := ih (Nat.lt_of_lt_of_le hlt hle) (polyAbove_cons_mono hΓ)
        rw [substCtxAt_cons, substSchemeVAt_mono] at hb
        exact hb
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg ihf iharg =>
      intro hlt hΓ
      have hf' := ihf hlt hΓ
      simp only [Ty.substAt] at hf'
      exact HasTypeAtV.app hf' (Ty.substAt_effWeaken ℓ σ hw) (iharg hlt hΓ)
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody ihdefn ihbody =>
      intro hlt hΓ
      have hb := ihbody (Nat.lt_of_lt_of_le hlt hle) (polyAbove_cons_mono hΓ)
      rw [substCtxAt_cons, substSchemeVAt_mono] at hb
      refine HasTypeAtV.let_ (ihdefn hlt hΓ) hle ?_ hb
      intro l hl
      rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
      · exact hfv l hl'
      · exact Nat.lt_of_le_of_lt (hσ i l hi) (Nat.lt_of_lt_of_le hlt hle)
  | @let_poly lvl Γ x lx lbody la body defnTy bodyTy ε a hdefn hcw hbody ihdefn ihbody =>
      intro hlt hΓ
      have hne : ℓ ≠ lvl := Nat.ne_of_lt hlt
      have hcleanlvl : ∀ i, lvl ∉ (σ i).levels := fun i hmem => absurd (hσ i lvl hmem) (by omega)
      have hdefn' := ihdefn hlt hΓ
      have hΓ1 : PolyAbove ℓ ((x, Scheme.genAtV lvl defnTy) :: Γ) := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · by_cases h0 : (Scheme.genAtV lvl defnTy).arity = 0
          · exact Or.inl h0
          · exact Or.inr (by simp only [Scheme.genAtV]; exact hlt)
        · exact hΓ b hb
      have hbodyIH := ihbody (by omega : ℓ < lvl + 1) hΓ1
      rw [substCtxAt_cons_genAtV hne hcleanlvl] at hbodyIH
      exact HasTypeAtV.let_poly hdefn' (ctxWfV_substCtxAt hlt hσ hcw) hbodyIH
  | int => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.int
  | str => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.str
  | bin => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.bin
  | tail => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.tail
  | cons => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.cons
  | tag => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.tag
  | nocases => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.nocases
  | case_ => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.case_
  | select => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.select
  | extend => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.extend
  | overwrite => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.overwrite
  | empty => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.empty
  | perform => intro hlt hΓ; simp only [Ty.substAt]; exact HasTypeAtV.perform
  | @handle lvl Γ l lift reply tail ret ε a =>
      intro hlt hΓ
      have heq : Ty.substAt ℓ σ (handleTy l lift reply tail ret)
          = handleTy l (Ty.substAt ℓ σ lift) (Ty.substAt ℓ σ reply) (Ty.substAt ℓ σ tail)
              (Ty.substAt ℓ σ ret) := by
        simp [handleTy, handlerTy, execTy, kontTy, Ty.substAt]
      rw [heq]; exact HasTypeAtV.handle
  | conv _ hτ hε ih =>
      intro hlt hΓ
      exact HasTypeAtV.conv (ih hlt hΓ) (Ty.substAt_tyEquiv ℓ σ hτ) (Ty.substAt_tyEquiv ℓ σ hε)

/-! ## The level-native readiness keystone -/

/-- **The instantiation keystone for a let-bound lambda (level-native).** For a lambda typed at
ambient level `ℓ` via its `lam` components — body at a strictly higher level `lvl' > ℓ`, context
`Γ` below `ℓ` (so `substAt ℓ` fixes it), and instantiation args with levels `≤ ℓ` — **every**
instantiation of the generalized scheme `genAtV ℓ (.fun argTy εb retTy)` is achieved by a genuine
`substAt ℓ` re-typing of the lambda's own `HasTypeAtV` derivation (`hasTypeAtV_substAt`).

This is the level-native counterpart of `genAt_closure_ready`'s term-level ingredient: the closure
body inhabits every instantiation of its scheme, established without any `noLambdaLet` restriction
(the lambda's body may itself contain nested generalized `let`s — the exact Caveat-5 shape). The
value-typing side (`HasTypeV (Value.Closure …)`, obstruction B) is a separate future session's job;
this delivers exactly the re-typing it will consume. -/
theorem genAtV_instantiate_lam_ready {ℓ : Nat} (hℓ : ℓ ≠ 0)
    {lvl' : Nat} {Γ : Ctx} {x : String} {lbody : Tree.Node m} {la : m}
    {argTy εb retTy ε : Ty}
    (hlt : ℓ < lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hbody : HasTypeAtV lvl' ((x, .mono argTy) :: Γ) lbody retTy εb)
    (hΓpa : PolyAbove ℓ Γ)
    (hΓwf : CtxWfV ℓ Γ)
    (args : List Ty)
    (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l ≤ ℓ) :
    HasTypeAtV ℓ Γ ⟨.Lambda x lbody, la⟩
      ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) ε := by
  -- Choose the explicit level-`ℓ` instantiation witness; its levels are `≤ ℓ`.
  set defnTy : Ty := .fun argTy εb retTy with hdefn
  have hΓpa' : PolyAbove ℓ ((x, Scheme.mono argTy) :: Γ) := polyAbove_cons_mono hΓpa
  by_cases h0 : (Scheme.genAtV ℓ defnTy).arity = 0
  · -- vacuous instantiation: the scheme has no level-`ℓ` quantifier, so it is `defnTy` itself
    rw [Scheme.instantiateV, if_pos h0, ← Ty.substAt_var_self ℓ defnTy]
    have hσ : ∀ i, ∀ l ∈ ((fun i => Ty.var ℓ i) i).levels, l ≤ ℓ := by
      intro i l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega
    have hb := hasTypeAtV_substAt hℓ (fun i => Ty.var ℓ i) hσ hbody hlt hΓpa'
    rw [substCtxAt_cons, substSchemeVAt_mono] at hb
    have hlam := HasTypeAtV.lam (a := la) (ε := ε) (le_of_lt hlt)
      (by intro l hl
          rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
          · exact hfv l hl'
          · simp only [Ty.levels, List.mem_singleton] at hi; omega) hb
    have hfix : substCtxAt ℓ (fun i => Ty.var ℓ i) Γ = Γ := substCtxAt_fix hΓwf
    rw [hfix] at hlam
    simpa only [Ty.substAt, hdefn] using hlam
  · -- non-vacuous instantiation via the explicit argument map
    rw [Scheme.instantiateV, if_neg h0]
    have hσ : ∀ i, ∀ l ∈ (args.getD i (.var ℓ i)).levels, l ≤ ℓ := by
      intro i l hl
      rcases lt_or_ge i args.length with hi | hi
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hl
        exact hargs _ (List.getElem_mem hi) l hl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none] at hl
        simp only [Ty.levels, List.mem_singleton] at hl; omega
    have hb := hasTypeAtV_substAt hℓ (fun i => args.getD i (.var ℓ i)) hσ hbody hlt hΓpa'
    rw [substCtxAt_cons, substSchemeVAt_mono] at hb
    have hlam := HasTypeAtV.lam (a := la) (ε := ε) (le_of_lt hlt)
      (by intro l hl
          rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
          · exact hfv l hl'
          · exact Nat.lt_of_le_of_lt (hσ i l hi) hlt) hb
    have hfix : substCtxAt ℓ (fun i => args.getD i (.var ℓ i)) Γ = Γ := substCtxAt_fix hΓwf
    rw [hfix] at hlam
    simpa only [Ty.substAt, hdefn] using hlam

/-! ## The nested-`let_poly` demonstration: the keystone fires non-vacuously reaching a nested scheme

The exact Caveat-5 shape `Tree.Node.noLambdaLet` rejects — a `let` binding a `Lambda`, nested inside
another generalized lambda's body — typed level-natively, then instantiated through the keystone at a
concrete type. The outer scheme lives at level `1`, the **nested inner** scheme at a *distinct* level
`2`; opening the outer scheme at level `1` (`α ↦ integer`) genuinely re-types the whole term while the
inner scheme is correctly re-generalized at level `2` (`substSchemeVAt_genAtV`) — the down-shift wall
does not reappear. -/

section NestedExample
open Eyg.Ir.Tree

/-- The **inner core**, at ambient level `2` inside the outer lambda's body: a generalized `let`
binding the polymorphic identity `\y. y` (generalized to `∀β. β → β` at level `2`), applied to the
ambient (level-`1`) `x : α`. A `Let`-binds-`Lambda` node — `noLambdaLet` of it is `False`. -/
theorem hInnerV :
    HasTypeAtV (m := Unit) 2 [("x", .mono (.var 1 0))]
      (let_ "inner" (lambda "y" (variable_ "y")) (apply (variable_ "inner") (variable_ "x")))
      (.var 1 0) .empty := by
  refine HasTypeAtV.let_poly (defnTy := .fun (.var 2 0) .empty (.var 2 0)) ?_ ?_ ?_
  · refine HasTypeAtV.lam (lvl' := 3) (by omega) ?_ ?_
    · intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega
    · exact HasTypeAtV.var (s := .mono (.var 2 0)) (args := []) rfl
  · intro b hb l hl
    simp only [List.mem_singleton] at hb; subst hb
    simp only [Scheme.mono, Ty.levels, List.mem_singleton] at hl; omega
  · refine HasTypeAtV.app (argTy := .var 1 0) (εf := .empty) ?_ (Ty.effWeaken_refl _) ?_
    · exact HasTypeAtV.var (s := Scheme.genAtV 2 (.fun (.var 2 0) .empty (.var 2 0)))
        (args := [.var 1 0]) rfl
    · exact HasTypeAtV.var (s := .mono (.var 1 0)) (args := []) rfl

/-- **The keystone fires on the outer lambda, instantiating the outer scheme at `integer`.** The outer
lambda `\x. (let inner = \y.y in inner x)` is typed at ambient level `1` (its body — `hInnerV` — at the
strictly higher level `2`, generalizing the nested `inner` at level `2`). `genAtV_instantiate_lam_ready`
produces the lambda re-typed at **every** instantiation of its scheme `genAtV 1 (α → α)`; here the
instantiation `[integer]` is shown. Non-vacuous: the outer body binds a `Lambda` in a `let`, the exact
shape the original `generalizes_closure_ready` chain cannot reach. -/
theorem hOuterV_instantiate :
    HasTypeAtV (m := Unit) 1 []
      (lambda "x" (let_ "inner" (lambda "y" (variable_ "y"))
        (apply (variable_ "inner") (variable_ "x"))))
      ((Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0))).instantiateV [.integer])
      .empty :=
  genAtV_instantiate_lam_ready (ℓ := 1) (by omega) (lvl' := 2) (by omega)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hInnerV
    (by intro b hb; simp at hb)
    (by intro b hb; simp at hb)
    [.integer]
    (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; intro l hl;
        simp only [Ty.levels] at hl; exact absurd hl (by simp))

/-- **The genuine, non-identity re-typing.** The keystone's instantiation
`(genAtV 1 (α → α)).instantiateV [integer]` computes to `integer → integer` (the outer type variable
`α` at level `1` is genuinely replaced by `integer`), so the doubly-generalized nested term type-checks
at `Integer → Integer` — the outer scheme opened non-vacuously, the inner scheme re-generalized
correctly at its own distinct level. This is the level-native "wall falls" check. -/
theorem hOuterV_typed_integer_arrow :
    HasTypeAtV (m := Unit) 1 []
      (lambda "x" (let_ "inner" (lambda "y" (variable_ "y"))
        (apply (variable_ "inner") (variable_ "x"))))
      (.fun .integer .empty .integer) .empty := by
  have h := hOuterV_instantiate
  have heq : (Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0))).instantiateV [.integer]
      = (.fun .integer .empty .integer : Ty) := rfl
  rwa [heq] at h

end NestedExample

end Eyg.Types
