import Eyg.Types.Typing

/-!
# G2 Phase-1 spike — `hasType_substAt_multi` (go/no-go gate)

The genuinely-new mathematics of the `eyg-g2-args-discipline-universal-readiness` plan: generalize
`hasType_substAt_le`'s σ-range bound `l = 0 ∨ l = ℓ` to a **per-level** side condition. The winning
condition (discovered here) *strictly extends* it with a third disjunct:
`l = 0 ∨ l = ℓ ∨ (l < lvl ∧ PolyAboveFV l Γ e)`:

* `l = ℓ` is the existing `_le` fragment — discharged by the derivation-level `NoGenAt ℓ h` (`hng`)
  and `PolyAboveFV ℓ Γ e` (`hΓ`) exactly as there.
* `l < lvl` (the root ambient) is the new disjunct admitting the off-scheme instantiation levels
  (G30/G31). It discharges the `lam`/`let`/`let_poly` bound-type `l < lvl'` obligations (ambient
  only grows going down) and the `let_poly` gen-level dodge `hcleanlvl`; it also makes the
  `NoGenAt l h` capture-avoidance free via `noGenAt_of_lt` — so no per-level `NoGenAt l h` threads.
* `PolyAboveFV l Γ e` (per σ-range level) is the var-arm capture avoidance against context schemes.

Spike file — validated with `lake env lean`. Promoted into `Typing.lean` once green.
-/

namespace Eyg.Types

open Eyg.Ir

variable {m : Type}

/-- `CtxWfV` transports under `substAt ℓ σ` when σ's range levels are all `< L` (the ambient at
which the context is well-formed). The `< L` variant of `ctxWfV_substCtxAt` (needs `≤ ℓ < L`). -/
theorem ctxWfV_substCtxAt_lt {ℓ L : Nat} {σ : Nat → Ty}
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l < L) {Γ : Ctx} (hΓ : CtxWfV L Γ) :
    CtxWfV L (substCtxAt ℓ σ Γ) := by
  intro b hb l hl
  simp only [substCtxAt, List.mem_map] at hb
  obtain ⟨⟨y, s⟩, hmem, rfl⟩ := hb
  simp only [Scheme.substSchemeVAt] at hl
  rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
  · exact hΓ (y, s) hmem l hl'
  · exact hσ i l hi

/-- **The per-level readiness keystone.** Re-types a derivation under an outer level-`ℓ`
substitution `substAt ℓ σ` whose range levels each are `0`, `= ℓ`, or (`< lvl` and `PolyAboveFV`),
with the derivation-level `NoGenAt ℓ h` and `ℓ ≤ lvl`. Strictly generalizes `hasType_substAt_le`
(its `σ`-range ⊆ `{0, ℓ}` is the `l = 0 ∨ l = ℓ` fragment — the `l = ℓ` disjunct is discharged by
`hng`/`hΓ` exactly as there); the new third disjunct `l < lvl ∧ PolyAboveFV l Γ e` is what admits
the off-scheme instantiation levels (G30/G31) — `l < lvl` gives every bound-type `l < lvl'` bound
and the gen-level dodge (plus `NoGenAt l h` free via `noGenAt_of_lt`), `PolyAboveFV l` gives the
var-arm capture avoidance. -/
theorem hasType_substAt_multi {ℓ : Nat} (hℓ : ℓ ≠ 0) (σ : Nat → Ty)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    {h : HasType lvl Γ e τ ε}
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl ∧ PolyAboveFV l Γ e))
    (hng : NoGenAt ℓ h) (hlt : ℓ ≤ lvl) (hΓ : PolyAboveFV ℓ Γ e) :
    HasType lvl (substCtxAt ℓ σ Γ) e (Ty.substAt ℓ σ τ) (Ty.substAt ℓ σ ε) := by
  revert hlt hΓ hσ
  induction hng with
  | @var lvl Γ x s args ε a hl =>
      intro hσ hlt hΓ
      have hdisj : s.arity = 0 ∨ (ℓ ≠ s.level ∧ ∀ i, ∀ j, j ∉ Ty.freeVarsAt s.level (σ i)) := by
        by_cases h0 : s.arity = 0
        · exact Or.inl h0
        · obtain ⟨hlvl0, hlvlℓ⟩ :=
            (hΓ x (by simp [Tree.Node.freeVars]) s hl).resolve_left h0
          refine Or.inr ⟨Ne.symm hlvlℓ, ?_⟩
          intro i j hj
          rcases hσ i s.level (Ty.mem_levels_of_mem_freeVarsAt hj) with h | h | ⟨_, hpa⟩
          · exact hlvl0 h
          · exact hlvlℓ h
          · exact absurd rfl ((hpa x (by simp [Tree.Node.freeVars]) s hl).resolve_left h0).2
      rw [substAt_instantiateV_scheme hdisj args]
      exact HasType.var (substCtxAt_lookup hl)
  | @builtin lvl Γ id s args ε a hs =>
      intro hσ hlt hΓ
      rw [substAt_instantiateV_closed (by rw [Builtins.scheme_level hs]; exact hℓ)
            (Builtins.scheme_no_level hℓ hs) args,
          Builtins.scheme_substSchemeVAt hℓ σ hs]
      exact HasType.builtin hs
  | @lam lvl lvl' Γ x body argTy εb retTy ε a hle hfv hbody nghbody ih =>
      intro hσ hlt hΓ
      simp only [Ty.substAt]
      refine HasType.lam hle ?_ ?_
      · intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hfv l hl'
        · have hℓlt := hfv ℓ hm
          rcases hσ i l hi with h | h | ⟨h, _⟩ <;> omega
      · have hσ' : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl' ∧
            PolyAboveFV l ((x, Scheme.mono argTy) :: Γ) body) := by
          intro i l hl
          rcases hσ i l hl with h | h | ⟨hlt', hpa⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨lt_of_lt_of_le hlt' hle,
              polyAboveFV_bind (Or.inl rfl) hpa
                (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩)⟩)
        have hb := ih hσ' (le_trans hlt hle)
          (polyAboveFV_bind (Or.inl rfl) hΓ
            (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩))
        rw [substCtxAt_cons, substSchemeVAt_mono] at hb
        exact hb
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg nghf ngharg ihf iharg =>
      intro hσ hlt hΓ
      have hσf : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl ∧ PolyAboveFV l Γ f) := by
        intro i l hl
        rcases hσ i l hl with h | h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨hlt', polyAboveFV_sub hpa (fun y hy => List.mem_append_left _ hy)⟩)
      have hσa : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl ∧ PolyAboveFV l Γ arg) := by
        intro i l hl
        rcases hσ i l hl with h | h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨hlt', polyAboveFV_sub hpa (fun y hy => List.mem_append_right _ hy)⟩)
      have hf' := ihf hσf hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy))
      simp only [Ty.substAt] at hf'
      exact HasType.app hf' (Ty.substAt_effWeaken ℓ σ hw)
        (iharg hσa hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_right _ hy)))
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody ngd ngb ihdefn ihbody =>
      intro hσ hlt hΓ
      have hσd : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl ∧ PolyAboveFV l Γ defn) := by
        intro i l hl
        rcases hσ i l hl with h | h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨hlt', polyAboveFV_sub hpa (fun y hy => List.mem_append_left _ hy)⟩)
      have hσb : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl' ∧
          PolyAboveFV l ((x, Scheme.mono defnTy) :: Γ) body) := by
        intro i l hl
        rcases hσ i l hl with h | h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨lt_of_lt_of_le hlt' hle,
            polyAboveFV_bind (Or.inl rfl) hpa
              (fun y hy hne =>
                List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne⟩))⟩)
      have hb := ihbody hσb (le_trans hlt hle)
        (polyAboveFV_bind (Or.inl rfl) hΓ
          (fun y hy hne => List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne⟩)))
      rw [substCtxAt_cons, substSchemeVAt_mono] at hb
      refine HasType.let_
        (ihdefn hσd hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy)))
        hle ?_ hb
      intro l hl
      rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
      · exact hfv l hl'
      · have hℓlt := hfv ℓ hm
        rcases hσ i l hi with h | h | ⟨h, _⟩ <;> omega
  | @let_poly lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a hstrict hfv hbodydefn hcw
      hbody hne ngd ngb ihdefn ihbody =>
      intro hσ hlt hΓ
      have hlts : ℓ < lvl := lt_of_le_of_ne hlt (Ne.symm hne)
      have hne' : ℓ ≠ lvl := Nat.ne_of_lt hlts
      have hcleanlvl : ∀ i, lvl ∉ (σ i).levels := by
        intro i hmem; rcases hσ i lvl hmem with h | h | ⟨h, _⟩ <;> omega
      have hσltlvl : ∀ i, ∀ l ∈ (σ i).levels, l < lvl := by
        intro i l hl; rcases hσ i l hl with h | h | ⟨h, _⟩ <;> omega
      have hΓdefn : PolyAboveFV ℓ Γ ⟨.Lambda lx lbody, la⟩ :=
        polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy)
      have hΓdb : PolyAboveFV ℓ ((lx, Scheme.mono argTy) :: Γ) lbody :=
        polyAboveFV_bind (Or.inl rfl) hΓdefn
          (fun y hy hne2 => List.mem_filter.mpr ⟨hy, by simpa using hne2⟩)
      have hσdb : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl' ∧
          PolyAboveFV l ((lx, Scheme.mono argTy) :: Γ) lbody) := by
        intro i l hl
        rcases hσ i l hl with h | h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · refine Or.inr (Or.inr ⟨lt_trans hlt' hstrict, ?_⟩)
          have hpad : PolyAboveFV l Γ ⟨.Lambda lx lbody, la⟩ :=
            polyAboveFV_sub hpa (fun y hy => List.mem_append_left _ hy)
          exact polyAboveFV_bind (Or.inl rfl) hpad
            (fun y hy hne2 => List.mem_filter.mpr ⟨hy, by simpa using hne2⟩)
      have hbd := ihdefn hσdb (le_of_lt (lt_trans hlts hstrict)) hΓdb
      rw [substCtxAt_cons, substSchemeVAt_mono] at hbd
      have hfv' : ∀ l ∈ (Ty.substAt ℓ σ argTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hfv l hl'
        · have hℓlt := hfv ℓ hm
          rcases hσ i l hi with h | h | ⟨h, _⟩ <;> omega
      have hΓ1 : PolyAboveFV ℓ ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body :=
        polyAboveFV_bind (Or.inr (by simp only [Scheme.genAtV]; omega)) hΓ
          (fun y hy hne2 => List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne2⟩))
      have hσ1 : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl + 1 ∧
          PolyAboveFV l ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body) := by
        intro i l hl
        rcases hσ i l hl with h | h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
          exact polyAboveFV_bind (Or.inr (by simp only [Scheme.genAtV]; omega)) hpa
            (fun y hy hne2 =>
              List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne2⟩))
      have hbodyIH := ihbody hσ1 (by omega : ℓ ≤ lvl + 1) hΓ1
      rw [substCtxAt_cons_genAtV hne' hcleanlvl] at hbodyIH
      simp only [Ty.substAt] at hbodyIH
      exact HasType.let_poly hstrict hfv' hbd (ctxWfV_substCtxAt_lt hσltlvl hcw) hbodyIH
  | int => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.int
  | str => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.str
  | bin => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.bin
  | tail => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.tail
  | cons => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.cons
  | tag => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.tag
  | nocases => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.nocases
  | case_ => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.case_
  | select => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.select
  | extend => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.extend
  | overwrite => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.overwrite
  | empty => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.empty
  | perform => intro hσ hlt hΓ; simp only [Ty.substAt]; exact HasType.perform
  | @handle lvl Γ l lift reply tail ret ε a =>
      intro hσ hlt hΓ
      have heq : Ty.substAt ℓ σ (handleTy l lift reply tail ret)
          = handleTy l (Ty.substAt ℓ σ lift) (Ty.substAt ℓ σ reply) (Ty.substAt ℓ σ tail)
              (Ty.substAt ℓ σ ret) := by
        simp [handleTy, handlerTy, execTy, kontTy, Ty.substAt]
      rw [heq]; exact HasType.handle
  | @conv lvl Γ e τ τ' ε ε' h hτ hε ngh ih =>
      intro hσ hlt hΓ
      exact HasType.conv (ih hσ hlt hΓ) (Ty.substAt_tyEquiv ℓ σ hτ) (Ty.substAt_tyEquiv ℓ σ hε)

/-- **Subsumption check.** `hasType_substAt_multi` strictly generalizes `hasType_substAt_le`: the
`{0, ℓ}` σ-range bound is the first two disjuncts, so the `_le` statement is an immediate corollary
(no extra hypotheses). Machine-confirms the "strictly generalizes" claim. -/
theorem hasType_substAt_le_of_multi {ℓ : Nat} (hℓ : ℓ ≠ 0) (σ : Nat → Ty)
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    {h : HasType lvl Γ e τ ε} (hng : NoGenAt ℓ h) (hlt : ℓ ≤ lvl)
    (hΓ : PolyAboveFV ℓ Γ e) :
    HasType lvl (substCtxAt ℓ σ Γ) e (Ty.substAt ℓ σ τ) (Ty.substAt ℓ σ ε) :=
  hasType_substAt_multi hℓ σ (fun i l hl => (hσ i l hl).imp_right Or.inl) hng hlt hΓ

/-- **The floor-conditioned term-level readiness keystone.** The `hasType_substAt_multi`-powered
generalization of `genAtV_instantiate_lam_ready_le`: a value-restricted lambda's `genAtV ℓ`-scheme
realised as a genuine `substAt ℓ` re-typing of its own body derivation at instantiation args whose
levels obey the **floor** form `l = 0 ∨ l = ℓ ∨ (l < lvl' ∧ PolyAboveFV l Γ ⟨lam⟩)` — with `lvl'`
(the body sublevel) as the floor `B`. This is the consumption site the plan's §3 names: exactly the
G30/G31 off-scheme instantiation levels are now admitted (they satisfy `l < lvl'`), no grounding.
The `_le` keystone is the `hargs ⊆ {0, ℓ}` special case. -/
theorem genAtV_instantiate_lam_ready_floor {ℓ : Nat} (hℓ : ℓ ≠ 0)
    {lvl' : Nat} {Γ : Ctx} {x : String} {lbody : Tree.Node m} {la : m}
    {argTy εb retTy ε : Ty}
    (hlt : ℓ ≤ lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    {hbody : HasType lvl' ((x, .mono argTy) :: Γ) lbody retTy εb}
    (hng : NoGenAt ℓ hbody)
    (hΓpa : PolyAboveFV ℓ Γ ⟨.Lambda x lbody, la⟩)
    (hΓwf : CtxWfV ℓ Γ)
    (args : List Ty)
    (hargs : ∀ t ∈ args, ∀ l ∈ t.levels,
      l = 0 ∨ l = ℓ ∨ (l < lvl' ∧ PolyAboveFV l Γ ⟨.Lambda x lbody, la⟩)) :
    HasType ℓ Γ ⟨.Lambda x lbody, la⟩
      ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) ε := by
  set defnTy : Ty := .fun argTy εb retTy with hdefn
  have hΓpa' : PolyAboveFV ℓ ((x, Scheme.mono argTy) :: Γ) lbody :=
    polyAboveFV_bind (Or.inl rfl) hΓpa
      (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩)
  by_cases h0 : (Scheme.genAtV ℓ defnTy).arity = 0
  · rw [Scheme.instantiateV, if_pos h0, ← Ty.substAt_var_self ℓ defnTy]
    have hσ : ∀ i, ∀ l ∈ ((fun i => Ty.var ℓ i) i).levels,
        l = 0 ∨ l = ℓ ∨ (l < lvl' ∧ PolyAboveFV l ((x, Scheme.mono argTy) :: Γ) lbody) := by
      intro i l hl; simp only [Ty.levels, List.mem_singleton] at hl; exact Or.inr (Or.inl hl)
    have hb := hasType_substAt_multi hℓ (fun i => Ty.var ℓ i) hσ hng hlt hΓpa'
    rw [substCtxAt_cons, substSchemeVAt_mono] at hb
    have hlam := HasType.lam (a := la) (ε := ε) hlt
      (by intro l hl
          rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
          · exact hfv l hl'
          · simp only [Ty.levels, List.mem_singleton] at hi; rw [hi]; exact hfv ℓ hm) hb
    have hfix : substCtxAt ℓ (fun i => Ty.var ℓ i) Γ = Γ := substCtxAt_fix hΓwf
    rw [hfix] at hlam
    simpa only [Ty.substAt, hdefn] using hlam
  · rw [Scheme.instantiateV, if_neg h0]
    have hσ : ∀ i, ∀ l ∈ (args.getD i (.var ℓ i)).levels,
        l = 0 ∨ l = ℓ ∨ (l < lvl' ∧ PolyAboveFV l ((x, Scheme.mono argTy) :: Γ) lbody) := by
      intro i l hl
      rcases lt_or_ge i args.length with hi | hi
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hl
        rcases hargs _ (List.getElem_mem hi) l hl with h | h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨hlt',
            polyAboveFV_bind (Or.inl rfl) hpa
              (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩)⟩)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none] at hl
        simp only [Ty.levels, List.mem_singleton] at hl; exact Or.inr (Or.inl hl)
    have hb := hasType_substAt_multi hℓ (fun i => args.getD i (.var ℓ i)) hσ hng hlt hΓpa'
    rw [substCtxAt_cons, substSchemeVAt_mono] at hb
    have hlam := HasType.lam (a := la) (ε := ε) hlt
      (by intro l hl
          rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
          · exact hfv l hl'
          · have hℓlt := hfv ℓ hm; rcases hσ i l hi with h | h | ⟨h, _⟩ <;> omega) hb
    have hfix : substCtxAt ℓ (fun i => args.getD i (.var ℓ i)) Γ = Γ := substCtxAt_fix hΓwf
    rw [hfix] at hlam
    simpa only [Ty.substAt, hdefn] using hlam

/-! ## Universal readiness for the closing case (via `hasType_fullRaise`) -/

/-- `raiseScheme_U` fixes a scheme whose gen level and body levels are all `< t`. -/
theorem raiseScheme_U_eq_self {t o : Nat} {s : Scheme}
    (hlvl : s.level < t) (hbody : ∀ l ∈ s.body.levels, l < t) :
    raiseScheme_U t o s = s := by
  simp only [raiseScheme_U, if_neg (Nat.not_le.mpr hlvl), Ty.raiseTy_eq_self_of_levels_lt hbody]

/-- `raiseCtx_U` fixes a context all of whose schemes it fixes. -/
theorem raiseCtx_U_eq_self {t o : Nat} {Γ : Ctx}
    (h : ∀ b ∈ Γ, raiseScheme_U t o b.2 = b.2) : raiseCtx_U t o Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons b tl ih =>
      rw [raiseCtx_U_cons, ih (fun c hc => h c (List.mem_cons_of_mem _ hc)),
        h b List.mem_cons_self]

/-- **Universal readiness for the CLOSING case.** When the closure's captured context `Γ`, `argTy`,
`retTy`, and `εb` all have levels `< lvl'` (the body sublevel), readiness holds at **any** args:
raise
the stored body's sublevel above the args by a fresh offset `o` (the closure's advertised type is
unchanged — every moved level is `< lvl'` = the raise threshold, so `raiseTy` fixes it), then the
floor keystone discharges. No `ArgsDisc`, no rule change — only `hasType_fullRaise` (landed) + the
floor keystone. The residual is exactly the escaping-`retTy` case where a `< lvl'` premise fails. -/
theorem genAtV_instantiate_lam_ready_universal {ℓ lvl' : Nat} {Γ : Ctx} {x : String}
    {lbody : Tree.Node m} {la : m} {argTy εb retTy ε : Ty}
    (hℓ : ℓ ≠ 0) (hlt : ℓ ≤ lvl') (h1 : 1 ≤ lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hretTy : ∀ l ∈ retTy.levels, l < lvl')
    (hεb : ∀ l ∈ εb.levels, l < lvl')
    {hbody : HasType lvl' ((x, .mono argTy) :: Γ) lbody retTy εb}
    (hΓpa : ∀ l, PolyAboveFV l Γ ⟨.Lambda x lbody, la⟩)
    (hΓwf : CtxWfV ℓ Γ) (hΓlt : CtxWfV lvl' Γ) (hΓsl : ∀ b ∈ Γ, b.2.level < lvl')
    (o : Nat) (ho : 1 ≤ o) (args : List Ty)
    (hargbound : ∀ t ∈ args, ∀ l ∈ t.levels, l < lvl' + o) :
    HasType ℓ Γ ⟨.Lambda x lbody, la⟩
      ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) ε := by
  have hraised := hasType_fullRaise (t := lvl') (o := o) h1 hbody (le_refl lvl')
  rw [raiseCtx_U_cons, raiseScheme_U_mono h1, Ty.raiseTy_eq_self_of_levels_lt hfv,
      raiseCtx_U_eq_self
        (fun b hb => raiseScheme_U_eq_self (hΓsl b hb) (fun l hl => hΓlt b hb l hl)),
      Ty.raiseTy_eq_self_of_levels_lt hretTy, Ty.raiseTy_eq_self_of_levels_lt hεb] at hraised
  exact genAtV_instantiate_lam_ready_floor hℓ (by omega : ℓ ≤ lvl' + o)
    (fun l hl => by have := hfv l hl; omega)
    (noGenAt_of_lt hraised (by omega)) (hΓpa ℓ) hΓwf args
    (fun t ht l hl => Or.inr (Or.inr ⟨hargbound t ht l hl, hΓpa l⟩))

end Eyg.Types
