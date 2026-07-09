import Eyg.Types.Typing

/-!
# G2 Phase-1 spike — `hasType_substAt_multi` (go/no-go gate)

The genuinely-new mathematics of the `eyg-g2-args-discipline-universal-readiness` plan: generalize
`hasType_substAt_le`'s σ-range bound `l = 0 ∨ l = ℓ` to a **per-level** side condition. The clean
condition (discovered here) is `l = 0 ∨ (l < lvl ∧ PolyAboveFV l Γ e)`:

* `l < lvl` (the root ambient) discharges the `lam`/`let`/`let_poly` bound-type `l < lvl'`
  obligations (ambient only grows going down) and the `let_poly` gen-level dodge `hcleanlvl`; it
  also makes the `NoGenAt l h` capture-avoidance free via `noGenAt_of_lt` — so, unlike the plan's
  tentative statement, `NoGenAt l h` need not be threaded.
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
substitution `substAt ℓ σ` whose range levels each are `0` or (`< lvl` and `PolyAboveFV`), with the
derivation-level `NoGenAt ℓ h` and `ℓ ≤ lvl`. Generalizes `hasType_substAt_le` (whose `σ`-range ⊆
`{0, ℓ}` is the
special case `l = ℓ ⟹ l < lvl` via `ℓ ≤ lvl` plus `PolyAboveFV ℓ Γ e = hΓ`). -/
theorem hasType_substAt_multi {ℓ : Nat} (hℓ : ℓ ≠ 0) (σ : Nat → Ty)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    {h : HasType lvl Γ e τ ε}
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ (l < lvl ∧ PolyAboveFV l Γ e))
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
          rcases hσ i s.level (Ty.mem_levels_of_mem_freeVarsAt hj) with h | ⟨_, hpa⟩
          · exact hlvl0 h
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
          rcases hσ i l hi with h | ⟨h, _⟩ <;> omega
      · have hσ' : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ (l < lvl' ∧
            PolyAboveFV l ((x, Scheme.mono argTy) :: Γ) body) := by
          intro i l hl
          rcases hσ i l hl with h | ⟨hlt', hpa⟩
          · exact Or.inl h
          · exact Or.inr ⟨lt_of_lt_of_le hlt' hle,
              polyAboveFV_bind (Or.inl rfl) hpa
                (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩)⟩
        have hb := ih hσ' (le_trans hlt hle)
          (polyAboveFV_bind (Or.inl rfl) hΓ
            (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩))
        rw [substCtxAt_cons, substSchemeVAt_mono] at hb
        exact hb
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg nghf ngharg ihf iharg =>
      intro hσ hlt hΓ
      have hσf : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ (l < lvl ∧ PolyAboveFV l Γ f) := by
        intro i l hl
        rcases hσ i l hl with h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr ⟨hlt', polyAboveFV_sub hpa (fun y hy => List.mem_append_left _ hy)⟩
      have hσa : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ (l < lvl ∧ PolyAboveFV l Γ arg) := by
        intro i l hl
        rcases hσ i l hl with h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr ⟨hlt', polyAboveFV_sub hpa (fun y hy => List.mem_append_right _ hy)⟩
      have hf' := ihf hσf hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy))
      simp only [Ty.substAt] at hf'
      exact HasType.app hf' (Ty.substAt_effWeaken ℓ σ hw)
        (iharg hσa hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_right _ hy)))
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody ngd ngb ihdefn ihbody =>
      intro hσ hlt hΓ
      have hσd : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ (l < lvl ∧ PolyAboveFV l Γ defn) := by
        intro i l hl
        rcases hσ i l hl with h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr ⟨hlt', polyAboveFV_sub hpa (fun y hy => List.mem_append_left _ hy)⟩
      have hσb : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ (l < lvl' ∧
          PolyAboveFV l ((x, Scheme.mono defnTy) :: Γ) body) := by
        intro i l hl
        rcases hσ i l hl with h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · exact Or.inr ⟨lt_of_lt_of_le hlt' hle,
            polyAboveFV_bind (Or.inl rfl) hpa
              (fun y hy hne =>
                List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne⟩))⟩
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
        rcases hσ i l hi with h | ⟨h, _⟩ <;> omega
  | @let_poly lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a hstrict hfv hbodydefn hcw
      hbody hne ngd ngb ihdefn ihbody =>
      intro hσ hlt hΓ
      have hlts : ℓ < lvl := lt_of_le_of_ne hlt (Ne.symm hne)
      have hne' : ℓ ≠ lvl := Nat.ne_of_lt hlts
      have hcleanlvl : ∀ i, lvl ∉ (σ i).levels := by
        intro i hmem; rcases hσ i lvl hmem with h | ⟨h, _⟩ <;> omega
      have hσltlvl : ∀ i, ∀ l ∈ (σ i).levels, l < lvl := by
        intro i l hl; rcases hσ i l hl with h | ⟨h, _⟩ <;> omega
      have hΓdefn : PolyAboveFV ℓ Γ ⟨.Lambda lx lbody, la⟩ :=
        polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy)
      have hΓdb : PolyAboveFV ℓ ((lx, Scheme.mono argTy) :: Γ) lbody :=
        polyAboveFV_bind (Or.inl rfl) hΓdefn
          (fun y hy hne2 => List.mem_filter.mpr ⟨hy, by simpa using hne2⟩)
      have hσdb : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ (l < lvl' ∧
          PolyAboveFV l ((lx, Scheme.mono argTy) :: Γ) lbody) := by
        intro i l hl
        rcases hσ i l hl with h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · refine Or.inr ⟨lt_trans hlt' hstrict, ?_⟩
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
          rcases hσ i l hi with h | ⟨h, _⟩ <;> omega
      have hΓ1 : PolyAboveFV ℓ ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body :=
        polyAboveFV_bind (Or.inr (by simp only [Scheme.genAtV]; omega)) hΓ
          (fun y hy hne2 => List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne2⟩))
      have hσ1 : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ (l < lvl + 1 ∧
          PolyAboveFV l ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body) := by
        intro i l hl
        rcases hσ i l hl with h | ⟨hlt', hpa⟩
        · exact Or.inl h
        · refine Or.inr ⟨by omega, ?_⟩
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

end Eyg.Types
