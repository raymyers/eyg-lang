import Eyg.Types.G2Spike
import Eyg.Types.ClosDisc
import Eyg.Types.Generation

/-!
# G2 Phase 3 (spike) — `ClosDisc` preserved through the readiness substitution

The go/no-go gate for the front-door discipline (finding 16): populating the `ClosDisc hbody`
field on `HasTypeV.closure` at the readiness site needs `ClosDisc` preserved through the raise +
`substAt` the readiness lemma performs. This file spikes **both** halves —
`closDisc_substAt_multi` and `closDisc_fullRaise` — `ClosDisc`-bundling companions of
`hasType_substAt_multi`/`hasType_fullRaise` (each returns `⟨h', ClosDisc h'⟩` at the new type).

## Avoiding the dependent-inversion friction

`hasType_substAt_multi` inducts on `NoGenAt ℓ h`; a naive companion would `cases` `ClosDisc h` at
each arm — but `HasType.lam` hides the sublevel `lvl'` from its type, so `ClosDisc.lam`'s
`retTy < lvl'` fields are **un-invertable** at a node (`cases` binds a fresh `lvl'`). We instead
**induct on `ClosDisc h` directly** (its fields come for free) and drop `NoGenAt` entirely: the
only place the substitution needs it is the `let_poly` arm's `lvl ≠ ℓ`, from a *strict* numeric
`ℓ < lvl` (available in the readiness setting — the `argsRaiseOffset` raise puts `ℓ` strictly below
every ambient; cf. `noGenAt_of_lt`). So no derivation-indexed predicate is cross-inverted.

## The level argument (compiler-verified here, not trusted)

* **`lam`/`let_poly` bounds** (`retTy`/`εb`/`argTy` `< lvl'`) survive with **no new σ-condition**: a
  substituted level is either an original non-`ℓ` level (`< lvl'` by the input discipline) or
  comes from `σ` at an `ℓ`-position (`ℓ ∈ retTy ⇒ ℓ < lvl'`; `hσ`'s disjuncts are each `< lvl'`).
* **`var`/`builtin` args** (`l = 0 ∨ s.level ≤ l`) need `σ`'s levels `0 ∨ ℓ ≤ l` (`hσdisc`) —
  exactly the widened `EnvWf.cons`/promise precondition. Then a substituted arg level is original
  (`0 ∨ s.level ≤`) or from `σ`: `0` ✓, or `≥ ℓ ≥ s.level` (since `ℓ ∈ t ⇒ s.level ≤ ℓ`).
  `substSchemeVAt` preserves `.level` definitionally.

Spike; additive; validated with `lake env lean` (independent of WIP `Soundness.lean`).
-/

namespace Eyg.Types

open Eyg.Ir

variable {m : Type}

/-- **`ClosDisc` survives the readiness `substAt`.** Bundled companion of `hasType_substAt_multi`
(inducting on `ClosDisc` with a strict numeric `ℓ < lvl` in place of `NoGenAt`): under the
substitution premises **plus** the widened arg-discipline `hσdisc` (`σ` levels `0 ∨ ℓ ≤ l`), a
closure-disciplined derivation re-types under `substAt ℓ σ` to one that is **again** disciplined. -/
theorem closDisc_substAt_multi {ℓ : Nat} (hℓ : ℓ ≠ 0) (σ : Nat → Ty)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    {h : HasType lvl Γ e τ ε} (hcd : ClosDisc h) :
      (∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl ∧ PolyAboveFV l Γ e)) →
      (∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ ℓ ≤ l) →
      ℓ < lvl → PolyAboveFV ℓ Γ e →
      ∃ h' : HasType lvl (substCtxAt ℓ σ Γ) e (Ty.substAt ℓ σ τ) (Ty.substAt ℓ σ ε),
        ClosDisc h' := by
  induction hcd with
  | @var lvl Γ x s args ε a hl hargs =>
      intro hσ hσdisc hℓlt hΓ
      have hdisj : s.arity = 0 ∨ (ℓ ≠ s.level ∧ ∀ i, ∀ j, j ∉ Ty.freeVarsAt s.level (σ i)) := by
        by_cases h0 : s.arity = 0
        · exact Or.inl h0
        · obtain ⟨hlvl0, hlvlℓ⟩ := (hΓ x (by simp [Tree.Node.freeVars]) s hl).resolve_left h0
          refine Or.inr ⟨Ne.symm hlvlℓ, ?_⟩
          intro i j hj
          rcases hσ i s.level (Ty.mem_levels_of_mem_freeVarsAt hj) with hh | hh | ⟨_, hpa⟩
          · exact hlvl0 hh
          · exact hlvlℓ hh
          · exact absurd rfl ((hpa x (by simp [Tree.Node.freeVars]) s hl).resolve_left h0).2
      have hargs' : ∀ t ∈ args.map (Ty.substAt ℓ σ), ∀ l ∈ t.levels,
          l = 0 ∨ (Scheme.substSchemeVAt ℓ σ s).level ≤ l := by
        intro t ht l hl'
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        rcases Ty.mem_levels_substAt_strong hl' with hl0 | ⟨hm, i, hi⟩
        · exact hargs t0 ht0 l hl0
        · have hsℓ : s.level ≤ ℓ := (hargs t0 ht0 ℓ hm).resolve_left hℓ
          rcases hσdisc i l hi with h0 | hle'
          · exact Or.inl h0
          · exact Or.inr (le_trans hsℓ hle')
      rw [substAt_instantiateV_scheme hdisj args]
      exact ⟨HasType.var (substCtxAt_lookup hl), ClosDisc.var (substCtxAt_lookup hl) hargs'⟩
  | @builtin lvl Γ id s args ε a hs hargs =>
      intro hσ hσdisc hℓlt hΓ
      rw [substAt_instantiateV_closed (by rw [Builtins.scheme_level hs]; exact hℓ)
            (Builtins.scheme_no_level hℓ hs) args,
          Builtins.scheme_substSchemeVAt hℓ σ hs]
      exact ⟨HasType.builtin hs, ClosDisc.builtin hs
        (fun t _ l _ => Or.inr (by rw [Builtins.scheme_level hs]; exact Nat.zero_le l))⟩
  | @lam lvl lvl' Γ x body argTy εb retTy ε a hle hfv hret hεb hbody cdbody ih =>
      intro hσ hσdisc hℓlt hΓ
      have hfv' : ∀ l ∈ (Ty.substAt ℓ σ argTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hfv l hl'
        · have := hfv ℓ hm; rcases hσ i l hi with hh | hh | ⟨hh, _⟩ <;> omega
      have hret' : ∀ l ∈ (Ty.substAt ℓ σ retTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hret l hl'
        · have := hret ℓ hm; rcases hσ i l hi with hh | hh | ⟨hh, _⟩ <;> omega
      have hεb' : ∀ l ∈ (Ty.substAt ℓ σ εb).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hεb l hl'
        · have := hεb ℓ hm; rcases hσ i l hi with hh | hh | ⟨hh, _⟩ <;> omega
      have hσ' : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl' ∧
          PolyAboveFV l ((x, Scheme.mono argTy) :: Γ) body) := by
        intro i l hl
        rcases hσ i l hl with hh | hh | ⟨hlt', hpa⟩
        · exact Or.inl hh
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr ⟨lt_of_lt_of_le hlt' hle,
            polyAboveFV_bind (Or.inl rfl) hpa
              (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩)⟩)
      obtain ⟨hb, cdb⟩ := ih hσ' hσdisc (lt_of_lt_of_le hℓlt hle)
        (polyAboveFV_bind (Or.inl rfl) hΓ
          (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩))
      simp only [substCtxAt_cons, substSchemeVAt_mono] at hb cdb
      simp only [Ty.substAt]
      exact ⟨HasType.lam hle hfv' hb, ClosDisc.lam hle hfv' hret' hεb' cdb⟩
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg cdf cdarg ihf iharg =>
      intro hσ hσdisc hℓlt hΓ
      have hσf : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl ∧ PolyAboveFV l Γ f) := by
        intro i l hl
        rcases hσ i l hl with hh | hh | ⟨hlt', hpa⟩
        · exact Or.inl hh
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr ⟨hlt', polyAboveFV_sub hpa (fun y hy => List.mem_append_left _ hy)⟩)
      have hσa : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl ∧ PolyAboveFV l Γ arg) := by
        intro i l hl
        rcases hσ i l hl with hh | hh | ⟨hlt', hpa⟩
        · exact Or.inl hh
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr ⟨hlt', polyAboveFV_sub hpa (fun y hy => List.mem_append_right _ hy)⟩)
      obtain ⟨hf', cdf'⟩ := ihf hσf hσdisc hℓlt
        (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy))
      obtain ⟨harg', cdarg'⟩ := iharg hσa hσdisc hℓlt
        (polyAboveFV_sub hΓ (fun y hy => List.mem_append_right _ hy))
      simp only [Ty.substAt] at hf'
      exact ⟨HasType.app hf' (Ty.substAt_effWeaken ℓ σ hw) harg',
        ClosDisc.app (hw := Ty.substAt_effWeaken ℓ σ hw) cdf' cdarg'⟩
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody cdd cdb ihd ihb =>
      intro hσ hσdisc hℓlt hΓ
      have hσd : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl ∧ PolyAboveFV l Γ defn) := by
        intro i l hl
        rcases hσ i l hl with hh | hh | ⟨hlt', hpa⟩
        · exact Or.inl hh
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr ⟨hlt', polyAboveFV_sub hpa (fun y hy => List.mem_append_left _ hy)⟩)
      have hσb : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl' ∧
          PolyAboveFV l ((x, Scheme.mono defnTy) :: Γ) body) := by
        intro i l hl
        rcases hσ i l hl with hh | hh | ⟨hlt', hpa⟩
        · exact Or.inl hh
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr ⟨lt_of_lt_of_le hlt' hle,
            polyAboveFV_bind (Or.inl rfl) hpa
              (fun y hy hne =>
                List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne⟩))⟩)
      obtain ⟨hd', cdd'⟩ := ihd hσd hσdisc hℓlt
        (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy))
      obtain ⟨hb, cdb'⟩ := ihb hσb hσdisc (lt_of_lt_of_le hℓlt hle)
        (polyAboveFV_bind (Or.inl rfl) hΓ
          (fun y hy hne => List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne⟩)))
      simp only [substCtxAt_cons, substSchemeVAt_mono] at hb cdb'
      have hfv' : ∀ l ∈ (Ty.substAt ℓ σ defnTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hfv l hl'
        · have := hfv ℓ hm; rcases hσ i l hi with hh | hh | ⟨hh, _⟩ <;> omega
      exact ⟨HasType.let_ hd' hle hfv' hb, ClosDisc.let_ hle hfv' cdd' cdb'⟩
  | @let_poly lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a hstrict hfv hret hεb hbodydefn
      hcw hbody cddefn cdbody ihdefn ihbody =>
      intro hσ hσdisc hℓlt hΓ
      have hne' : ℓ ≠ lvl := Nat.ne_of_lt hℓlt
      have hcleanlvl : ∀ i, lvl ∉ (σ i).levels := by
        intro i hmem; rcases hσ i lvl hmem with hh | hh | ⟨hh, _⟩ <;> omega
      have hσltlvl : ∀ i, ∀ l ∈ (σ i).levels, l < lvl := by
        intro i l hl; rcases hσ i l hl with hh | hh | ⟨hh, _⟩ <;> omega
      have hΓdefn : PolyAboveFV ℓ Γ ⟨.Lambda lx lbody, la⟩ :=
        polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy)
      have hΓdb : PolyAboveFV ℓ ((lx, Scheme.mono argTy) :: Γ) lbody :=
        polyAboveFV_bind (Or.inl rfl) hΓdefn
          (fun y hy hne2 => List.mem_filter.mpr ⟨hy, by simpa using hne2⟩)
      have hσdb : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl' ∧
          PolyAboveFV l ((lx, Scheme.mono argTy) :: Γ) lbody) := by
        intro i l hl
        rcases hσ i l hl with hh | hh | ⟨hlt', hpa⟩
        · exact Or.inl hh
        · exact Or.inr (Or.inl hh)
        · refine Or.inr (Or.inr ⟨lt_trans hlt' hstrict, ?_⟩)
          have hpad : PolyAboveFV l Γ ⟨.Lambda lx lbody, la⟩ :=
            polyAboveFV_sub hpa (fun y hy => List.mem_append_left _ hy)
          exact polyAboveFV_bind (Or.inl rfl) hpad
            (fun y hy hne2 => List.mem_filter.mpr ⟨hy, by simpa using hne2⟩)
      obtain ⟨hbd, cdbd⟩ := ihdefn hσdb hσdisc (lt_trans hℓlt hstrict) hΓdb
      simp only [substCtxAt_cons, substSchemeVAt_mono] at hbd cdbd
      have hfv' : ∀ l ∈ (Ty.substAt ℓ σ argTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hfv l hl'
        · have := hfv ℓ hm; rcases hσ i l hi with hh | hh | ⟨hh, _⟩ <;> omega
      have hret' : ∀ l ∈ (Ty.substAt ℓ σ retTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hret l hl'
        · have := hret ℓ hm; rcases hσ i l hi with hh | hh | ⟨hh, _⟩ <;> omega
      have hεb' : ∀ l ∈ (Ty.substAt ℓ σ εb).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hεb l hl'
        · have := hεb ℓ hm; rcases hσ i l hi with hh | hh | ⟨hh, _⟩ <;> omega
      have hΓ1 : PolyAboveFV ℓ ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body :=
        polyAboveFV_bind (Or.inr (by simp only [Scheme.genAtV]; omega)) hΓ
          (fun y hy hne2 =>
            List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne2⟩))
      have hσ1 : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ ∨ (l < lvl + 1 ∧
          PolyAboveFV l ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body) := by
        intro i l hl
        rcases hσ i l hl with hh | hh | ⟨hlt', hpa⟩
        · exact Or.inl hh
        · exact Or.inr (Or.inl hh)
        · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
          exact polyAboveFV_bind (Or.inr (by simp only [Scheme.genAtV]; omega)) hpa
            (fun y hy hne2 =>
              List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne2⟩))
      obtain ⟨hbodyIH, cdbodyIH⟩ := ihbody hσ1 hσdisc (by omega : ℓ < lvl + 1) hΓ1
      simp only [substCtxAt_cons_genAtV hne' hcleanlvl, Ty.substAt] at hbodyIH cdbodyIH
      exact ⟨HasType.let_poly hstrict hfv' hbd (ctxWfV_substCtxAt_lt hσltlvl hcw) hbodyIH,
        ClosDisc.let_poly hstrict hfv' hret' hεb'
          (hcw := ctxWfV_substCtxAt_lt hσltlvl hcw) cdbd cdbodyIH⟩
  | int => intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.int, ClosDisc.int⟩
  | str => intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.str, ClosDisc.str⟩
  | bin => intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.bin, ClosDisc.bin⟩
  | tail => intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.tail, ClosDisc.tail⟩
  | cons => intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.cons, ClosDisc.cons⟩
  | tag => intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.tag, ClosDisc.tag⟩
  | nocases =>
      intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.nocases, ClosDisc.nocases⟩
  | case_ =>
      intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.case_, ClosDisc.case_⟩
  | select =>
      intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.select, ClosDisc.select⟩
  | extend =>
      intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.extend, ClosDisc.extend⟩
  | overwrite =>
      intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]
      exact ⟨HasType.overwrite, ClosDisc.overwrite⟩
  | empty => intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.empty, ClosDisc.empty⟩
  | perform =>
      intro hσ hσdisc hℓlt hΓ; simp only [Ty.substAt]
      exact ⟨HasType.perform, ClosDisc.perform⟩
  | @handle lvl Γ l lift reply tail ret ε a =>
      intro hσ hσdisc hℓlt hΓ
      have heq : Ty.substAt ℓ σ (handleTy l lift reply tail ret)
          = handleTy l (Ty.substAt ℓ σ lift) (Ty.substAt ℓ σ reply) (Ty.substAt ℓ σ tail)
              (Ty.substAt ℓ σ ret) := by
        simp [handleTy, handlerTy, execTy, kontTy, Ty.substAt]
      rw [heq]; exact ⟨HasType.handle, ClosDisc.handle⟩
  | @conv lvl Γ e τ τ' ε ε' hh hτ hε cdh ih =>
      intro hσ hσdisc hℓlt hΓ
      obtain ⟨h', cdh'⟩ := ih hσ hσdisc hℓlt hΓ
      exact ⟨HasType.conv h' (Ty.substAt_tyEquiv ℓ σ hτ) (Ty.substAt_tyEquiv ℓ σ hε),
        ClosDisc.conv (Ty.substAt_tyEquiv ℓ σ hτ) (Ty.substAt_tyEquiv ℓ σ hε) cdh'⟩

/-- **`ClosDisc` survives the readiness `fullRaise`.** Bundled companion of `hasType_fullRaise`
(inducting on `ClosDisc`): the uniform `+o` relabel of levels `≥ t` shifts every discipline bound
`retTy/εb/argTy < lvl'` to `< lvl' + o`, and preserves the `var`/`builtin` args condition
(`raiseScheme_U` raises `.level` in lock-step with the raised args). No extra hypothesis needed. -/
theorem closDisc_fullRaise {t o : Nat} (ht : 1 ≤ t)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    {h : HasType lvl Γ e τ ε} (hcd : ClosDisc h) :
    t ≤ lvl →
    ∃ h' : HasType (lvl + o) (raiseCtx_U t o Γ) e (Ty.raiseTy t o τ) (Ty.raiseTy t o ε),
      ClosDisc h' := by
  induction hcd with
  | @var lvl Γ x s args ε a hl hargs =>
      intro htlvl
      have hargs' : ∀ t' ∈ args.map (Ty.raiseTy t o), ∀ l ∈ t'.levels,
          l = 0 ∨ (raiseScheme_U t o s).level ≤ l := by
        intro t' ht' l hl'
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        rw [Ty.levels_raiseTy, List.mem_map] at hl'
        obtain ⟨l0, hl0mem, rfl⟩ := hl'
        rcases hargs t0 ht0 l0 hl0mem with h0 | hsle
        · subst h0; left; simp only [if_neg (show ¬ t ≤ 0 by omega)]
        · right; simp only [raiseScheme_U]; split <;> split <;> omega
      rw [← instantiateV_raiseScheme_U t o s args]
      exact ⟨HasType.var (raiseCtx_U_lookup hl), ClosDisc.var (raiseCtx_U_lookup hl) hargs'⟩
  | @builtin lvl Γ id s args ε a hs hargs =>
      intro htlvl
      have hclosed : raiseScheme_U t o s = s := by
        refine Scheme.ext' rfl ?_ ?_
        · simp only [raiseScheme_U, Builtins.scheme_level hs, if_neg (by omega : ¬ t ≤ 0)]
        · simp only [raiseScheme_U]
          exact Ty.raiseTy_eq_self_of_levels_lt
            (fun l hl => by rw [Builtins.scheme_levels_zero hs l hl]; omega)
      rw [← instantiateV_raiseScheme_U t o s args, hclosed]
      exact ⟨HasType.builtin hs, ClosDisc.builtin hs
        (fun t' _ l _ => Or.inr (by rw [Builtins.scheme_level hs]; exact Nat.zero_le l))⟩
  | @lam lvl lvl' Γ x body argTy εb retTy ε a hle hfv hret hεb hbody cdbody ih =>
      intro htlvl
      have hfv' : ∀ l ∈ (Ty.raiseTy t o argTy).levels, l < lvl' + o := by
        intro l hl; rw [Ty.levels_raiseTy, List.mem_map] at hl
        obtain ⟨l0, hl0, rfl⟩ := hl; have := hfv l0 hl0; split <;> omega
      have hret' : ∀ l ∈ (Ty.raiseTy t o retTy).levels, l < lvl' + o := by
        intro l hl; rw [Ty.levels_raiseTy, List.mem_map] at hl
        obtain ⟨l0, hl0, rfl⟩ := hl; have := hret l0 hl0; split <;> omega
      have hεb' : ∀ l ∈ (Ty.raiseTy t o εb).levels, l < lvl' + o := by
        intro l hl; rw [Ty.levels_raiseTy, List.mem_map] at hl
        obtain ⟨l0, hl0, rfl⟩ := hl; have := hεb l0 hl0; split <;> omega
      obtain ⟨hb, cdb⟩ := ih (le_trans htlvl hle)
      simp only [raiseCtx_U_cons, raiseScheme_U_mono ht] at hb cdb
      simp only [Ty.raiseTy]
      exact ⟨HasType.lam (lvl' := lvl' + o) (by omega) hfv' hb,
        ClosDisc.lam (by omega) hfv' hret' hεb' cdb⟩
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg cdf cdarg ihf iharg =>
      intro htlvl
      obtain ⟨hf', cdf'⟩ := ihf htlvl
      obtain ⟨harg', cdarg'⟩ := iharg htlvl
      simp only [Ty.raiseTy] at hf'
      exact ⟨HasType.app hf' (Ty.raiseTy_effWeaken t o hw) harg',
        ClosDisc.app (hw := Ty.raiseTy_effWeaken t o hw) cdf' cdarg'⟩
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody cdd cdb ihd ihb =>
      intro htlvl
      have hfv' : ∀ l ∈ (Ty.raiseTy t o defnTy).levels, l < lvl' + o := by
        intro l hl; rw [Ty.levels_raiseTy, List.mem_map] at hl
        obtain ⟨l0, hl0, rfl⟩ := hl; have := hfv l0 hl0; split <;> omega
      obtain ⟨hd', cdd'⟩ := ihd htlvl
      obtain ⟨hb, cdb'⟩ := ihb (le_trans htlvl hle)
      simp only [raiseCtx_U_cons, raiseScheme_U_mono ht] at hb cdb'
      exact ⟨HasType.let_ hd' (by omega) hfv' hb, ClosDisc.let_ (by omega) hfv' cdd' cdb'⟩
  | @let_poly lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a hstrict hfv hret hεb hbodydefn
      hcw hbody cddefn cdbody ihdefn ihbody =>
      intro htlvl
      have hfv' : ∀ l ∈ (Ty.raiseTy t o argTy).levels, l < lvl' + o := by
        intro l hl; rw [Ty.levels_raiseTy, List.mem_map] at hl
        obtain ⟨l0, hl0, rfl⟩ := hl; have := hfv l0 hl0; split <;> omega
      have hret' : ∀ l ∈ (Ty.raiseTy t o retTy).levels, l < lvl' + o := by
        intro l hl; rw [Ty.levels_raiseTy, List.mem_map] at hl
        obtain ⟨l0, hl0, rfl⟩ := hl; have := hret l0 hl0; split <;> omega
      have hεb' : ∀ l ∈ (Ty.raiseTy t o εb).levels, l < lvl' + o := by
        intro l hl; rw [Ty.levels_raiseTy, List.mem_map] at hl
        obtain ⟨l0, hl0, rfl⟩ := hl; have := hεb l0 hl0; split <;> omega
      obtain ⟨hbd, cdbd⟩ := ihdefn (by omega : t ≤ lvl')
      simp only [raiseCtx_U_cons, raiseScheme_U_mono ht] at hbd cdbd
      obtain ⟨hb, cdb⟩ := ihbody (by omega : t ≤ lvl + 1)
      simp only [raiseCtx_U_cons, raiseScheme_U_genAtV htlvl, Ty.raiseTy,
        show lvl + 1 + o = lvl + o + 1 from by omega] at hb cdb
      refine ⟨HasType.let_poly (a := a) (by omega : lvl + o < lvl' + o) hfv' hbd
          (ctxWfV_raiseCtx_U hcw) hb,
        ClosDisc.let_poly (by omega : lvl + o < lvl' + o) hfv' hret' hεb'
          (hcw := ctxWfV_raiseCtx_U hcw) cdbd cdb⟩
  | int => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.int, ClosDisc.int⟩
  | str => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.str, ClosDisc.str⟩
  | bin => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.bin, ClosDisc.bin⟩
  | tail => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.tail, ClosDisc.tail⟩
  | cons => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.cons, ClosDisc.cons⟩
  | tag => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.tag, ClosDisc.tag⟩
  | nocases => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.nocases, ClosDisc.nocases⟩
  | case_ => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.case_, ClosDisc.case_⟩
  | select => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.select, ClosDisc.select⟩
  | extend => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.extend, ClosDisc.extend⟩
  | overwrite => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.overwrite, ClosDisc.overwrite⟩
  | empty => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.empty, ClosDisc.empty⟩
  | perform => intro _; simp only [Ty.raiseTy]; exact ⟨HasType.perform, ClosDisc.perform⟩
  | @handle lvl Γ l lift reply tail ret ε a =>
      intro _
      have heq : Ty.raiseTy t o (handleTy l lift reply tail ret)
          = handleTy l (Ty.raiseTy t o lift) (Ty.raiseTy t o reply) (Ty.raiseTy t o tail)
              (Ty.raiseTy t o ret) := by
        simp [handleTy, handlerTy, execTy, kontTy, Ty.raiseTy]
      rw [heq]; exact ⟨HasType.handle, ClosDisc.handle⟩
  | @conv lvl Γ e τ τ' ε ε' hh hτ hε cdh ih =>
      intro htlvl
      obtain ⟨h', cdh'⟩ := ih htlvl
      exact ⟨HasType.conv h' (Ty.raiseTy_tyEquiv t o hτ) (Ty.raiseTy_tyEquiv t o hε),
        ClosDisc.conv (Ty.raiseTy_tyEquiv t o hτ) (Ty.raiseTy_tyEquiv t o hε) cdh'⟩

end Eyg.Types
