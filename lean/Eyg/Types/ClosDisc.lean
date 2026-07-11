import Eyg.Types.Typing

/-!
# `ClosDisc` — the closure-discipline entry predicate (G2 Phase 3 home)

The front-door restriction on `soundness`'s entry derivation (Phase-0 sign-off): a derivation is
**closure-disciplined** when every lambda's `retTy`/`εb` sit strictly below its sublevel `lvl'` (the
CLOSING case the universal readiness lemma discharges), and every `var`/`builtin` instantiation's arg
levels satisfy the Γ-free `l = 0 ∨ s.level ≤ l` (the Rémy-inference shape — a scheme is instantiated at
fresh vars at the current level `≥ s.level`, or at generalized-away `0`).

`ClosDisc` is defined here — depending only on `HasType` (`Typing.lean`) — so that `Runtime.lean` can
import it and store it on `HasTypeV.closure`. Unlike `HasTypeRT`, it **recurses into lambda/defn
bodies** (it is a *static*, whole-derivation property), so the stored field is consumed as-is at apply
time. The readiness lemmas that consume it live downstream (they need `HasTypeV` + the `genAtV`
keystones); see `G2DiscSpike.lean` (spike) pending their promotion.
-/

namespace Eyg.Types

open Eyg.Ir

variable {m : Type}

/-- **Closure discipline** (indexed by a `HasType` derivation, `NoGenAt`-shaped). `lam`/`let_poly`
arms record `retTy.levels < lvl' ∧ εb.levels < lvl'` (the CLOSING case; `argTy < lvl'` is already
forced by the rule). `var`/`builtin` arms record the Γ-free arg condition `l = 0 ∨ s.level ≤ l`.
Recurses into **all** sub-derivations, including lambda bodies (static, storable). -/
inductive ClosDisc {m : Type} :
    {lvl : Nat} → {Γ : Ctx} → {e : Tree.Node m} → {τ ε : Ty} →
    HasType lvl Γ e τ ε → Prop where
  | var {lvl Γ x s args ε a} (hl : Γ.lookup x = some s)
      (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ s.level ≤ l) :
      ClosDisc (HasType.var (lvl := lvl) (Γ := Γ) (x := x) (s := s) (args := args)
        (ε := ε) (a := a) hl)
  | lam {lvl lvl' Γ x body argTy εb retTy ε a}
      (hle : lvl ≤ lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      (hret : ∀ l ∈ retTy.levels, l < lvl') (hεb : ∀ l ∈ εb.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb} :
      ClosDisc hbody → ClosDisc (HasType.lam (ε := ε) (a := a) hle hfv hbody)
  | app {lvl Γ f arg argTy εf retTy ε a}
      {hf : HasType lvl Γ f (.fun argTy εf retTy) ε} {hw : Ty.EffWeaken εf ε}
      {harg : HasType lvl Γ arg argTy ε} :
      ClosDisc hf → ClosDisc harg → ClosDisc (HasType.app (a := a) hf hw harg)
  | let_ {lvl lvl' Γ x defn body defnTy bodyTy ε a}
      {hdefn : HasType lvl Γ defn defnTy ε} (hle : lvl ≤ lvl')
      (hfv : ∀ l ∈ defnTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono defnTy) :: Γ) body bodyTy ε} :
      ClosDisc hdefn → ClosDisc hbody →
      ClosDisc (HasType.let_ (a := a) hdefn hle hfv hbody)
  | let_poly {lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a}
      (hstrict : lvl < lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      (hret : ∀ l ∈ retTy.levels, l < lvl') (hεb : ∀ l ∈ εb.levels, l < lvl')
      {hbodydefn : HasType lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb} {hcw : CtxWfV lvl Γ}
      {hbody : HasType (lvl + 1)
        ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body bodyTy ε} :
      ClosDisc hbodydefn → ClosDisc hbody →
      ClosDisc (HasType.let_poly (a := a) (la := la) hstrict hfv hbodydefn hcw hbody)
  | int {lvl Γ n ε a} :
      ClosDisc (HasType.int (m := m) (lvl := lvl) (Γ := Γ) (n := n) (ε := ε) (a := a))
  | str {lvl Γ s ε a} :
      ClosDisc (HasType.str (m := m) (lvl := lvl) (Γ := Γ) (s := s) (ε := ε) (a := a))
  | bin {lvl Γ b ε a} :
      ClosDisc (HasType.bin (m := m) (lvl := lvl) (Γ := Γ) (b := b) (ε := ε) (a := a))
  | builtin {lvl Γ id s args ε a} (hs : Builtins.scheme id = some s)
      (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ s.level ≤ l) :
      ClosDisc (HasType.builtin (lvl := lvl) (Γ := Γ) (args := args) (ε := ε) (a := a) hs)
  | tail {lvl Γ elem ε a} :
      ClosDisc (HasType.tail (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | cons {lvl Γ elem ε a} :
      ClosDisc (HasType.cons (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | tag {lvl Γ l elem tail ε a} :
      ClosDisc (HasType.tag (m := m) (lvl := lvl) (Γ := Γ) (l := l) (elem := elem)
        (tail := tail) (ε := ε) (a := a))
  | nocases {lvl Γ ret ε a} :
      ClosDisc (HasType.nocases (m := m) (lvl := lvl) (Γ := Γ) (ret := ret) (ε := ε) (a := a))
  | case_ {lvl Γ l inner eff ret tail ε a} :
      ClosDisc (HasType.case_ (m := m) (lvl := lvl) (Γ := Γ) (l := l) (inner := inner)
        (eff := eff) (ret := ret) (tail := tail) (ε := ε) (a := a))
  | select {lvl Γ l fieldTy tail ε a} :
      ClosDisc (HasType.select (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (tail := tail) (ε := ε) (a := a))
  | extend {lvl Γ l fieldTy row ε a} :
      ClosDisc (HasType.extend (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (row := row) (ε := ε) (a := a))
  | overwrite {lvl Γ l newTy oldTy tail ε a} :
      ClosDisc (HasType.overwrite (m := m) (lvl := lvl) (Γ := Γ) (l := l) (newTy := newTy)
        (oldTy := oldTy) (tail := tail) (ε := ε) (a := a))
  | empty {lvl Γ ε a} :
      ClosDisc (HasType.empty (m := m) (lvl := lvl) (Γ := Γ) (ε := ε) (a := a))
  | perform {lvl Γ l aa b μ ε ann} :
      ClosDisc (HasType.perform (m := m) (lvl := lvl) (Γ := Γ) (l := l) (a := aa) (b := b)
        (μ := μ) (ε := ε) (ann := ann))
  | handle {lvl Γ l lift reply tail ret ε ann} :
      ClosDisc (HasType.handle (m := m) (lvl := lvl) (Γ := Γ) (l := l) (lift := lift)
        (reply := reply) (tail := tail) (ret := ret) (ε := ε) (ann := ann))
  | conv {lvl Γ e τ τ' ε ε'} {h : HasType lvl Γ e τ ε}
      (hτ : Ty.TyEquiv τ τ') (hε : Ty.TyEquiv ε ε') :
      ClosDisc h → ClosDisc (HasType.conv h hτ hε)

/-- **`ClosDisc`-indexed context-binding conversion** (the `ClosDisc` companion to
`hasTypeRT_ctxConv`). Unlike `HasTypeRT`, `ClosDisc` recurses into lambda/defn bodies, so the
`lam`/`let_poly` arms rebuild the body's `ClosDisc` from the induction hypothesis rather than
re-deriving a plain `HasType`. Consumed by `stackSeg_conv_input` (via `closDisc_ctxHead_conv`). -/
theorem closDisc_ctxConv {m : Type} {lvl : Nat} {Γ₀ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    {h : HasType lvl Γ₀ e τ ε} (hcd : ClosDisc h) :
    ∀ (Δ Γ : Ctx) (x : String) (σ σ' : Ty),
      Γ₀ = Δ ++ (x, .mono σ) :: Γ → Ty.TyEquiv σ' σ →
      ∃ h' : HasType lvl (Δ ++ (x, .mono σ') :: Γ) e τ ε, ClosDisc h' := by
  induction hcd with
  | @var lvl Γ₁ y s args ε' a hl hargs =>
      intro Δ Γ x σ σ' heq hc; subst heq
      rw [List.lookup_append] at hl
      cases hΔ : Δ.lookup y with
      | some v =>
          rw [hΔ, Option.some_or] at hl; cases hl
          exact ⟨HasType.var (by rw [List.lookup_append, hΔ, Option.some_or]),
            ClosDisc.var (by rw [List.lookup_append, hΔ, Option.some_or]) hargs⟩
      | none =>
          rw [hΔ, Option.none_or] at hl
          by_cases hyx : (y == x) = true
          · simp only [List.lookup_cons, hyx] at hl; cases hl
            refine ⟨HasType.conv
              (HasType.var (s := .mono σ') (args := args)
                (by simp only [List.lookup_append, hΔ, Option.none_or, List.lookup_cons, hyx]))
              ?_ (.refl _), ClosDisc.conv ?_ (.refl _)
                (ClosDisc.var (s := .mono σ') (args := args)
                  (by simp only [List.lookup_append, hΔ, Option.none_or, List.lookup_cons, hyx])
                  hargs)⟩
            · simp only [Scheme.instantiateV_mono]; exact hc
            · simp only [Scheme.instantiateV_mono]; exact hc
          · simp only [List.lookup_cons, hyx] at hl ⊢
            exact ⟨HasType.var (s := s) (args := args)
                (by simp only [List.lookup_append, hΔ, Option.none_or, List.lookup_cons, hyx]; exact hl),
              ClosDisc.var (s := s) (args := args)
                (by simp only [List.lookup_append, hΔ, Option.none_or, List.lookup_cons, hyx]; exact hl) hargs⟩
  | @lam lvl lvl' Γ₁ z body argTy εb retTy ε' a hle hfv hret hεb hbody cdbody ih =>
      intro Δ Γ x σ σ' heq hc; subst heq
      obtain ⟨hb', cdb'⟩ := ih ((z, .mono argTy) :: Δ) Γ x σ σ' rfl hc
      exact ⟨HasType.lam hle hfv hb', ClosDisc.lam hle hfv hret hεb cdb'⟩
  | @app lvl Γ₁ f arg argTy εf retTy ε' a hf hw harg cdf cdarg ihf iharg =>
      intro Δ Γ x σ σ' heq hc; subst heq
      obtain ⟨hf', cdf'⟩ := ihf Δ Γ x σ σ' rfl hc
      obtain ⟨harg', cdarg'⟩ := iharg Δ Γ x σ σ' rfl hc
      exact ⟨HasType.app hf' hw harg', ClosDisc.app (hw := hw) cdf' cdarg'⟩
  | @let_ lvl lvl' Γ₁ z defn body defnTy bodyTy ε' a hdefn hle hfv hbody cdd cdb ihd ihb =>
      intro Δ Γ x σ σ' heq hc; subst heq
      obtain ⟨hd', cdd'⟩ := ihd Δ Γ x σ σ' rfl hc
      obtain ⟨hb', cdb'⟩ := ihb ((z, .mono defnTy) :: Δ) Γ x σ σ' rfl hc
      exact ⟨HasType.let_ hd' hle hfv hb', ClosDisc.let_ hle hfv cdd' cdb'⟩
  | @let_poly lvl lvl' Γ₁ z lx lbody la body argTy εb retTy bodyTy ε' a hstrict hfv hret hεb
      hbodydefn hcw hbody cddefn cdbody ihdefn ihbody =>
      intro Δ Γ x σ σ' heq hc; subst heq
      obtain ⟨hbd', cdbd'⟩ := ihdefn ((lx, Scheme.mono argTy) :: Δ) Γ x σ σ' rfl hc
      obtain ⟨hb', cdb'⟩ :=
        ihbody ((z, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Δ) Γ x σ σ' rfl hc
      have hcw' := ctxWfV_ctxConv hc hcw
      exact ⟨HasType.let_poly hstrict hfv hbd' hcw' hb',
        ClosDisc.let_poly hstrict hfv hret hεb (hcw := hcw') cdbd' cdb'⟩
  | int => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.int, ClosDisc.int⟩
  | str => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.str, ClosDisc.str⟩
  | bin => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.bin, ClosDisc.bin⟩
  | builtin hs hargs =>
      intro Δ Γ x σ σ' heq hc; subst heq
      exact ⟨HasType.builtin hs, ClosDisc.builtin hs hargs⟩
  | tail => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.tail, ClosDisc.tail⟩
  | cons => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.cons, ClosDisc.cons⟩
  | tag => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.tag, ClosDisc.tag⟩
  | nocases =>
      intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.nocases, ClosDisc.nocases⟩
  | case_ => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.case_, ClosDisc.case_⟩
  | select => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.select, ClosDisc.select⟩
  | extend => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.extend, ClosDisc.extend⟩
  | overwrite =>
      intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.overwrite, ClosDisc.overwrite⟩
  | empty => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.empty, ClosDisc.empty⟩
  | perform =>
      intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.perform, ClosDisc.perform⟩
  | handle => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.handle, ClosDisc.handle⟩
  | @conv lvl Γ₁ e' τ' τ'' ε₁ ε₂ hh hτ hε cdh ih =>
      intro Δ Γ x σ σ' heq hc; subst heq
      obtain ⟨h'', cdh''⟩ := ih Δ Γ x σ σ' rfl hc
      exact ⟨HasType.conv h'' hτ hε, ClosDisc.conv hτ hε cdh''⟩

/-- The head-binding (`Δ = []`) specialization of `closDisc_ctxConv`, the form `stackSeg_conv_input`
uses. -/
theorem closDisc_ctxHead_conv {m : Type} {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {x : String}
    {σ σ' τ ε : Ty} {h : HasType lvl ((x, .mono σ) :: Γ) e τ ε} (hcd : ClosDisc h)
    (hc : Ty.TyEquiv σ' σ) :
    ∃ h' : HasType lvl ((x, .mono σ') :: Γ) e τ ε, ClosDisc h' :=
  closDisc_ctxConv hcd [] Γ x σ σ' rfl hc

end Eyg.Types
