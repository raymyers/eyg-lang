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

end Eyg.Types
