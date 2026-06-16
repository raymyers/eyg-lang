import Eyg.Types.Typing
import Eyg.Types.TyEquivInv

/-!
# Generation (inversion) lemmas for `HasType` (Milestone T3c-ii support)

Because `HasType` carries a `conv` rule, a derivation `HasType Γ ⟨e,a⟩ τ ε` need
not end in the syntactic rule for `e` — it may end in `conv`. The **generation
lemmas** invert each syntactic form *up to* `TyEquiv`, folding any trailing
conversions into the recovered components. They are the inputs to the `tau`-case
of preservation: each reads the typing of the control expression into the pieces
the reduction produces.

`HasType` is a plain (non-mutual) inductive, so these go by `induction h`, with
the node fixed via `generalize`; the `conv` case threads the IH through `trans`
(and, for `app`, retypes the sub-derivations at the outer `(τ, ε)` since `conv`
may also have moved the effect row).
-/

namespace Eyg.Types

open Eyg.Ir

variable {m : Type}

theorem inv_int {Γ : Ctx} {n : Int} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Integer n, a⟩ : Tree.Node m) τ ε) : Ty.TyEquiv .integer τ := by
  generalize he : (⟨.Integer n, a⟩ : Tree.Node m) = e at h
  induction h with
  | int => exact .refl _
  | conv _ hτ _ ih => exact (ih he).trans hτ
  | _ => simp at he

theorem inv_str {Γ : Ctx} {s : String} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.String s, a⟩ : Tree.Node m) τ ε) : Ty.TyEquiv .string τ := by
  generalize he : (⟨.String s, a⟩ : Tree.Node m) = e at h
  induction h with
  | str => exact .refl _
  | conv _ hτ _ ih => exact (ih he).trans hτ
  | _ => simp at he

theorem inv_bin {Γ : Ctx} {b : ByteArray} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Binary b, a⟩ : Tree.Node m) τ ε) : Ty.TyEquiv .binary τ := by
  generalize he : (⟨.Binary b, a⟩ : Tree.Node m) = e at h
  induction h with
  | bin => exact .refl _
  | conv _ hτ _ ih => exact (ih he).trans hτ
  | _ => simp at he

theorem inv_var {Γ : Ctx} {x : String} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Variable x, a⟩ : Tree.Node m) τ ε) :
    ∃ s args, Γ.lookup x = some s ∧ Ty.TyEquiv (s.instantiate args) τ := by
  generalize he : (⟨.Variable x, a⟩ : Tree.Node m) = e at h
  induction h with
  | @var Γ x' s args ε a hl =>
      cases he; exact ⟨s, args, hl, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨s, args, hl, heq⟩ := ih he; exact ⟨s, args, hl, heq.trans hτ⟩
  | _ => simp at he

theorem inv_builtin {Γ : Ctx} {id : String} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Builtin id, a⟩ : Tree.Node m) τ ε) :
    ∃ s args, Builtins.scheme id = some s ∧ Ty.TyEquiv (s.instantiate args) τ := by
  generalize he : (⟨.Builtin id, a⟩ : Tree.Node m) = e at h
  induction h with
  | @builtin Γ id' s args ε a hs =>
      cases he; exact ⟨s, args, hs, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨s, args, hs, heq⟩ := ih he; exact ⟨s, args, hs, heq.trans hτ⟩
  | _ => simp at he

theorem inv_lambda {Γ : Ctx} {x : String} {body : Tree.Node m} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Lambda x body, a⟩ : Tree.Node m) τ ε) :
    ∃ argTy εb retTy, HasType ((x, .mono argTy) :: Γ) body retTy εb ∧
      Ty.TyEquiv (.fun argTy εb retTy) τ := by
  generalize he : (⟨.Lambda x body, a⟩ : Tree.Node m) = e at h
  induction h with
  | @lam Γ x' body' argTy εb retTy ε a hbody =>
      cases he; exact ⟨argTy, εb, retTy, hbody, .refl _⟩
  | conv _ hτ _ ih =>
      obtain ⟨argTy, εb, retTy, hbody, heq⟩ := ih he
      exact ⟨argTy, εb, retTy, hbody, heq.trans hτ⟩
  | _ => simp at he

theorem inv_let {Γ : Ctx} {x : String} {defn body : Tree.Node m} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Let x defn body, a⟩ : Tree.Node m) τ ε) :
    ∃ defnTy, HasType Γ defn defnTy ε ∧ HasType ((x, .mono defnTy) :: Γ) body τ ε := by
  generalize he : (⟨.Let x defn body, a⟩ : Tree.Node m) = e at h
  induction h with
  | @let_ Γ x' defn' body' defnTy bodyTy ε a hdefn hbody =>
      cases he; exact ⟨defnTy, hdefn, hbody⟩
  | conv hinner hτ hε ih =>
      obtain ⟨defnTy, hdefn, hbody⟩ := ih he
      -- retype both sub-derivations at the outer (τ, ε)
      exact ⟨defnTy, HasType.conv hdefn (.refl _) hε,
        HasType.conv hbody hτ hε⟩
  | _ => simp at he

theorem inv_app {Γ : Ctx} {f arg : Tree.Node m} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Apply f arg, a⟩ : Tree.Node m) τ ε) :
    ∃ argTy, HasType Γ f (.fun argTy ε τ) ε ∧ HasType Γ arg argTy ε := by
  generalize he : (⟨.Apply f arg, a⟩ : Tree.Node m) = e at h
  induction h with
  | @app Γ f' arg' argTy retTy ε a hf harg =>
      cases he; exact ⟨argTy, hf, harg⟩
  | conv hinner hτ hε ih =>
      obtain ⟨argTy, hf, harg⟩ := ih he
      refine ⟨argTy, ?_, ?_⟩
      · exact HasType.conv hf (.congrFun (.refl _) hε hτ) hε
      · exact HasType.conv harg (.refl _) hε
  | _ => simp at he

end Eyg.Types
