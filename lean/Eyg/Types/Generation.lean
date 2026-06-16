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

/-- **Typeable nodes are exactly the pure-core forms.** A well-typed node's
expression is one of the eight rules' shapes — used to discharge the untypeable
`reduceEval` arms (`Vacant`, `Tail`, `Cons`, `Select`, …) in the preservation
`tau` split. Grows as later slices add rules. -/
theorem hasType_expr_form {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    (h : HasType Γ e τ ε) :
    (∃ x, e.expr = .Variable x) ∨ (∃ x b, e.expr = .Lambda x b) ∨
    (∃ f arg, e.expr = .Apply f arg) ∨ (∃ x d b, e.expr = .Let x d b) ∨
    (∃ n, e.expr = .Integer n) ∨ (∃ s, e.expr = .String s) ∨
    (∃ b, e.expr = .Binary b) ∨ (∃ id, e.expr = .Builtin id) ∨
    e.expr = .Tail ∨ e.expr = .Empty ∨ e.expr = .Cons ∨ (∃ l, e.expr = .Tag l) ∨
    e.expr = .NoCases ∨ (∃ l, e.expr = .Case l) := by
  induction h with
  | var => exact Or.inl ⟨_, rfl⟩
  | lam => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  | app => exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  | let_ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  | int => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
  | str => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  | bin => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))
  | builtin => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))))
  | tail => iterate 8 apply Or.inr
            exact Or.inl rfl
  | empty => iterate 9 apply Or.inr
             exact Or.inl rfl
  | cons => iterate 10 apply Or.inr
            exact Or.inl rfl
  | tag => iterate 11 apply Or.inr
           exact Or.inl ⟨_, rfl⟩
  | nocases => iterate 12 apply Or.inr
               exact Or.inl rfl
  | case_ => iterate 13 apply Or.inr
             exact ⟨_, rfl⟩
  | conv _ _ _ ih => exact ih

/-- Inversion for `Tail`: a type equivalent to some list type. -/
theorem inv_tail {Γ : Ctx} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Tail, a⟩ : Tree.Node m) τ ε) : ∃ elem, Ty.TyEquiv (.list elem) τ := by
  generalize he : (⟨.Tail, a⟩ : Tree.Node m) = e at h
  induction h with
  | tail => exact ⟨_, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨elem, heq⟩ := ih he; exact ⟨elem, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Empty`: a type equivalent to the empty record. -/
theorem inv_empty {Γ : Ctx} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Empty, a⟩ : Tree.Node m) τ ε) : Ty.TyEquiv (.record .empty) τ := by
  generalize he : (⟨.Empty, a⟩ : Tree.Node m) = e at h
  induction h with
  | empty => exact .refl _
  | conv _ hτ _ ih => exact (ih he).trans hτ
  | _ => simp at he

/-- Inversion for `Cons`: a type equivalent to some `α → List α → List α`. -/
theorem inv_cons {Γ : Ctx} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Cons, a⟩ : Tree.Node m) τ ε) :
    ∃ elem, Ty.TyEquiv (.fun elem .empty (.fun (.list elem) .empty (.list elem))) τ := by
  generalize he : (⟨.Cons, a⟩ : Tree.Node m) = e at h
  induction h with
  | cons => exact ⟨_, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨elem, heq⟩ := ih he; exact ⟨elem, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Tag l`: a type equivalent to some `α → ⟨l : α | r⟩`. -/
theorem inv_tag {Γ : Ctx} {l : String} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Tag l, a⟩ : Tree.Node m) τ ε) :
    ∃ elem tail, Ty.TyEquiv (.fun elem .empty (.union (.rowExtend l elem tail))) τ := by
  generalize he : (⟨.Tag l, a⟩ : Tree.Node m) = e at h
  induction h with
  | tag => cases he; exact ⟨_, _, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨elem, tail, heq⟩ := ih he; exact ⟨elem, tail, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `NoCases`: a type equivalent to some `⟨⟩ → β`. -/
theorem inv_nocases {Γ : Ctx} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.NoCases, a⟩ : Tree.Node m) τ ε) :
    ∃ ret, Ty.TyEquiv (.fun (.union .empty) .empty ret) τ := by
  generalize he : (⟨.NoCases, a⟩ : Tree.Node m) = e at h
  induction h with
  | nocases => exact ⟨_, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨ret, heq⟩ := ih he; exact ⟨ret, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Case l`: a type equivalent to the full match scheme. -/
theorem inv_case {Γ : Ctx} {l : String} {a : m} {τ ε : Ty}
    (h : HasType Γ (⟨.Case l, a⟩ : Tree.Node m) τ ε) :
    ∃ inner eff ret tail, Ty.TyEquiv (.fun (.fun inner eff ret) .empty
      (.fun (.fun (.union tail) eff ret) .empty
        (.fun (.union (.rowExtend l inner tail)) eff ret))) τ := by
  generalize he : (⟨.Case l, a⟩ : Tree.Node m) = e at h
  induction h with
  | case_ => cases he; exact ⟨_, _, _, _, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨i, e', r, t, heq⟩ := ih he; exact ⟨i, e', r, t, heq.trans hτ⟩
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
