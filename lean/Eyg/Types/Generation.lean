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

theorem inv_int {lvl : Nat} {Γ : Ctx} {n : Int} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Integer n, a⟩ : Tree.Node m) τ ε) : Ty.TyEquiv .integer τ := by
  generalize he : (⟨.Integer n, a⟩ : Tree.Node m) = e at h
  induction h with
  | int => exact .refl _
  | conv _ hτ _ ih => exact (ih he).trans hτ
  | _ => simp at he

theorem inv_str {lvl : Nat} {Γ : Ctx} {s : String} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.String s, a⟩ : Tree.Node m) τ ε) : Ty.TyEquiv .string τ := by
  generalize he : (⟨.String s, a⟩ : Tree.Node m) = e at h
  induction h with
  | str => exact .refl _
  | conv _ hτ _ ih => exact (ih he).trans hτ
  | _ => simp at he

theorem inv_bin {lvl : Nat} {Γ : Ctx} {b : ByteArray} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Binary b, a⟩ : Tree.Node m) τ ε) : Ty.TyEquiv .binary τ := by
  generalize he : (⟨.Binary b, a⟩ : Tree.Node m) = e at h
  induction h with
  | bin => exact .refl _
  | conv _ hτ _ ih => exact (ih he).trans hτ
  | _ => simp at he

theorem inv_var {lvl : Nat} {Γ : Ctx} {x : String} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Variable x, a⟩ : Tree.Node m) τ ε) :
    ∃ s args, Γ.lookup x = some s ∧ Ty.TyEquiv (s.instantiateV args) τ := by
  generalize he : (⟨.Variable x, a⟩ : Tree.Node m) = e at h
  induction h with
  | @var lvl Γ x' s args ε a hl =>
      cases he; exact ⟨s, args, hl, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨s, args, hl, heq⟩ := ih he; exact ⟨s, args, hl, heq.trans hτ⟩
  | _ => simp at he

theorem inv_builtin {lvl : Nat} {Γ : Ctx} {id : String} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Builtin id, a⟩ : Tree.Node m) τ ε) :
    ∃ s args, Builtins.scheme id = some s ∧ Ty.TyEquiv (s.instantiateV args) τ := by
  generalize he : (⟨.Builtin id, a⟩ : Tree.Node m) = e at h
  induction h with
  | @builtin lvl Γ id' s args ε a hs =>
      cases he; exact ⟨s, args, hs, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨s, args, hs, heq⟩ := ih he; exact ⟨s, args, hs, heq.trans hτ⟩
  | _ => simp at he

theorem inv_lambda {lvl : Nat} {Γ : Ctx} {x : String} {body : Tree.Node m} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Lambda x body, a⟩ : Tree.Node m) τ ε) :
    ∃ lvl' argTy εb retTy, lvl ≤ lvl' ∧ (∀ l ∈ argTy.levels, l < lvl') ∧
      HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb ∧
      Ty.TyEquiv (.fun argTy εb retTy) τ := by
  generalize he : (⟨.Lambda x body, a⟩ : Tree.Node m) = e at h
  induction h with
  | @lam lvl lvl' Γ x' body' argTy εb retTy ε a hle hfv hbody =>
      cases he; exact ⟨lvl', argTy, εb, retTy, hle, hfv, hbody, .refl _⟩
  | conv _ hτ _ ih =>
      obtain ⟨lvl', argTy, εb, retTy, hle, hfv, hbody, heq⟩ := ih he
      exact ⟨lvl', argTy, εb, retTy, hle, hfv, hbody, heq.trans hτ⟩
  | _ => simp at he

/-- **Inversion for `Let`** (unified mono/poly, level-native). Either the binding is monomorphic (body
typed at `.mono defnTy` at a stored sublevel `lvl'`) or polymorphic (value-restricted: `defn` is a
`Lambda`; body typed at the level-native generalization `genAtV lvl defnTy`, with `CtxWfV lvl Γ`, at
level `lvl + 1`; **no `noLambdaLet`**). The two engines' Let-push split on this. -/
theorem inv_let {lvl : Nat} {Γ : Ctx} {x : String} {defn body : Tree.Node m} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Let x defn body, a⟩ : Tree.Node m) τ ε) :
    (∃ lvl' defnTy, HasType lvl Γ defn defnTy ε ∧ lvl ≤ lvl' ∧
        (∀ l ∈ defnTy.levels, l < lvl') ∧ HasType lvl' ((x, .mono defnTy) :: Γ) body τ ε) ∨
    (∃ lx lbody la defnTy, defn = ⟨.Lambda lx lbody, la⟩ ∧
        HasType lvl Γ defn defnTy ε ∧ CtxWfV lvl Γ ∧
        HasType (lvl + 1) ((x, Scheme.genAtV lvl defnTy) :: Γ) body τ ε) := by
  generalize he : (⟨.Let x defn body, a⟩ : Tree.Node m) = e at h
  induction h with
  | @let_ lvl lvl' Γ x' defn' body' defnTy bodyTy ε a hdefn hle hfv hbody =>
      cases he; exact Or.inl ⟨lvl', defnTy, hdefn, hle, hfv, hbody⟩
  | @let_poly lvl Γ x' lx lbody la body' defnTy bodyTy ε a hdefn hcw hbody =>
      cases he; exact Or.inr ⟨lx, lbody, la, defnTy, rfl, hdefn, hcw, hbody⟩
  | conv hinner hτ hε ih =>
      rcases ih he with ⟨lvl', defnTy, hdefn, hle, hfv, hbody⟩ |
          ⟨lx, lbody, la, defnTy, hdl, hdefn, hcw, hbody⟩
      · exact Or.inl ⟨lvl', defnTy, HasType.conv hdefn (.refl _) hε, hle, hfv,
          HasType.conv hbody hτ hε⟩
      · exact Or.inr ⟨lx, lbody, la, defnTy, hdl, HasType.conv hdefn (.refl _) hε, hcw,
          HasType.conv hbody hτ hε⟩
  | _ => simp at he

/-- **Typeable nodes are exactly the pure-core forms.** A well-typed node's
expression is one of the eight rules' shapes — used to discharge the untypeable
`reduceEval` arms (`Vacant`, `Tail`, `Cons`, `Select`, …) in the preservation
`tau` split. Grows as later slices add rules. -/
theorem hasType_expr_form {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    (h : HasType lvl Γ e τ ε) :
    (∃ x, e.expr = .Variable x) ∨ (∃ x b, e.expr = .Lambda x b) ∨
    (∃ f arg, e.expr = .Apply f arg) ∨ (∃ x d b, e.expr = .Let x d b) ∨
    (∃ n, e.expr = .Integer n) ∨ (∃ s, e.expr = .String s) ∨
    (∃ b, e.expr = .Binary b) ∨ (∃ id, e.expr = .Builtin id) ∨
    e.expr = .Tail ∨ e.expr = .Empty ∨ e.expr = .Cons ∨ (∃ l, e.expr = .Tag l) ∨
    e.expr = .NoCases ∨ (∃ l, e.expr = .Case l) ∨ (∃ l, e.expr = .Select l) ∨
    (∃ l, e.expr = .Extend l) ∨ (∃ l, e.expr = .Overwrite l) ∨
    (∃ l, e.expr = .Perform l) ∨ (∃ l, e.expr = .Handle l) := by
  induction h with
  | var => exact Or.inl ⟨_, rfl⟩
  | lam => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  | app => exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  | let_ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  | let_poly => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
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
             exact Or.inl ⟨_, rfl⟩
  | select => iterate 14 apply Or.inr
              exact Or.inl ⟨_, rfl⟩
  | extend => iterate 15 apply Or.inr
              exact Or.inl ⟨_, rfl⟩
  | overwrite => iterate 16 apply Or.inr
                 exact Or.inl ⟨_, rfl⟩
  | perform => iterate 17 apply Or.inr
               exact Or.inl ⟨_, rfl⟩
  | handle => iterate 18 apply Or.inr
              exact ⟨_, rfl⟩
  | conv _ _ _ ih => exact ih

/-- Inversion for `Tail`: a type equivalent to some list type. -/
theorem inv_tail {lvl : Nat} {Γ : Ctx} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Tail, a⟩ : Tree.Node m) τ ε) : ∃ elem, Ty.TyEquiv (.list elem) τ := by
  generalize he : (⟨.Tail, a⟩ : Tree.Node m) = e at h
  induction h with
  | tail => exact ⟨_, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨elem, heq⟩ := ih he; exact ⟨elem, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Empty`: a type equivalent to the empty record. -/
theorem inv_empty {lvl : Nat} {Γ : Ctx} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Empty, a⟩ : Tree.Node m) τ ε) : Ty.TyEquiv (.record .empty) τ := by
  generalize he : (⟨.Empty, a⟩ : Tree.Node m) = e at h
  induction h with
  | empty => exact .refl _
  | conv _ hτ _ ih => exact (ih he).trans hτ
  | _ => simp at he

/-- Inversion for `Cons`: a type equivalent to some `α → List α → List α`. -/
theorem inv_cons {lvl : Nat} {Γ : Ctx} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Cons, a⟩ : Tree.Node m) τ ε) :
    ∃ elem, Ty.TyEquiv (.fun elem .empty (.fun (.list elem) .empty (.list elem))) τ := by
  generalize he : (⟨.Cons, a⟩ : Tree.Node m) = e at h
  induction h with
  | cons => exact ⟨_, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨elem, heq⟩ := ih he; exact ⟨elem, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Tag l`: a type equivalent to some `α → ⟨l : α | r⟩`. -/
theorem inv_tag {lvl : Nat} {Γ : Ctx} {l : String} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Tag l, a⟩ : Tree.Node m) τ ε) :
    ∃ elem tail, Ty.TyEquiv (.fun elem .empty (.union (.rowExtend l elem tail))) τ := by
  generalize he : (⟨.Tag l, a⟩ : Tree.Node m) = e at h
  induction h with
  | tag => cases he; exact ⟨_, _, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨elem, tail, heq⟩ := ih he; exact ⟨elem, tail, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `NoCases`: a type equivalent to some `⟨⟩ → β`. -/
theorem inv_nocases {lvl : Nat} {Γ : Ctx} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.NoCases, a⟩ : Tree.Node m) τ ε) :
    ∃ ret, Ty.TyEquiv (.fun (.union .empty) .empty ret) τ := by
  generalize he : (⟨.NoCases, a⟩ : Tree.Node m) = e at h
  induction h with
  | nocases => exact ⟨_, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨ret, heq⟩ := ih he; exact ⟨ret, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Case l`: a type equivalent to the full match scheme. -/
theorem inv_case {lvl : Nat} {Γ : Ctx} {l : String} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Case l, a⟩ : Tree.Node m) τ ε) :
    ∃ inner eff ret tail, Ty.TyEquiv (.fun (.fun inner eff ret) .empty
      (.fun (.fun (.union tail) eff ret) .empty
        (.fun (.union (.rowExtend l inner tail)) eff ret))) τ := by
  generalize he : (⟨.Case l, a⟩ : Tree.Node m) = e at h
  induction h with
  | case_ => cases he; exact ⟨_, _, _, _, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨i, e', r, t, heq⟩ := ih he; exact ⟨i, e', r, t, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Select l`: a type equivalent to `{l:α|r} → α`. -/
theorem inv_select {lvl : Nat} {Γ : Ctx} {l : String} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Select l, a⟩ : Tree.Node m) τ ε) :
    ∃ fieldTy tail, Ty.TyEquiv (.fun (.record (.rowExtend l fieldTy tail)) .empty fieldTy) τ := by
  generalize he : (⟨.Select l, a⟩ : Tree.Node m) = e at h
  induction h with
  | select => cases he; exact ⟨_, _, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨ft, t, heq⟩ := ih he; exact ⟨ft, t, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Extend l`: a type equivalent to `α → {r} → {l:α|r}`. -/
theorem inv_extend {lvl : Nat} {Γ : Ctx} {l : String} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Extend l, a⟩ : Tree.Node m) τ ε) :
    ∃ fieldTy row, Ty.TyEquiv (.fun fieldTy .empty
      (.fun (.record row) .empty (.record (.rowExtend l fieldTy row)))) τ := by
  generalize he : (⟨.Extend l, a⟩ : Tree.Node m) = e at h
  induction h with
  | extend => cases he; exact ⟨_, _, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨ft, r, heq⟩ := ih he; exact ⟨ft, r, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Overwrite l`: a type equivalent to `α → {l:β|r} → {l:α|r}`. -/
theorem inv_overwrite {lvl : Nat} {Γ : Ctx} {l : String} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Overwrite l, a⟩ : Tree.Node m) τ ε) :
    ∃ newTy oldTy tail, Ty.TyEquiv (.fun newTy .empty
      (.fun (.record (.rowExtend l oldTy tail)) .empty
        (.record (.rowExtend l newTy tail)))) τ := by
  generalize he : (⟨.Overwrite l, a⟩ : Tree.Node m) = e at h
  induction h with
  | overwrite => cases he; exact ⟨_, _, _, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨n, o, t, heq⟩ := ih he; exact ⟨n, o, t, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Perform l`: a type equivalent to `α →⟨l:(α,β)|μ⟩ β`. -/
theorem inv_perform {lvl : Nat} {Γ : Ctx} {l : String} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Perform l, a⟩ : Tree.Node m) τ ε) :
    ∃ argTy replyTy μ, Ty.TyEquiv (.fun argTy (.effectExtend l argTy replyTy μ) replyTy) τ := by
  generalize he : (⟨.Perform l, a⟩ : Tree.Node m) = e at h
  induction h with
  | perform => cases he; exact ⟨_, _, _, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨at_, rt, μ, heq⟩ := ih he; exact ⟨at_, rt, μ, heq.trans hτ⟩
  | _ => simp at he

/-- Inversion for `Handle l`: a type equivalent to `handleTy l lift reply tail ret`. -/
theorem inv_handle {lvl : Nat} {Γ : Ctx} {l : String} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Handle l, a⟩ : Tree.Node m) τ ε) :
    ∃ lift reply tail ret, Ty.TyEquiv (handleTy l lift reply tail ret) τ := by
  generalize he : (⟨.Handle l, a⟩ : Tree.Node m) = e at h
  induction h with
  | handle => cases he; exact ⟨_, _, _, _, .refl _⟩
  | conv _ hτ _ ih => obtain ⟨li, r, t, re, heq⟩ := ih he; exact ⟨li, r, t, re, heq.trans hτ⟩
  | _ => simp at he

theorem inv_app {lvl : Nat} {Γ : Ctx} {f arg : Tree.Node m} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Apply f arg, a⟩ : Tree.Node m) τ ε) :
    ∃ argTy εf, Ty.EffWeaken εf ε ∧ HasType lvl Γ f (.fun argTy εf τ) ε ∧
      HasType lvl Γ arg argTy ε := by
  generalize he : (⟨.Apply f arg, a⟩ : Tree.Node m) = e at h
  induction h with
  | @app lvl Γ f' arg' argTy εf retTy ε a hf hw harg =>
      cases he; exact ⟨argTy, εf, hw, hf, harg⟩
  | conv hinner hτ hε ih =>
      obtain ⟨argTy, εf, hw, hf, harg⟩ := ih he
      refine ⟨argTy, εf, Ty.effWeaken_tyEquiv_right hw hε, ?_, ?_⟩
      · exact HasType.conv hf (.congrFun (.refl _) (.refl _) hτ) hε
      · exact HasType.conv harg (.refl _) hε
  | _ => simp at he

end Eyg.Types
