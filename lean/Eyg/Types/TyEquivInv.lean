import Eyg.Types.Ty

/-!
# `TyEquiv` head-shape invariance & inversion (Milestone T1b, partial)

`TyEquiv` carries a `conv`-style closure (`refl`/`symm`/`trans` + congruences +
row swaps), so a derivation of `TyEquiv s t` cannot be inverted by a bare `cases`
— it may end in `symm`/`trans`. The lightweight tool the preservation proof needs
is that **`TyEquiv` preserves the top-level head constructor's *shape***: two
equivalent types have the same outermost former (rows only ever swap *within* a
`rowExtend`/`effectExtend` head, never change it). From that, the per-head
inversion lemmas (`TyEquiv τ (.fun …) ⟹ τ is a .fun`, etc.) follow by a one-line
`cases`.

The full normalization decision procedure (`RowEquiv ↔ normalize r = normalize
s`, decidability, component-wise inversion `TyEquiv (.fun a e r) (.fun a' e' r')
⟹ a ∼= a' ∧ …`) is the remaining T1b work; this file delivers the head-shape
fragment, which is what unblocks the T3 preservation case split.
-/

namespace Eyg.Types.Ty

/-- The outermost type former, ignoring its arguments. -/
inductive Shape where
  | var | fn | binary | integer | string | list
  | record | union | empty | rowExtend | effectExtend | never | promise
  deriving DecidableEq, Repr

/-- The head shape of a type. -/
def shape : Ty → Shape
  | .var _ => .var
  | .fun _ _ _ => .fn
  | .binary => .binary
  | .integer => .integer
  | .string => .string
  | .list _ => .list
  | .record _ => .record
  | .union _ => .union
  | .empty => .empty
  | .rowExtend _ _ _ => .rowExtend
  | .effectExtend _ _ _ _ => .effectExtend
  | .never => .never
  | .promise _ => .promise

/-- **`TyEquiv` preserves head shape.** Every rule keeps the outermost former:
congruences are head-preserving by construction, and the row swaps relate a
`rowExtend`/`effectExtend` to another of the same head. -/
theorem tyEquiv_shape {s t : Ty} (h : TyEquiv s t) : shape s = shape t := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congrFun _ _ _ _ _ _ => rfl
  | congrList _ _ => rfl
  | congrRecord _ _ => rfl
  | congrUnion _ _ => rfl
  | congrPromise _ _ => rfl
  | congrRow _ _ _ _ => rfl
  | congrEff _ _ _ _ _ _ => rfl
  | swapRow _ => rfl
  | swapEff _ => rfl

/-! ## Per-head inversion lemmas

Each says "a type equivalent to one with head `H` itself has head `H`" (with its
arguments existentially recovered). Proved uniformly from `tyEquiv_shape`. -/

theorem tyEquiv_fun_inv {τ a e r : Ty} (h : TyEquiv τ (.fun a e r)) :
    ∃ a' e' r', τ = .fun a' e' r' := by
  have hs := tyEquiv_shape h
  cases τ <;> simp_all [shape]

theorem tyEquiv_integer_inv {τ : Ty} (h : TyEquiv τ .integer) : τ = .integer := by
  have hs := tyEquiv_shape h
  cases τ <;> simp_all [shape]

theorem tyEquiv_string_inv {τ : Ty} (h : TyEquiv τ .string) : τ = .string := by
  have hs := tyEquiv_shape h
  cases τ <;> simp_all [shape]

theorem tyEquiv_binary_inv {τ : Ty} (h : TyEquiv τ .binary) : τ = .binary := by
  have hs := tyEquiv_shape h
  cases τ <;> simp_all [shape]

theorem tyEquiv_record_inv {τ r : Ty} (h : TyEquiv τ (.record r)) : ∃ r', τ = .record r' := by
  have hs := tyEquiv_shape h
  cases τ <;> simp_all [shape]

theorem tyEquiv_union_inv {τ r : Ty} (h : TyEquiv τ (.union r)) : ∃ r', τ = .union r' := by
  have hs := tyEquiv_shape h
  cases τ <;> simp_all [shape]

/-! ## Sanity checks -/

-- A type equivalent to `boolean` is itself a `union`.
example {τ : Ty} (h : TyEquiv τ boolean) : ∃ r', τ = .union r' := tyEquiv_union_inv h

-- A type equivalent to `integer → integer` is itself an arrow.
example {τ : Ty} (h : TyEquiv τ (.fun .integer .empty .integer)) :
    ∃ a' e' r', τ = .fun a' e' r' := tyEquiv_fun_inv h

end Eyg.Types.Ty
