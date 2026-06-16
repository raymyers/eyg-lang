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

theorem tyEquiv_list_inv {τ elem : Ty} (h : TyEquiv τ (.list elem)) : ∃ elem', τ = .list elem' := by
  have hs := tyEquiv_shape h
  cases τ <;> simp_all [shape]

theorem tyEquiv_record_inv {τ r : Ty} (h : TyEquiv τ (.record r)) : ∃ r', τ = .record r' := by
  have hs := tyEquiv_shape h
  cases τ <;> simp_all [shape]

theorem tyEquiv_union_inv {τ r : Ty} (h : TyEquiv τ (.union r)) : ∃ r', τ = .union r' := by
  have hs := tyEquiv_shape h
  cases τ <;> simp_all [shape]

/-! ## Component inversion for arrows (no-confusion up to `TyEquiv`)

`tyEquiv_*_inv` recover only the head. The `StackWf` conversion lemma also needs
the **components** of an arrow: `TyEquiv (.fun a e r) (.fun a' e' r')` must give
`a ∼= a'`, `e ∼= e'`, `r ∼= r'`. The slick proof avoids normalization: project
each component with a total function that is the identity off `.fun`, and show the
projection is a `TyEquiv` congruence. The arrow case yields the stored component
premise; every other case re-applies its own constructor (the projection is
identity there). -/

/-- Domain projection: the argument type of an arrow, else the type itself. -/
def domOf : Ty → Ty | .fun a _ _ => a | t => t
/-- Row projection under `union`, else the type itself. -/
def unionRow : Ty → Ty | .union r => r | t => t
/-- Effect-row projection of an arrow, else the type itself. -/
def effOf : Ty → Ty | .fun _ e _ => e | t => t
/-- Codomain projection of an arrow, else the type itself. -/
def retOf : Ty → Ty | .fun _ _ r => r | t => t

theorem tyEquiv_domOf {s t : Ty} (h : TyEquiv s t) : TyEquiv (domOf s) (domOf t) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congrFun ha _ _ _ _ _ => exact ha
  | congrList hb _ => exact .congrList hb
  | congrRecord hr _ => exact .congrRecord hr
  | congrUnion hr _ => exact .congrUnion hr
  | congrPromise ha _ => exact .congrPromise ha
  | congrRow hf ht _ _ => exact .congrRow hf ht
  | congrEff ha hb ht _ _ _ => exact .congrEff ha hb ht
  | swapRow hne => exact .swapRow hne
  | swapEff hne => exact .swapEff hne

theorem tyEquiv_effOf {s t : Ty} (h : TyEquiv s t) : TyEquiv (effOf s) (effOf t) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congrFun _ he _ _ _ _ => exact he
  | congrList hb _ => exact .congrList hb
  | congrRecord hr _ => exact .congrRecord hr
  | congrUnion hr _ => exact .congrUnion hr
  | congrPromise ha _ => exact .congrPromise ha
  | congrRow hf ht _ _ => exact .congrRow hf ht
  | congrEff ha hb ht _ _ _ => exact .congrEff ha hb ht
  | swapRow hne => exact .swapRow hne
  | swapEff hne => exact .swapEff hne

theorem tyEquiv_retOf {s t : Ty} (h : TyEquiv s t) : TyEquiv (retOf s) (retOf t) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congrFun _ _ hr _ _ _ => exact hr
  | congrList hb _ => exact .congrList hb
  | congrRecord hr _ => exact .congrRecord hr
  | congrUnion hr _ => exact .congrUnion hr
  | congrPromise ha _ => exact .congrPromise ha
  | congrRow hf ht _ _ => exact .congrRow hf ht
  | congrEff ha hb ht _ _ _ => exact .congrEff ha hb ht
  | swapRow hne => exact .swapRow hne
  | swapEff hne => exact .swapEff hne

theorem tyEquiv_unionRow {s t : Ty} (h : TyEquiv s t) : TyEquiv (unionRow s) (unionRow t) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congrFun ha he hr _ _ _ => exact .congrFun ha he hr
  | congrList hb _ => exact .congrList hb
  | congrRecord hr _ => exact .congrRecord hr
  | congrUnion hr _ => exact hr
  | congrPromise ha _ => exact .congrPromise ha
  | congrRow hf ht _ _ => exact .congrRow hf ht
  | congrEff ha hb ht _ _ _ => exact .congrEff ha hb ht
  | swapRow hne => exact .swapRow hne
  | swapEff hne => exact .swapEff hne

/-- **Arrow component inversion.** Recover the three component equivalences. -/
theorem tyEquiv_fun_components {a e r a' e' r' : Ty}
    (h : TyEquiv (.fun a e r) (.fun a' e' r')) :
    TyEquiv a a' ∧ TyEquiv e e' ∧ TyEquiv r r' :=
  ⟨tyEquiv_domOf h, tyEquiv_effOf h, tyEquiv_retOf h⟩

/-- A type equivalent to an arrow *is* an arrow with `TyEquiv` components. -/
theorem tyEquiv_fun_inv' {τ a e r : Ty} (h : TyEquiv τ (.fun a e r)) :
    ∃ a' e' r', τ = .fun a' e' r' ∧ TyEquiv a' a ∧ TyEquiv e' e ∧ TyEquiv r' r := by
  obtain ⟨a', e', r', rfl⟩ := tyEquiv_fun_inv h
  obtain ⟨ha, he, hr⟩ := tyEquiv_fun_components h
  exact ⟨a', e', r', rfl, ha, he, hr⟩

/-! ## Sanity checks -/

-- A type equivalent to `boolean` is itself a `union`.
example {τ : Ty} (h : TyEquiv τ boolean) : ∃ r', τ = .union r' := tyEquiv_union_inv h

-- A type equivalent to `integer → integer` is itself an arrow.
example {τ : Ty} (h : TyEquiv τ (.fun .integer .empty .integer)) :
    ∃ a' e' r', τ = .fun a' e' r' := tyEquiv_fun_inv h

end Eyg.Types.Ty
