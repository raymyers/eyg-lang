import Eyg.Basic

/-!
# EYG type language & row equivalence (Milestone T1)

The **full** EYG type language, transcribed from
`packages/gleam_analysis/src/eyg/analysis/type_/isomorphic.gleam`'s `Type(var)`,
plus the Leijen *scoped-labels* row equivalence the declarative typing judgment
threads (its conversion rule replaces syntactic equality with `TyEquiv`).

## Type variables: de Bruijn

`isomorphic.Type` is parametric in `var`; we instantiate it to **de Bruijn
indices** (`Ty.var : Nat → Ty`). Canonical types, decidable structural equality,
no α-renaming (`references/progress-preservation-recipe.md` §5).

## Rows, records, unions, effects — one relation

Records (`record r`), variant unions (`union r`), and effect rows (the middle
slot of `fun` / `effectExtend`) are **all** rows: `empty` / `rowExtend` (value
rows) and `empty` / `effectExtend` (effect rows). Per Leijen
(`references/row-types-scoped-labels.md` §2), two rows are equal *up to
permutation of distinct labels* — duplicate labels keep their order (scoping).
`TyEquiv` is the congruence closure of the two swap rules; the `l ≠ l'` guard on
each swap is **load-bearing** and kept as a decidable obligation.

A decision-procedure for `TyEquiv` (stable-sort normalization ⇒ decidability and
the sorted-record reconciliation lemma) is the T1b follow-up; the declarative
soundness proof needs only the relation and its equivalence laws, delivered here.
-/

namespace Eyg.Types

/-- EYG types, mirroring `isomorphic.Type(var)` with de Bruijn type variables.

`fun arg eff ret` carries an **effect row** in its middle slot. Records, unions,
and effects are rows built from `empty`/`rowExtend`/`effectExtend`. -/
inductive Ty where
  | var (idx : Nat)
  | fun (arg : Ty) (eff : Ty) (ret : Ty)
  | binary
  | integer
  | string
  | list (elem : Ty)
  | record (row : Ty)
  | union (row : Ty)
  | empty
  | rowExtend (label : String) (field : Ty) (tail : Ty)
  | effectExtend (label : String) (lift : Ty) (reply : Ty) (tail : Ty)
  | never
  | promise (value : Ty)
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Ty

/-! ## Smart constructors (mirroring `isomorphic.gleam`) -/

/-- `unit = Record(Empty)`. -/
def unit : Ty := .record .empty

/-- Build a value row from a field list over a tail (`isomorphic.do_rows`):
fold right, so the first list entry is the outermost (visible) extension. -/
def rows (fields : List (String × Ty)) (tail : Ty) : Ty :=
  fields.foldr (fun f acc => .rowExtend f.1 f.2 acc) tail

/-- `Record(rows(fields))`. -/
def record' (fields : List (String × Ty)) : Ty := .record (rows fields .empty)

/-- `Union(rows(fields))`. -/
def union' (fields : List (String × Ty)) : Ty := .union (rows fields .empty)

/-- `boolean = Union(|True :: unit, False :: unit|)`. -/
def boolean : Ty := union' [("True", unit), ("False", unit)]

/-- `result(value, reason) = Union(|Ok :: value, Error :: reason|)`. -/
def result (value reason : Ty) : Ty := union' [("Ok", value), ("Error", reason)]

/-- `option(value) = Union(|Some :: value, None :: unit|)`. -/
def option (value : Ty) : Ty := union' [("Some", value), ("None", unit)]

/-! ## Row equivalence — Leijen's scoped-labels equality (Figure 1, on rows)

`TyEquiv` is the congruence closure of reflexivity and the two row-swap rules.
With `symm`/`trans` as constructors it is an `Equivalence` by construction; the
per-constructor congruence rules let it act under every type former, and the two
`swap` rules (guarded by `l ≠ l'`) permute distinct-labelled row entries while
**never** commuting equal labels — exactly "rows equal up to permutation of
distinct labels". -/

/-- Type equality up to row reordering (Leijen `∼=`, restricted to EYG types). -/
inductive TyEquiv : Ty → Ty → Prop where
  | refl (t : Ty) : TyEquiv t t
  | symm {s t : Ty} : TyEquiv s t → TyEquiv t s
  | trans {r s t : Ty} : TyEquiv r s → TyEquiv s t → TyEquiv r t
  -- congruence
  | congrFun {a a' e e' r r'} :
      TyEquiv a a' → TyEquiv e e' → TyEquiv r r' → TyEquiv (.fun a e r) (.fun a' e' r')
  | congrList {a a'} : TyEquiv a a' → TyEquiv (.list a) (.list a')
  | congrRecord {r r'} : TyEquiv r r' → TyEquiv (.record r) (.record r')
  | congrUnion {r r'} : TyEquiv r r' → TyEquiv (.union r) (.union r')
  | congrPromise {a a'} : TyEquiv a a' → TyEquiv (.promise a) (.promise a')
  /-- `eq-head`: congruence under a value-row extension. -/
  | congrRow {l f f' t t'} :
      TyEquiv f f' → TyEquiv t t' → TyEquiv (.rowExtend l f t) (.rowExtend l f' t')
  /-- congruence under an effect-row extension. -/
  | congrEff {l a a' b b' t t'} :
      TyEquiv a a' → TyEquiv b b' → TyEquiv t t' →
      TyEquiv (.effectExtend l a b t) (.effectExtend l a' b' t')
  /-- `eq-swap` on value rows: commute the first two entries iff labels differ. -/
  | swapRow {l l' f f' t} :
      l ≠ l' →
      TyEquiv (.rowExtend l f (.rowExtend l' f' t)) (.rowExtend l' f' (.rowExtend l f t))
  /-- `eq-swap` on effect rows: commute the first two entries iff labels differ. -/
  | swapEff {l l' a b a' b' t} :
      l ≠ l' →
      TyEquiv (.effectExtend l a b (.effectExtend l' a' b' t))
              (.effectExtend l' a' b' (.effectExtend l a b t))

/-- `TyEquiv` is an equivalence relation (refl/symm/trans are constructors). -/
theorem tyEquiv_equivalence : Equivalence TyEquiv :=
  ⟨TyEquiv.refl, TyEquiv.symm, TyEquiv.trans⟩

instance : Trans TyEquiv TyEquiv TyEquiv where
  trans := TyEquiv.trans

/-- Row equivalence is `TyEquiv` on rows (records/unions); effect-row equivalence
likewise. Named aliases mirror the plan's `RowEquiv`/`EffEquiv`. -/
abbrev RowEquiv : Ty → Ty → Prop := TyEquiv
abbrev EffEquiv : Ty → Ty → Prop := TyEquiv

/-! ## Sanity checks -/

-- `{True :: unit, False :: unit}` ∼= `{False :: unit, True :: unit}` (distinct labels swap).
example : TyEquiv (rows [("True", unit), ("False", unit)] .empty)
                  (rows [("False", unit), ("True", unit)] .empty) := by
  simpa [rows] using TyEquiv.swapRow (l := "True") (l' := "False")
    (f := unit) (f' := unit) (t := .empty) (by decide)

-- Reordering distinct fields under `Union` (so `boolean` is order-insensitive).
example : TyEquiv boolean (union' [("False", unit), ("True", unit)]) := by
  apply TyEquiv.congrUnion
  simpa [rows] using TyEquiv.swapRow (l := "True") (l' := "False")
    (f := unit) (f' := unit) (t := .empty) (by decide)

-- An effect row commutes two distinct operations.
example : TyEquiv (.effectExtend "Get" integer integer (.effectExtend "Put" integer unit .empty))
                  (.effectExtend "Put" integer unit (.effectExtend "Get" integer integer .empty)) :=
  TyEquiv.swapEff (by decide)

-- Same-label entries do **not** commute through `swapRow` — but `refl` holds.
example : TyEquiv (.rowExtend "x" integer (.rowExtend "x" string .empty))
                  (.rowExtend "x" integer (.rowExtend "x" string .empty)) := TyEquiv.refl _

end Ty

end Eyg.Types
