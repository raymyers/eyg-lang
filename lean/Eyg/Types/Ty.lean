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
and effects are rows built from `empty`/`rowExtend`/`effectExtend`.

**`var` carries a generalization *level* tag** (`plan/eyg-g1-level-tagged-ty.md`):
`var level idx` — `level` names which generalization layer this variable belongs to
(`0` = the ambient/global scope, matching every pre-existing use of `Ty`; `k > 0` =
`k`-deep inside nested `let`-polymorphism), `idx` is its position within that level.
This resolves the nested-`let_poly` substitution-stability wall
(`Generalization.lean`'s `generalizes_subst_false`): a level-scoped ambient
substitution can only ever rewrite its own level's `var` leaves, so it structurally
cannot reach a *different* scheme's quantifiers, regardless of index magnitude — no
shifting/reindexing is needed the way the old single-index-space design required. -/
inductive Ty where
  | var (level idx : Nat)
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

/-! ## Effect weakening (row subsumption for application — T6b / Open Question 3)

The application frames must let a function's *latent* effect row `εf` be smaller than
the ambient row `ε` (e.g. `fix`'s **pure** builder `α →⟨∅⟩ α` applied inside an
effectful recursion ambient, or any pure builtin applied under a non-empty ambient).

The natural notion is membership-based subsumption (`EffSub`, `Eyg/Types/EffSub.lean`),
but a bare `EffSub εf ε` premise on the typing rule is **not substitution-stable**
(`EffSub (var 0) .empty` holds vacuously, but its `σ`-image need not), which would break
`hasType_subst` (needed by `gen`). `EffWeaken` is the **substitution-stable** restriction
that is still sufficient for `fix` / pure builtins: the latent is (equivalent to) the
ambient, or to the empty row. Both disjuncts survive substitution
(`subst σ ε`/`subst σ .empty = .empty`); it absorbs the row reorderings the judgment
already reasons up to (via `TyEquiv`), so the term-level weakening lemma `weakenEff`
(admissible) and `inv_app`'s `conv` arm both go through. A general row-variable-aware
subsumption (`⟨a⟩ ⊑ ⟨a,b⟩` with a shared tail var) is future work; `fix` does not need it. -/

/-- The function latent row `εf` may be applied at ambient `ε` when `εf` is equivalent
to `ε` or to the empty row. -/
def EffWeaken (εf ε : Ty) : Prop := TyEquiv εf ε ∨ TyEquiv εf .empty

/-- Reflexivity (the exact-match case, all of T3–T5). -/
theorem effWeaken_refl (ε : Ty) : EffWeaken ε ε := .inl (.refl _)

/-- **The empty latent is weakenable to any ambient** — the `fix` pure-builder /
pure-builtin key. -/
theorem effWeaken_empty (ε : Ty) : EffWeaken .empty ε := .inr (.refl _)

/-- Transitivity (compose two weakenings). -/
theorem effWeaken_trans {a b c : Ty} (h₁ : EffWeaken a b) (h₂ : EffWeaken b c) :
    EffWeaken a c := by
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · exact .inl (h₁.trans h₂)
    · exact .inr (h₁.trans h₂)
  · exact .inr h₁

/-- Rewrite the ambient by a `TyEquiv` on the right. -/
theorem effWeaken_tyEquiv_right {a b c : Ty} (h : EffWeaken a b) (hbc : TyEquiv b c) :
    EffWeaken a c := effWeaken_trans h (.inl hbc)

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
