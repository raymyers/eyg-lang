import Eyg.Types.Scheme
import Eyg.Ir.Tree

/-!
# Declarative typing judgment — pure monomorphic core (Milestone T3a)

`HasType Γ e τ ε` — "in context `Γ`, term `e` has type `τ` and may perform
effects in row `ε`". This is the **declarative** judgment (a relation), with
rules transcribed from `contextual.do_infer`; we prove the dynamics sound against
it (we do *not* prove algorithm-J itself sound — that is the T8 stretch).

The signature carries the effect row `ε` **from the start** (plan rule 1: fix all
judgment signatures once). This slice pins nothing structurally, but the pure
fragment's terms perform no effects, so they are typeable at *any* ambient `ε`
(values are pure; `ε` is an upper bound) — exactly `do_infer`'s "pass `eff`
through" for literals/variables/lambda. The T3 soundness statement instantiates
`ε := empty`; T5 un-pins it with `Perform`/`Handle`.

## Rules in this slice (pure core)

`Variable` (instantiate a context scheme), `Lambda` (arrow carrying the body's
effect row in its middle slot; the closure value itself pure), `Apply` (effect
threading — the function's latent effect equals the ambient row, per
`do_infer`'s `unify(test_eff, eff)`), monomorphic `Let`, the `Integer`/`String`/
`Binary` literals, `Builtin` (instantiate a `Builtins.scheme`), and the
**`TyEquiv` conversion rule** so row order never blocks a derivation.

Structured-data nodes (`Extend`/`Select`/`Tag`/`Case`/`Cons`/…) join in T4 and
effects (`Perform`/`Handle`) in T5 — as *new constructors*, never re-typing this
judgment.
-/

namespace Eyg.Types

open Eyg.Ir

/-- Typing context: a list of `(name, scheme)` bindings, innermost first
(`contextual` threads `[#(x, scheme), ..env]`; lookup takes the first match,
matching the interpreter's `Env` shadowing). -/
abbrev Ctx := List (String × Scheme)

/-- The declarative typing judgment for EYG terms (pure core this slice). -/
inductive HasType {m : Type} : Ctx → Tree.Node m → Ty → Ty → Prop where
  /-- Variable: look up a scheme and instantiate it (`do_infer` `ir.Variable`). -/
  | var {Γ x s args ε a} :
      Γ.lookup x = some s →
      HasType Γ ⟨.Variable x, a⟩ (s.instantiate args) ε
  /-- Lambda: the arrow carries the body's effect row `εb` in its middle slot; the
  closure value performs nothing, so it is typeable at any ambient `ε`. -/
  | lam {Γ x body argTy εb retTy ε a} :
      HasType ((x, .mono argTy) :: Γ) body retTy εb →
      HasType Γ ⟨.Lambda x body, a⟩ (.fun argTy εb retTy) ε
  /-- Application: the function's latent effect equals the ambient row `ε`
  (`do_infer` unifies `test_eff` with `eff`); `f` and `arg` are evaluated at `ε`. -/
  | app {Γ f arg argTy retTy ε a} :
      HasType Γ f (.fun argTy ε retTy) ε →
      HasType Γ arg argTy ε →
      HasType Γ ⟨.Apply f arg, a⟩ retTy ε
  /-- Monomorphic `let` (generalization is T6). -/
  | let_ {Γ x defn body defnTy bodyTy ε a} :
      HasType Γ defn defnTy ε →
      HasType ((x, .mono defnTy) :: Γ) body bodyTy ε →
      HasType Γ ⟨.Let x defn body, a⟩ bodyTy ε
  /-- Integer literal. -/
  | int {Γ n ε a} : HasType Γ ⟨.Integer n, a⟩ .integer ε
  /-- String literal. -/
  | str {Γ s ε a} : HasType Γ ⟨.String s, a⟩ .string ε
  /-- Binary literal. -/
  | bin {Γ b ε a} : HasType Γ ⟨.Binary b, a⟩ .binary ε
  /-- Builtin: instantiate its scheme (`do_infer` `ir.Builtin`/`prim`). -/
  | builtin {Γ id s args ε a} :
      Builtins.scheme id = some s →
      HasType Γ ⟨.Builtin id, a⟩ (s.instantiate args) ε
  /-- The empty list `Tail`, polymorphic in its element type (`prim(List(q0))`). -/
  | tail {Γ elem ε a} : HasType Γ ⟨.Tail, a⟩ (.list elem) ε
  /-- List `Cons`: `∀α. α → List α → List α` (`cons() = pure2(q0, List q0, List q0)`). -/
  | cons {Γ elem ε a} :
      HasType Γ ⟨.Cons, a⟩ (.fun elem .empty (.fun (.list elem) .empty (.list elem))) ε
  /-- Variant injection `Tag l`: `∀α r. α → ⟨l : α | r⟩`
  (`tag(l) = pure1(q0, Union(RowExtend l q0 q1))`). -/
  | tag {Γ l elem tail ε a} :
      HasType Γ ⟨.Tag l, a⟩ (.fun elem .empty (.union (.rowExtend l elem tail))) ε
  /-- The empty record `Empty` (`prim(Record(Empty))`). -/
  | empty {Γ ε a} : HasType Γ ⟨.Empty, a⟩ (.record .empty) ε
  /-- **Conversion**: types and effect rows may be replaced by `TyEquiv`-equal
  ones (Leijen's `∼=` in the application rule) so row order never blocks a rule. -/
  | conv {Γ e τ τ' ε ε'} :
      HasType Γ e τ ε → Ty.TyEquiv τ τ' → Ty.TyEquiv ε ε' →
      HasType Γ e τ' ε'

/-! ## Sanity checks: typing real fixtures

Each `example` is a derivation exercising the rules end-to-end (the closed terms
also drive `State.lean`'s `#guard`s, so the typed and the evaluated meaning of
each fixture coincide). Effect row pinned to `empty`. -/

section Examples
open Eyg.Ir.Tree

-- `(\x. x) 1 : integer ! empty`
example : HasType (m := Unit) [] (apply (lambda "x" (variable_ "x")) (integer 1))
    .integer .empty := by
  apply HasType.app (argTy := .integer)
  · exact HasType.lam (HasType.var (s := .mono .integer) (args := []) rfl)
  · exact HasType.int

-- `let x = 2 in x : integer ! empty`
example : HasType (m := Unit) [] (let_ "x" (integer 2) (variable_ "x")) .integer .empty := by
  apply HasType.let_ (defnTy := .integer)
  · exact HasType.int
  · exact HasType.var (s := .mono .integer) (args := []) rfl

-- `int_add 2 3 : integer ! empty` (builtin instantiated, effect threading)
example : HasType (m := Unit) [] (add (integer 2) (integer 3)) .integer .empty := by
  apply HasType.app (argTy := .integer)
  · apply HasType.app (argTy := .integer)
    · exact HasType.builtin (id := "int_add")
        (s := .mono (Ty.pure2 .integer .integer .integer)) (args := []) rfl
    · exact HasType.int
  · exact HasType.int

-- `\x. x` typeable at a *non-empty* ambient row (the closure value is pure),
-- exercising the `ε`-generality of values.
example : HasType (m := Unit) [] (lambda "x" (variable_ "x"))
    (.fun .integer .empty .integer) (.effectExtend "Log" .string .empty .empty) :=
  HasType.lam (HasType.var (s := .mono .integer) (args := []) rfl)

-- Conversion: `\x. x : boolean → boolean` retyped up to row reordering of the
-- `boolean` union (`{True,False}` ∼= `{False,True}`). The ambient `ε` stays
-- `empty` (an arithmetic/effect term could not move it — `int_add` pins it). This
-- is where the `TyEquiv` conversion rule earns its keep: row order never blocks.
example : HasType (m := Unit) [] (lambda "x" (variable_ "x"))
    (.fun (Ty.union' [("False", Ty.unit), ("True", Ty.unit)]) .empty
          (Ty.union' [("False", Ty.unit), ("True", Ty.unit)])) .empty := by
  have hb : Ty.TyEquiv Ty.boolean (Ty.union' [("False", Ty.unit), ("True", Ty.unit)]) := by
    apply Ty.TyEquiv.congrUnion
    simpa [Ty.rows] using Ty.TyEquiv.swapRow (l := "True") (l' := "False")
      (f := Ty.unit) (f' := Ty.unit) (t := .empty) (by decide)
  apply HasType.conv (τ := .fun Ty.boolean .empty Ty.boolean) (ε := .empty)
  · exact HasType.lam (HasType.var (s := .mono Ty.boolean) (args := []) rfl)
  · exact Ty.TyEquiv.congrFun hb (Ty.TyEquiv.refl _) hb
  · exact Ty.TyEquiv.refl _

end Examples

end Eyg.Types
