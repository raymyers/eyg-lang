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

/-! ## `Handle` scheme component types (T5)

The deep-handler scheme `handle(l)` (`contextual.gleam` `handle`) factors into these
pieces. They are `abbrev`s (reducible) so `canonical_arrow` / `tyEquiv_fun_inv` see the
arrows through them. -/

/-- The resumption type `Fun(reply, tail, ret)` — a delimited continuation. -/
abbrev kontTy (reply tail ret : Ty) : Ty := .fun reply tail ret
/-- The handler type `Fun(lift, ∅, Fun(kont, tail, ret))` — gets the performed value
and the resumption, returns the answer under the discharged row `tail`. -/
abbrev handlerTy (lift reply tail ret : Ty) : Ty :=
  .fun lift .empty (.fun (kontTy reply tail ret) tail ret)
/-- The guarded-computation type `Fun({}, ⟨l:(lift,reply)|tail⟩, ret)` — runs under
the handled row; `l` is discharged by the handler. -/
abbrev execTy (l : String) (lift reply tail ret : Ty) : Ty :=
  .fun (.record .empty) (.effectExtend l lift reply tail) ret
/-- `handle(l) = Fun(handler, ∅, Fun(exec, tail, ret))`. -/
abbrev handleTy (l : String) (lift reply tail ret : Ty) : Ty :=
  .fun (handlerTy lift reply tail ret) .empty
    (.fun (execTy l lift reply tail ret) tail ret)

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
  /-- The empty-variant eliminator `NoCases`: `∀β. ⟨⟩ → β`
  (`nocases() = pure1(Union(Empty), q0)`). -/
  | nocases {Γ ret ε a} :
      HasType Γ ⟨.NoCases, a⟩ (.fun (.union .empty) .empty ret) ε
  /-- Variant decomposition `Case l`: `(α→⟨e⟩β) → (⟨r⟩→⟨e⟩β) → (⟨l:α|r⟩→⟨e⟩β)`
  (`case_(l) = pure2(branch, otherwise, exec)`). -/
  | case_ {Γ l inner eff ret tail ε a} :
      HasType Γ ⟨.Case l, a⟩
        (.fun (.fun inner eff ret) .empty
          (.fun (.fun (.union tail) eff ret) .empty
            (.fun (.union (.rowExtend l inner tail)) eff ret))) ε
  /-- Record projection `Select l`: `∀α r. {l:α|r} → α`
  (`select(l) = pure1(Record(RowExtend l q0 q1), q0)`). -/
  | select {Γ l fieldTy tail ε a} :
      HasType Γ ⟨.Select l, a⟩ (.fun (.record (.rowExtend l fieldTy tail)) .empty fieldTy) ε
  /-- Record extension `Extend l`: `∀α r. α → {r} → {l:α|r}`
  (`extend(l) = pure2(q0, Record q1, Record(RowExtend l q0 q1))`). -/
  | extend {Γ l fieldTy row ε a} :
      HasType Γ ⟨.Extend l, a⟩ (.fun fieldTy .empty
        (.fun (.record row) .empty (.record (.rowExtend l fieldTy row)))) ε
  /-- Record overwrite `Overwrite l`: `∀α β r. α → {l:β|r} → {l:α|r}`
  (`overwrite(l) = pure2(q0, Record(RowExtend l q1 q2), Record(RowExtend l q0 q2))`).
  The input record must already carry `l` (old type `β`). -/
  | overwrite {Γ l newTy oldTy tail ε a} :
      HasType Γ ⟨.Overwrite l, a⟩ (.fun newTy .empty
        (.fun (.record (.rowExtend l oldTy tail)) .empty
          (.record (.rowExtend l newTy tail)))) ε
  /-- The empty record `Empty` (`prim(Record(Empty))`). -/
  | empty {Γ ε a} : HasType Γ ⟨.Empty, a⟩ (.record .empty) ε
  /-- Effect operation `Perform l`: `∀α β μ. α →⟨l:(α,β)|μ⟩ β`
  (`perform(l) = Fun(q0, EffectExtend(l,(q0,q1),Empty), q1)`; the scheme pins the
  tail to `Empty`, the declarative rule allows an arbitrary tail `μ` — Koka's
  "operation as a variable", so `Perform l arg` is typeable exactly when the ambient
  row carries `l` (effect safety falls out of the `app` rule's latent = ambient
  unification). The `Perform l` node is a value, so its own ambient `ε` is free. -/
  | perform {Γ l a b μ ε ann} :
      HasType Γ ⟨.Perform l, ann⟩ (.fun a (.effectExtend l a b μ) b) ε
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

-- Effect (T5): `perform "Log" "hi"` performs the `Log` operation. It types at the
-- reply type `unit` under an ambient row that *carries* `Log : (String, unit)` —
-- effect safety made visible: the term is only typeable when `Log ∈ ε`.
example : HasType (m := Unit) [] (apply (perform "Log") (string "hi"))
    Ty.unit (.effectExtend "Log" .string Ty.unit .empty) := by
  apply HasType.app (argTy := .string)
  · exact HasType.perform
  · exact HasType.str

end Examples

end Eyg.Types
