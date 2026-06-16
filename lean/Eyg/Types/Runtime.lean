import Eyg.Types.Typing
import Eyg.Types.TyEquivInv
import Eyg.Interpreter.State

/-!
# Runtime typing — values & environments (Milestone T3b)

Typing for *runtime* objects, the layer that lets preservation/progress talk
about machine states. Following `references/abstract-machine-type-soundness.md`
§3, an environment machine replaces the **substitution lemma** with an
**environment-typing + lookup lemma**: a closure is well-typed when its captured
environment realizes a context under which its body type-checks, and variable
lookup is sound against that.

This slice delivers the **value** half — `HasTypeV` (values), `EnvWf`
(environments, lock-step with `Ctx`), and `BuiltinPartialWf` (a partially-applied
builtin at its residual arrow) — plus the lookup lemma and the canonical-forms
lemmas. The **continuation** half (`StackWf` answer-type transformer) and
`MStateWf`, then `preservation`/`progress`/`soundness`, are the T3c sub-slice.

## Why a partially-applied builtin is typed *only at an arrow*

A resting `Partial (Builtin id) applied` is always **strictly under-applied** —
the machine reduces a saturated builtin immediately, never leaving it as a value.
So its type is always a residual *arrow* (`fun a ε r`). Baking that into
`HasTypeV.partialBuiltin` (the conclusion type is literally `.fun a ε r`) makes
the arrow canonical-forms lemma immediate and excludes the un-reachable
"saturated builtin sitting as a base-typed value". Preservation maintains it:
applying the last argument reduces rather than resting.
-/

namespace Eyg.Types

open Eyg.Interpreter
open Eyg.Ir

/-! Runtime typing for values, environments, and builtin partials (mutually
recursive: a `Closure` carries an `EnvWf`; an env binds `HasTypeV` values). Values
are pure — no effect row (a value *is* a result). -/
mutual

/-- A value has a type. Each constructor's conclusion is *any* type `TyEquiv`-equal
to the value's natural type — conversion is baked in at the leaves (rather than as
a separate recursive `convV` rule), so canonical forms are pure `cases` and the
typing-judgment's conversion is localized to values (keeping `StackWf`
conversion-free). -/
inductive HasTypeV {m : Type} : Value m → Ty → Prop where
  | int {n τ} : Ty.TyEquiv .integer τ → HasTypeV (.Integer n) τ
  | str {s τ} : Ty.TyEquiv .string τ → HasTypeV (.String s) τ
  | bin {b τ} : Ty.TyEquiv .binary τ → HasTypeV (.Binary b) τ
  /-- A closure inhabits (a type equivalent to) an arrow whose middle slot is the
  body's effect row, provided its captured env realizes a context typing the body. -/
  | closure {x body env argTy εb retTy Γ τ} :
      EnvWf env Γ →
      HasType ((x, .mono argTy) :: Γ) body retTy εb →
      Ty.TyEquiv (.fun argTy εb retTy) τ →
      HasTypeV (.Closure x body env) τ
  /-- A (strictly under-applied) builtin partial at (a type equivalent to) its
  residual arrow. -/
  | partialBuiltin {id s args applied a ε r τ} :
      Builtins.scheme id = some s →
      BuiltinPartialWf (s.instantiate args) applied (.fun a ε r) →
      Ty.TyEquiv (.fun a ε r) τ →
      HasTypeV (.Partial (.Builtin id) applied) τ
  /-- The empty list inhabits any list type. -/
  | listNil {elem τ} : Ty.TyEquiv (.list elem) τ → HasTypeV (.LinkedList []) τ
  /-- A cons cell: head and tail share the element type. -/
  | listCons {hd tl elem τ} :
      HasTypeV hd elem → HasTypeV (.LinkedList tl) (.list elem) →
      Ty.TyEquiv (.list elem) τ → HasTypeV (.LinkedList (hd :: tl)) τ
  /-- The empty record inhabits the empty-row record type. -/
  | recordNil {τ} : Ty.TyEquiv (.record .empty) τ → HasTypeV (.Record []) τ
  /-- The unsaturated `Cons` (no args): `α → List α → List α`. -/
  | partialConsNil {elem τ} :
      Ty.TyEquiv (.fun elem .empty (.fun (.list elem) .empty (.list elem))) τ →
      HasTypeV (.Partial .Cons []) τ
  /-- `Cons` applied to its head: `List α → List α`. -/
  | partialConsOne {hd elem τ} :
      HasTypeV hd elem → Ty.TyEquiv (.fun (.list elem) .empty (.list elem)) τ →
      HasTypeV (.Partial .Cons [hd]) τ

/-- An environment realizes a context, binding-for-binding. The value bound to a
scheme must inhabit *every* instantiation of it (polymorphic readiness; for the
monomorphic schemes of T3–T5 this is just `HasTypeV v τ`). -/
inductive EnvWf {m : Type} : Env m → Ctx → Prop where
  | nil : EnvWf [] []
  | cons {y v s env Γ} :
      (∀ args, HasTypeV v (s.instantiate args)) →
      EnvWf env Γ →
      EnvWf ((y, v) :: env) ((y, s) :: Γ)

/-- Peel the already-applied arguments of a builtin partial off an arrow,
yielding the residual type: each applied value matches the next domain. -/
inductive BuiltinPartialWf {m : Type} : Ty → List (Value m) → Ty → Prop where
  | nil {τ} : BuiltinPartialWf τ [] τ
  | cons {a ε r v applied τ} :
      HasTypeV v a →
      BuiltinPartialWf r applied τ →
      BuiltinPartialWf (.fun a ε r) (v :: applied) τ

end

/-! ## The lookup lemma (replaces the substitution lemma)

If `env` realizes `Γ` and `Γ` binds `x` to scheme `s`, then `env` binds `x` to a
value inhabiting every instantiation of `s` — in particular the one the `var`
typing rule chose. -/

theorem envwf_lookup {m : Type} {env : Env m} {Γ : Ctx} {x : String} {s : Scheme}
    (h : EnvWf env Γ) (hl : Γ.lookup x = some s) :
    ∃ v, env.lookup x = some v ∧ ∀ args, HasTypeV v (s.instantiate args) := by
  induction env generalizing Γ with
  | nil => cases h; simp [List.lookup] at hl
  | cons hd tl ih =>
      obtain ⟨y, v⟩ := hd
      cases h with
      | @cons _ _ s' _ Γ₀ hv henv =>
          simp only [List.lookup_cons] at hl ⊢
          by_cases hxy : (x == y) = true
          · simp only [hxy] at hl ⊢
            cases hl
            exact ⟨v, rfl, hv⟩
          · simp only [hxy] at hl ⊢
            exact ih henv hl

/-- **Value conversion** (derived): a value's type may be replaced by a
`TyEquiv`-equal one. Each constructor already carries a `TyEquiv` to its natural
type; compose it with `trans`. -/
theorem HasTypeV.conv {m : Type} {v : Value m} {τ τ' : Ty}
    (h : HasTypeV v τ) (heq : Ty.TyEquiv τ τ') : HasTypeV v τ' := by
  cases h with
  | int he => exact .int (he.trans heq)
  | str he => exact .str (he.trans heq)
  | bin he => exact .bin (he.trans heq)
  | closure henv hbody he => exact .closure henv hbody (he.trans heq)
  | partialBuiltin hs hp he => exact .partialBuiltin hs hp (he.trans heq)
  | listNil he => exact .listNil (he.trans heq)
  | listCons hh ht he => exact .listCons hh ht (he.trans heq)
  | recordNil he => exact .recordNil (he.trans heq)
  | partialConsNil he => exact .partialConsNil (he.trans heq)
  | partialConsOne hh he => exact .partialConsOne hh (he.trans heq)

/-! ## Canonical forms

A value of a base type is the corresponding literal; a value of an arrow type is
a closure or a builtin partial (the only callable shapes in the pure core). Since
conversion is baked into each constructor's conclusion, these are pure `cases`:
the constructors whose *natural* head differs carry an impossible `TyEquiv` (e.g.
`TyEquiv .string .integer`), refuted by the head-shape inversion lemmas. -/

theorem canonical_integer {m : Type} {v : Value m} (h : HasTypeV v .integer) :
    ∃ n, v = .Integer n := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, rfl⟩ | exact absurd (Ty.tyEquiv_integer_inv he) (by simp)

theorem canonical_string {m : Type} {v : Value m} (h : HasTypeV v .string) :
    ∃ s, v = .String s := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, rfl⟩ | exact absurd (Ty.tyEquiv_string_inv he) (by simp)

theorem canonical_binary {m : Type} {v : Value m} (h : HasTypeV v .binary) :
    ∃ b, v = .Binary b := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, rfl⟩ | exact absurd (Ty.tyEquiv_binary_inv he) (by simp)

/-- A value at a list type is a `LinkedList`. -/
theorem canonical_list {m : Type} {v : Value m} {elem : Ty} (h : HasTypeV v (.list elem)) :
    ∃ es, v = .LinkedList es := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, rfl⟩ | (obtain ⟨_, hc⟩ := Ty.tyEquiv_list_inv he; simp at hc)

/-- A value at an arrow type is a closure or a (callable) partial — never a
literal or a data structure. Callers `cases` the typing again to dispatch on the
partial's switch. -/
theorem canonical_arrow {m : Type} {v : Value m} {a ε r : Ty}
    (h : HasTypeV v (.fun a ε r)) :
    (∃ x body env, v = .Closure x body env) ∨
    (∃ sw applied, v = .Partial sw applied) := by
  cases h with
  | closure _ _ _ => exact Or.inl ⟨_, _, _, rfl⟩
  | partialBuiltin _ _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialConsNil _ => exact Or.inr ⟨_, _, rfl⟩
  | partialConsOne _ _ => exact Or.inr ⟨_, _, rfl⟩
  | int he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | str he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | bin he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | listNil he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | listCons _ _ he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | recordNil he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc

/-! ## Sanity checks -/

-- `Integer 5 : integer`.
example : HasTypeV (.Integer 5 : Value Unit) .integer := HasTypeV.int (Ty.TyEquiv.refl _)

-- The empty env realizes the empty context.
example : EnvWf ([] : Env Unit) [] := EnvWf.nil

-- A partially-applied `int_add` rests at the arrow `integer → integer`.
example : HasTypeV (.Partial (.Builtin "int_add") [.Integer 2] : Value Unit)
    (.fun .integer .empty .integer) :=
  HasTypeV.partialBuiltin (s := .mono (Ty.pure2 .integer .integer .integer)) (args := []) rfl
    (BuiltinPartialWf.cons (HasTypeV.int (Ty.TyEquiv.refl _)) BuiltinPartialWf.nil)
    (Ty.TyEquiv.refl _)

-- A closure over the empty env inhabits `integer → integer`.
example : HasTypeV (.Closure "x" (Eyg.Ir.Tree.variable_ "x") [] : Value Unit)
    (.fun .integer .empty .integer) :=
  HasTypeV.closure EnvWf.nil (HasType.var (s := .mono .integer) (args := []) rfl)
    (Ty.TyEquiv.refl _)

end Eyg.Types
