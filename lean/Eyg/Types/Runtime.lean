import Eyg.Types.Typing
import Eyg.Types.TyEquivInv
import Eyg.Types.Row
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
  /-- The unsaturated `Cons` (no args): `α → List α → List α`. -/
  | partialConsNil {elem τ} :
      Ty.TyEquiv (.fun elem .empty (.fun (.list elem) .empty (.list elem))) τ →
      HasTypeV (.Partial .Cons []) τ
  /-- `Cons` applied to its head: `List α → List α`. -/
  | partialConsOne {hd elem τ} :
      HasTypeV hd elem → Ty.TyEquiv (.fun (.list elem) .empty (.list elem)) τ →
      HasTypeV (.Partial .Cons [hd]) τ
  /-- A tagged value inhabits a union row containing its label. -/
  | tagged {label v elem tail τ} :
      HasTypeV v elem → Ty.TyEquiv (.union (.rowExtend label elem tail)) τ →
      HasTypeV (.Tagged label v) τ
  /-- The unsaturated `Tag l`: `α → ⟨l : α | r⟩`. -/
  | partialTag {label elem tail τ} :
      Ty.TyEquiv (.fun elem .empty (.union (.rowExtend label elem tail))) τ →
      HasTypeV (.Partial (.Tag label) []) τ
  /-- The unsaturated `NoCases`: `⟨⟩ → β`. -/
  | partialNoCases {ret τ} :
      Ty.TyEquiv (.fun (.union .empty) .empty ret) τ →
      HasTypeV (.Partial .NoCases []) τ
  /-- `Case l` with no args: the full match scheme
  `(inner →⟨e⟩ r) → (⟨tail⟩ →⟨e⟩ r) → (⟨l:inner|tail⟩ →⟨e⟩ r)`. -/
  | partialMatchNil {label inner eff ret tail τ} :
      Ty.TyEquiv (.fun (.fun inner eff ret) .empty
        (.fun (.fun (.union tail) eff ret) .empty
          (.fun (.union (.rowExtend label inner tail)) eff ret))) τ →
      HasTypeV (.Partial (.Match label) []) τ
  /-- `Case l` with the branch applied. -/
  | partialMatchOne {label branch inner eff ret tail τ} :
      HasTypeV branch (.fun inner eff ret) →
      Ty.TyEquiv (.fun (.fun (.union tail) eff ret) .empty
        (.fun (.union (.rowExtend label inner tail)) eff ret)) τ →
      HasTypeV (.Partial (.Match label) [branch]) τ
  /-- `Case l` with both branches applied: `⟨l:inner|tail⟩ →⟨e⟩ r`. -/
  | partialMatchTwo {label branch otherwise inner eff ret tail τ} :
      HasTypeV branch (.fun inner eff ret) →
      HasTypeV otherwise (.fun (.union tail) eff ret) →
      Ty.TyEquiv (.fun (.union (.rowExtend label inner tail)) eff ret) τ →
      HasTypeV (.Partial (.Match label) [branch, otherwise]) τ
  /-- A record value realizes a row by **first-occurrence membership**, in two
  `∃`-free clauses (so it nests legally): every row label is *present*, and every
  present value *matches* the row's visible field type. Both read the first
  occurrence, so the interpreter's sorted-unique records match scoped-row types
  even with shadowed duplicates. -/
  | record {fields row τ} :
      (∀ l f, Ty.RowContains row l f → recordGet fields l ≠ none) →
      (∀ l f v, Ty.RowContains row l f → recordGet fields l = some v → HasTypeV v f) →
      Ty.TyEquiv (.record row) τ → HasTypeV (.Record fields) τ
  /-- `Select l`: `∀α r. ⟨l:α|r⟩ → α` (`select(l) = pure1(Record(RowExtend l q0 q1), q0)`). -/
  | partialSelect {label fieldTy tail τ} :
      Ty.TyEquiv (.fun (.record (.rowExtend label fieldTy tail)) .empty fieldTy) τ →
      HasTypeV (.Partial (.Select label) []) τ
  /-- `Extend l` with no args: `∀α r. α → {r} → {l:α|r}`. -/
  | partialExtendNil {label fieldTy row τ} :
      Ty.TyEquiv (.fun fieldTy .empty
        (.fun (.record row) .empty (.record (.rowExtend label fieldTy row)))) τ →
      HasTypeV (.Partial (.Extend label) []) τ
  /-- `Extend l` with the field value applied: `{r} → {l:α|r}`. -/
  | partialExtendOne {label v fieldTy row τ} :
      HasTypeV v fieldTy →
      Ty.TyEquiv (.fun (.record row) .empty (.record (.rowExtend label fieldTy row))) τ →
      HasTypeV (.Partial (.Extend label) [v]) τ
  /-- `Overwrite l` with no args: `∀α β r. α → {l:β|r} → {l:α|r}`. -/
  | partialOverwriteNil {label newTy oldTy tail τ} :
      Ty.TyEquiv (.fun newTy .empty
        (.fun (.record (.rowExtend label oldTy tail)) .empty
          (.record (.rowExtend label newTy tail)))) τ →
      HasTypeV (.Partial (.Overwrite label) []) τ
  /-- `Overwrite l` with the new field value applied: `{l:β|r} → {l:α|r}`. -/
  | partialOverwriteOne {label v newTy oldTy tail τ} :
      HasTypeV v newTy →
      Ty.TyEquiv (.fun (.record (.rowExtend label oldTy tail)) .empty
        (.record (.rowExtend label newTy tail))) τ →
      HasTypeV (.Partial (.Overwrite label) [v]) τ

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
  | partialConsNil he => exact .partialConsNil (he.trans heq)
  | partialConsOne hh he => exact .partialConsOne hh (he.trans heq)
  | tagged hv he => exact .tagged hv (he.trans heq)
  | partialTag he => exact .partialTag (he.trans heq)
  | partialNoCases he => exact .partialNoCases (he.trans heq)
  | partialMatchNil he => exact .partialMatchNil (he.trans heq)
  | partialMatchOne hb he => exact .partialMatchOne hb (he.trans heq)
  | partialMatchTwo hb ho he => exact .partialMatchTwo hb ho (he.trans heq)
  | record hpres hmatch he => exact .record hpres hmatch (he.trans heq)
  | partialSelect he => exact .partialSelect (he.trans heq)
  | partialExtendNil he => exact .partialExtendNil (he.trans heq)
  | partialExtendOne hvf he => exact .partialExtendOne hvf (he.trans heq)
  | partialOverwriteNil he => exact .partialOverwriteNil (he.trans heq)
  | partialOverwriteOne hvf he => exact .partialOverwriteOne hvf (he.trans heq)

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

/-- **No value inhabits the empty union.** A tagged value's natural row is a
`rowExtend` (≠ `empty`), and every other value's natural type is not a union — so
the carried `TyEquiv` to `union empty` is impossible (head-shape mismatch under the
union row). This makes `NoCases` vacuously safe. -/
theorem canonical_union_empty {m : Type} {v : Value m}
    (h : HasTypeV v (.union .empty)) : False := by
  cases h <;> rename_i he <;>
    (have hs := Ty.tyEquiv_shape (Ty.tyEquiv_unionRow he); simp [Ty.shape, Ty.unionRow] at hs)

/-- A value at a union type is a `Tagged` value. -/
theorem canonical_union {m : Type} {v : Value m} {row : Ty} (h : HasTypeV v (.union row)) :
    ∃ label inner, v = .Tagged label inner := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, _, rfl⟩ | (have hs := Ty.tyEquiv_shape he; simp [Ty.shape] at hs)

/-- A value at a record type is a `Record` value. -/
theorem canonical_record {m : Type} {v : Value m} {row : Ty} (h : HasTypeV v (.record row)) :
    ∃ fields, v = .Record fields := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, rfl⟩ | (have hs := Ty.tyEquiv_shape he; simp [Ty.shape] at hs)

/-- **`Select` is safe**: from the two record clauses, `recordGet` finds the field
(present) and its value has the row's type (matches) — no `MissingField`. -/
theorem record_get {m : Type} {fields : List (String × Value m)} {row : Ty} {l : String}
    {f : Ty}
    (hpres : ∀ l f, Ty.RowContains row l f → recordGet fields l ≠ none)
    (hmatch : ∀ l f v, Ty.RowContains row l f → recordGet fields l = some v → HasTypeV v f)
    (hc : Ty.RowContains row l f) : ∃ v, recordGet fields l = some v ∧ HasTypeV v f := by
  cases hg : recordGet fields l with
  | none => exact absurd hg (hpres l f hc)
  | some v => exact ⟨v, rfl, hmatch l f v hc hg⟩

/-- Inserting `l ↦ v` makes `recordGet … l = v` (the sorted-insert ↔ lookup hinge). -/
theorem recordInsert_get_eq {m : Type} (fields : List (String × Value m)) (l : String)
    (v : Value m) : recordGet (recordInsert fields l v) l = some v := by
  induction fields with
  | nil => simp [recordInsert, recordGet]
  | cons hd rest ih =>
      obtain ⟨k, vk⟩ := hd
      simp only [recordInsert]
      split
      · simp [recordGet]
      · next h1 =>
          split
          · simp [recordGet]
          · simp only [recordGet]
            split
            · next hh => exact absurd hh h1
            · exact ih

/-- Inserting `l ↦ v` leaves `recordGet … l'` unchanged for `l' ≠ l`. -/
theorem recordInsert_get_ne {m : Type} (fields : List (String × Value m)) {l l' : String}
    (v : Value m) (hne : (l' == l) = false) :
    recordGet (recordInsert fields l v) l' = recordGet fields l' := by
  induction fields with
  | nil => simp [recordInsert, recordGet, hne]
  | cons hd rest ih =>
      obtain ⟨k, vk⟩ := hd
      simp only [recordInsert]
      split
      · next hlk => obtain rfl := eq_of_beq hlk; simp [recordGet, hne]
      · split
        · simp [recordGet, hne]
        · simp only [recordGet]
          split
          · rfl
          · exact ih

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
  | partialTag _ => exact Or.inr ⟨_, _, rfl⟩
  | partialNoCases _ => exact Or.inr ⟨_, _, rfl⟩
  | partialMatchNil _ => exact Or.inr ⟨_, _, rfl⟩
  | partialMatchOne _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialMatchTwo _ _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialSelect _ => exact Or.inr ⟨_, _, rfl⟩
  | partialExtendNil _ => exact Or.inr ⟨_, _, rfl⟩
  | partialExtendOne _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialOverwriteNil _ => exact Or.inr ⟨_, _, rfl⟩
  | partialOverwriteOne _ _ => exact Or.inr ⟨_, _, rfl⟩
  | record _ _ he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | tagged _ he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | int he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | str he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | bin he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | listNil he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | listCons _ _ he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc

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
