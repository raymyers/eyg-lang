import Eyg.Types.Machine
import Eyg.Types.Generation
import Eyg.Semantics.BehaviorR

/-!
# Type soundness for the pure core — preservation (Milestone T3c-ii)

`preservation`: a well-typed machine state stays well-typed under `Reduce`. Proved
over the transparent `Reduce`/`reduce1Run` (T0), by the recipe validated in
`progress/2026-06-16-T3c-preservation-design.md`. This file builds it up case by
case; the builtin **saturation** step (`reduceCallBuiltin` running `Builtin.run`)
is the T6 obligation and is isolated behind `reduceCall`.
-/

namespace Eyg.Types

open Eyg.Interpreter
open Eyg.Ir
open Eyg.Semantics

variable {m : Type}

/-! ## Preservation across the value-production `eval` steps

For a control `.E e` that `reduceEval` turns into a value (`Lambda`, the literals),
the successor is `.V <value>` with the same stack; the value is typed at exactly
the stack's expected incoming type using the generation lemma's `TyEquiv` directly
in the value constructor. -/

/-- Unfold `MStateWf` on a running `.E` state. -/
theorem mStateWf_E {e : Tree.Node m} {env k τ ε}
    (h : MStateWf (.run (.E e, env, k)) τ ε) :
    ∃ Γ τin, EnvWf env Γ ∧ HasType Γ e τin ε ∧ StackWf k τin ε τ := h

/-- Unfold `MStateWf` on a running `.V` state. -/
theorem mStateWf_V {v : Value m} {env k τ ε}
    (h : MStateWf (.run (.V v, env, k)) τ ε) :
    ∃ τin, HasTypeV v τin ∧ StackWf k τin ε τ := h

/-- A crash reason `soundness` must exclude. `Unrepresentable` is the one
*sanctioned* runtime trap (a JS-safe-range overflow — see the plan's crash list and
`break.gleam`), so it is **not** bad; every type-error crash is. -/
def Reason.IsBad : Reason m → Prop
  | .Unrepresentable _ _ => False
  | _ => True

/-- The analyzer's builtin table is contained in the interpreter's: a typed
`Builtin id` is a real builtin, so its node evaluates (no `UndefinedBuiltin`). -/
theorem builtin_scheme_isBuiltin {id : String} {s : Scheme}
    (h : Builtins.scheme id = some s) : isBuiltin id = true := by
  unfold Builtins.scheme at h
  split at h <;> first | decide | simp_all

/-- Every builtin scheme instantiates to an arrow (builtins are functions), so a
freshly-evaluated `Builtin` node (`Partial (Builtin id) []`) types at a residual
arrow via `BuiltinPartialWf.nil`. -/
theorem builtin_instantiate_arrow {id : String} {s : Scheme} (args : List Ty)
    (h : Builtins.scheme id = some s) : ∃ a e r, s.instantiate args = .fun a e r := by
  unfold Builtins.scheme at h
  split at h <;>
    first
      | (obtain rfl := Option.some.inj h; exact ⟨_, _, _, rfl⟩)
      | exact absurd h (by simp)

/-- A well-typed stack carries **no `Delimit` frame** (none of `StackWf`'s six
frame constructors is `Delimit` — until `Handle`/`Delimit` typing lands in the next
T5 slice). Hence the transparent stack walk `doPerformR` traverses it to the end and
reports the effect **unhandled**: every well-typed `perform` escapes to the
boundary. Structural induction on `StackWf` (each frame is the non-`Delimit`
catch-all of `doPerformR`, so it recurses on the tail). This is what makes effect
safety provable — `doPerformR` is transparent (T5b), so this computes. -/
theorem stackWf_doPerformR_unhandled [BEq m] {k : Stack m} {σ ε τ : Ty}
    (hst : StackWf k σ ε τ) :
    ∀ (label : String) (arg : Value m) (env : Env m) acc,
      doPerformR label arg env k acc = .error (.UnhandledEffect label arg) := by
  induction hst with
  | nil => intro label arg env acc; rfl
  | trace _ ih => intro label arg env acc; exact ih _ _ _ _
  | assign _ _ _ ih => intro label arg env acc; exact ih _ _ _ _
  | arg _ _ _ ih => intro label arg env acc; exact ih _ _ _ _
  | applyf _ _ ih => intro label arg env acc; exact ih _ _ _ _
  | callwith _ _ ih => intro label arg env acc; exact ih _ _ _ _

/-- Preservation across an `.E`-control (`reduceEval`) step. -/
theorem preservation_E [BEq m] {e : Tree.Node m} {env : Env m} {k : Stack m}
    {cfg' : Config m} {τ ε : Ty}
    (hwf : MStateWf (.run (.E e, env, k)) τ ε)
    (hr : reduce1Run (.E e, env, k) = .tau cfg') :
    MStateWf (.run cfg') τ ε := by
  obtain ⟨Γ, τin, henv, hty, hst⟩ := mStateWf_E hwf
  obtain ⟨expr, ann⟩ := e
  cases expr with
  | Integer n =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      exact ⟨τin, HasTypeV.int (inv_int hty), hst⟩
  | String s =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      exact ⟨τin, HasTypeV.str (inv_str hty), hst⟩
  | Binary b =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      exact ⟨τin, HasTypeV.bin (inv_bin hty), hst⟩
  | Lambda x body =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨argTy, εb, retTy, hbody, heq⟩ := inv_lambda hty
      exact ⟨τin, HasTypeV.closure henv hbody heq, hst⟩
  | Variable x =>
      obtain ⟨s, args, hlookup, heq⟩ := inv_var hty
      obtain ⟨v, hvlk, hvty⟩ := envwf_lookup henv hlookup
      simp only [reduce1Run, reduceEval, hvlk] at hr; cases hr
      exact ⟨τin, (hvty args).conv heq, hst⟩
  | Apply f arg =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨argTy, hf, harg⟩ := inv_app hty
      exact ⟨Γ, _, henv, hf, StackWf.arg henv harg hst⟩
  | Let x defn body =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨defnTy, hdefn, hbody⟩ := inv_let hty
      exact ⟨Γ, defnTy, henv, hdefn, StackWf.assign henv hbody hst⟩
  | Builtin id =>
      obtain ⟨s, args, hs, heq⟩ := inv_builtin hty
      obtain ⟨a, e, r, harrow⟩ := builtin_instantiate_arrow args hs
      rw [harrow] at heq
      simp only [reduce1Run, reduceEval] at hr
      split at hr
      · cases hr
        refine ⟨τin, HasTypeV.partialBuiltin (args := args) hs ?_ heq, hst⟩
        rw [harrow]; exact BuiltinPartialWf.nil
      · exact absurd hr (by simp)
  | Tail =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨elem, heq⟩ := inv_tail hty
      exact ⟨τin, HasTypeV.listNil heq, hst⟩
  | Empty =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      exact ⟨τin, HasTypeV.record (fun _ _ hc => by cases hc) (fun _ _ _ hc _ => by cases hc)
        (inv_empty hty), hst⟩
  | Cons =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨elem, heq⟩ := inv_cons hty
      exact ⟨τin, HasTypeV.partialConsNil heq, hst⟩
  | Tag l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨elem, tail, heq⟩ := inv_tag hty
      exact ⟨τin, HasTypeV.partialTag heq, hst⟩
  | NoCases =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨ret, heq⟩ := inv_nocases hty
      exact ⟨τin, HasTypeV.partialNoCases heq, hst⟩
  | Case l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨inner, eff, ret, tail, heq⟩ := inv_case hty
      exact ⟨τin, HasTypeV.partialMatchNil heq, hst⟩
  | Select l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨fieldTy, tail, heq⟩ := inv_select hty
      exact ⟨τin, HasTypeV.partialSelect heq, hst⟩
  | Extend l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨fieldTy, row, heq⟩ := inv_extend hty
      exact ⟨τin, HasTypeV.partialExtendNil heq, hst⟩
  | Overwrite l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨newTy, oldTy, tail, heq⟩ := inv_overwrite hty
      exact ⟨τin, HasTypeV.partialOverwriteNil heq, hst⟩
  | Perform l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨argTy, replyTy, μ, heq⟩ := inv_perform hty
      exact ⟨τin, HasTypeV.partialPerformNil heq, hst⟩
  | _ =>
      exfalso
      rcases hasType_expr_form hty with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ |
        ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h | h | h | ⟨_, h⟩ | h | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h

/-! ## T6 — per-builtin `Builtin.run` typing (the saturation obligation, in progress)

The isolated `BuiltinAppPreserves`/`BuiltinAppNoBadCrash` hypotheses are discharged by
proving, per builtin, that `Builtin.run` applied to arguments of the builtin's scheme
domains yields a value of its scheme codomain (or a *sanctioned* `Unrepresentable`
trap). These are mechanical — extract the typed args with the canonical-forms lemmas,
compute `run`, type the result. A representative subset is proved here (arithmetic /
string core); the full table + assembly into `BuiltinAppPreserves` is the rest of T6. -/

/-- `int_to_string : Integer → String`. -/
theorem run_int_to_string [BEq m] {a v : Value m} (ha : HasTypeV a .integer)
    (h : Builtin.run "int_to_string" [a] = .ok v) : HasTypeV v .string := by
  obtain ⟨x, rfl⟩ := canonical_integer ha
  simp only [Builtin.run, Cast.asInteger, bind, Except.bind] at h
  cases h; exact HasTypeV.str (.refl _)

/-- `int_add : Integer → Integer → Integer` (or the sanctioned `Unrepresentable` trap). -/
theorem run_int_add [BEq m] {a b v : Value m}
    (ha : HasTypeV a .integer) (hb : HasTypeV b .integer)
    (h : Builtin.run "int_add" [a, b] = .ok v) : HasTypeV v .integer := by
  obtain ⟨x, rfl⟩ := canonical_integer ha
  obtain ⟨y, rfl⟩ := canonical_integer hb
  simp only [Builtin.run, Cast.asInteger, bind, Except.bind] at h
  split at h
  · cases h; exact HasTypeV.int (.refl _)
  · exact absurd h (by simp)

/-- `int_add`'s only failure is the sanctioned `Unrepresentable`. -/
theorem run_int_add_noBad [BEq m] {a b : Value m} {e : Reason m}
    (ha : HasTypeV a .integer) (hb : HasTypeV b .integer)
    (h : Builtin.run "int_add" [a, b] = .error e) : ¬ Reason.IsBad e := by
  obtain ⟨x, rfl⟩ := canonical_integer ha
  obtain ⟨y, rfl⟩ := canonical_integer hb
  simp only [Builtin.run, Cast.asInteger, bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · cases h; simp [Reason.IsBad]

/-- `int_subtract`'s only failure is the sanctioned `Unrepresentable`. -/
theorem run_int_subtract_noBad [BEq m] {a b : Value m} {e : Reason m}
    (ha : HasTypeV a .integer) (hb : HasTypeV b .integer)
    (h : Builtin.run "int_subtract" [a, b] = .error e) : ¬ Reason.IsBad e := by
  obtain ⟨x, rfl⟩ := canonical_integer ha; obtain ⟨y, rfl⟩ := canonical_integer hb
  simp only [Builtin.run, Cast.asInteger, bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · cases h; simp [Reason.IsBad]

/-- `int_multiply`'s only failure is the sanctioned `Unrepresentable`. -/
theorem run_int_multiply_noBad [BEq m] {a b : Value m} {e : Reason m}
    (ha : HasTypeV a .integer) (hb : HasTypeV b .integer)
    (h : Builtin.run "int_multiply" [a, b] = .error e) : ¬ Reason.IsBad e := by
  obtain ⟨x, rfl⟩ := canonical_integer ha; obtain ⟨y, rfl⟩ := canonical_integer hb
  simp only [Builtin.run, Cast.asInteger, bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · cases h; simp [Reason.IsBad]

/-- `int_parse`'s only failure is the sanctioned `Unrepresentable`. -/
theorem run_int_parse_noBad [BEq m] {a : Value m} {e : Reason m} (ha : HasTypeV a .string)
    (h : Builtin.run "int_parse" [a] = .error e) : ¬ Reason.IsBad e := by
  obtain ⟨s, rfl⟩ := canonical_string ha
  simp only [Builtin.run, Cast.asString, bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · cases h; simp [Reason.IsBad]

/-- `string_append : String → String → String`. -/
theorem run_string_append [BEq m] {a b v : Value m}
    (ha : HasTypeV a .string) (hb : HasTypeV b .string)
    (h : Builtin.run "string_append" [a, b] = .ok v) : HasTypeV v .string := by
  obtain ⟨x, rfl⟩ := canonical_string ha
  obtain ⟨y, rfl⟩ := canonical_string hb
  simp only [Builtin.run, Cast.asString, bind, Except.bind] at h
  cases h; exact HasTypeV.str (.refl _)

/-- `string_length : String → Integer`. -/
theorem run_string_length [BEq m] {a v : Value m} (ha : HasTypeV a .string)
    (h : Builtin.run "string_length" [a] = .ok v) : HasTypeV v .integer := by
  obtain ⟨s, rfl⟩ := canonical_string ha
  simp only [Builtin.run, Cast.asString, bind, Except.bind] at h
  cases h; exact HasTypeV.int (.refl _)

/-- The unit value inhabits the unit (empty record) type. -/
theorem hasTypeV_unit [BEq m] : HasTypeV (Eyg.Interpreter.unit : Value m) Ty.unit := by
  refine HasTypeV.record ?_ ?_ (.refl _)
  · intro l f hc; cases hc
  · intro l f v hc hg; cases hc

/-- A boolean value inhabits the `boolean` union type. -/
theorem hasTypeV_bool [BEq m] (b : Bool) : HasTypeV (Eyg.Interpreter.bool b : Value m) Ty.boolean := by
  cases b with
  | true =>
      refine HasTypeV.tagged (tail := .rowExtend "False" Ty.unit .empty) hasTypeV_unit ?_
      simp only [Ty.boolean, Ty.union', Ty.rows]; exact .refl _
  | false =>
      refine HasTypeV.tagged (tail := .rowExtend "True" Ty.unit .empty) hasTypeV_unit ?_
      simp only [Ty.boolean, Ty.union', Ty.rows]
      exact Ty.TyEquiv.congrUnion
        (Ty.TyEquiv.swapRow (l := "False") (l' := "True") (f := Ty.unit) (f' := Ty.unit)
          (t := .empty) (by decide))

/-- `int_subtract : Integer → Integer → Integer` (or `Unrepresentable`). -/
theorem run_int_subtract [BEq m] {a b v : Value m}
    (ha : HasTypeV a .integer) (hb : HasTypeV b .integer)
    (h : Builtin.run "int_subtract" [a, b] = .ok v) : HasTypeV v .integer := by
  obtain ⟨x, rfl⟩ := canonical_integer ha; obtain ⟨y, rfl⟩ := canonical_integer hb
  simp only [Builtin.run, Cast.asInteger, bind, Except.bind] at h
  split at h
  · cases h; exact HasTypeV.int (.refl _)
  · exact absurd h (by simp)

/-- `int_multiply : Integer → Integer → Integer` (or `Unrepresentable`). -/
theorem run_int_multiply [BEq m] {a b v : Value m}
    (ha : HasTypeV a .integer) (hb : HasTypeV b .integer)
    (h : Builtin.run "int_multiply" [a, b] = .ok v) : HasTypeV v .integer := by
  obtain ⟨x, rfl⟩ := canonical_integer ha; obtain ⟨y, rfl⟩ := canonical_integer hb
  simp only [Builtin.run, Cast.asInteger, bind, Except.bind] at h
  split at h
  · cases h; exact HasTypeV.int (.refl _)
  · exact absurd h (by simp)

/-- `int_absolute : Integer → Integer`. -/
theorem run_int_absolute [BEq m] {a v : Value m} (ha : HasTypeV a .integer)
    (h : Builtin.run "int_absolute" [a] = .ok v) : HasTypeV v .integer := by
  obtain ⟨x, rfl⟩ := canonical_integer ha
  simp only [Builtin.run, Cast.asInteger, bind, Except.bind] at h
  cases h; exact HasTypeV.int (.refl _)

/-- `string_uppercase : String → String`. -/
theorem run_string_uppercase [BEq m] {a v : Value m} (ha : HasTypeV a .string)
    (h : Builtin.run "string_uppercase" [a] = .ok v) : HasTypeV v .string := by
  obtain ⟨s, rfl⟩ := canonical_string ha
  simp only [Builtin.run, Cast.asString, bind, Except.bind] at h
  cases h; exact HasTypeV.str (.refl _)

/-- `string_lowercase : String → String`. -/
theorem run_string_lowercase [BEq m] {a v : Value m} (ha : HasTypeV a .string)
    (h : Builtin.run "string_lowercase" [a] = .ok v) : HasTypeV v .string := by
  obtain ⟨s, rfl⟩ := canonical_string ha
  simp only [Builtin.run, Cast.asString, bind, Except.bind] at h
  cases h; exact HasTypeV.str (.refl _)

/-- `equal : α → α → Boolean` (the result type is `boolean` regardless of the args). -/
theorem run_equal [BEq m] {a b v : Value m}
    (h : Builtin.run "equal" [a, b] = .ok v) : HasTypeV v Ty.boolean := by
  simp only [Builtin.run] at h; cases h; exact hasTypeV_bool _

/-- `string_starts_with : String → String → Boolean`. -/
theorem run_string_starts_with [BEq m] {a b v : Value m}
    (ha : HasTypeV a .string) (hb : HasTypeV b .string)
    (h : Builtin.run "string_starts_with" [a, b] = .ok v) : HasTypeV v Ty.boolean := by
  obtain ⟨x, rfl⟩ := canonical_string ha; obtain ⟨y, rfl⟩ := canonical_string hb
  simp only [Builtin.run, Cast.asString, bind, Except.bind] at h
  cases h; exact hasTypeV_bool _

/-- `string_ends_with : String → String → Boolean`. -/
theorem run_string_ends_with [BEq m] {a b v : Value m}
    (ha : HasTypeV a .string) (hb : HasTypeV b .string)
    (h : Builtin.run "string_ends_with" [a, b] = .ok v) : HasTypeV v Ty.boolean := by
  obtain ⟨x, rfl⟩ := canonical_string ha; obtain ⟨y, rfl⟩ := canonical_string hb
  simp only [Builtin.run, Cast.asString, bind, Except.bind] at h
  cases h; exact hasTypeV_bool _

/-- `Ok v` inhabits `result a b` when `v : a`. -/
theorem hasTypeV_ok [BEq m] {v : Value m} {a b : Ty} (hv : HasTypeV v a) :
    HasTypeV (Eyg.Interpreter.ok v) (Ty.result a b) := by
  refine HasTypeV.tagged (tail := .rowExtend "Error" b .empty) hv ?_
  simp only [Ty.result, Ty.union', Ty.rows]; exact .refl _

/-- `Error v` inhabits `result a b` when `v : b`. -/
theorem hasTypeV_error [BEq m] {v : Value m} {a b : Ty} (hv : HasTypeV v b) :
    HasTypeV (Eyg.Interpreter.error v) (Ty.result a b) := by
  refine HasTypeV.tagged (tail := .rowExtend "Ok" a .empty) hv ?_
  simp only [Ty.result, Ty.union', Ty.rows]
  exact Ty.TyEquiv.congrUnion
    (Ty.TyEquiv.swapRow (l := "Error") (l' := "Ok") (f := b) (f' := a) (t := .empty) (by decide))

/-- An `ordTag` value inhabits `Builtins.intCompareResult`. -/
theorem hasTypeV_ordTag [BEq m] (o : Ordering) :
    HasTypeV (Builtin.ordTag o : Value m) Builtins.intCompareResult := by
  cases o with
  | lt =>
      refine HasTypeV.tagged
        (tail := .rowExtend "Eq" Ty.unit (.rowExtend "Gt" Ty.unit .empty)) hasTypeV_unit ?_
      simp only [Builtins.intCompareResult, Ty.union', Ty.rows]; exact .refl _
  | eq =>
      refine HasTypeV.tagged
        (tail := .rowExtend "Lt" Ty.unit (.rowExtend "Gt" Ty.unit .empty)) hasTypeV_unit ?_
      simp only [Builtins.intCompareResult, Ty.union', Ty.rows]
      exact Ty.TyEquiv.congrUnion
        (Ty.TyEquiv.swapRow (l := "Eq") (l' := "Lt") (f := Ty.unit) (f' := Ty.unit)
          (t := .rowExtend "Gt" Ty.unit .empty) (by decide))
  | gt =>
      refine HasTypeV.tagged
        (tail := .rowExtend "Lt" Ty.unit (.rowExtend "Eq" Ty.unit .empty)) hasTypeV_unit ?_
      simp only [Builtins.intCompareResult, Ty.union', Ty.rows]
      refine (Ty.TyEquiv.congrUnion (Ty.TyEquiv.swapRow (l := "Gt") (l' := "Lt")
        (f := Ty.unit) (f' := Ty.unit) (t := .rowExtend "Eq" Ty.unit .empty) (by decide))).trans ?_
      exact Ty.TyEquiv.congrUnion (Ty.TyEquiv.congrRow (.refl _)
        (Ty.TyEquiv.swapRow (l := "Gt") (l' := "Eq") (f := Ty.unit) (f' := Ty.unit)
          (t := .empty) (by decide)))

/-- `int_compare : Integer → Integer → Builtins.intCompareResult`. -/
theorem run_int_compare [BEq m] {a b v : Value m}
    (ha : HasTypeV a .integer) (hb : HasTypeV b .integer)
    (h : Builtin.run "int_compare" [a, b] = .ok v) : HasTypeV v Builtins.intCompareResult := by
  obtain ⟨x, rfl⟩ := canonical_integer ha; obtain ⟨y, rfl⟩ := canonical_integer hb
  simp only [Builtin.run, Cast.asInteger, bind, Except.bind] at h
  cases h; exact hasTypeV_ordTag _

/-- `int_divide : Integer → Integer → result Integer Unit`. -/
theorem run_int_divide [BEq m] {a b v : Value m}
    (ha : HasTypeV a .integer) (hb : HasTypeV b .integer)
    (h : Builtin.run "int_divide" [a, b] = .ok v) : HasTypeV v (Ty.result .integer Ty.unit) := by
  obtain ⟨x, rfl⟩ := canonical_integer ha; obtain ⟨y, rfl⟩ := canonical_integer hb
  simp only [Builtin.run, Cast.asInteger, bind, Except.bind] at h
  cases h
  split
  · exact hasTypeV_error hasTypeV_unit
  · exact hasTypeV_ok (HasTypeV.int (.refl _))

/-- `int_parse : String → result Integer Unit` (or the sanctioned `Unrepresentable`). -/
theorem run_int_parse [BEq m] {a v : Value m} (ha : HasTypeV a .string)
    (h : Builtin.run "int_parse" [a] = .ok v) : HasTypeV v (Ty.result .integer Ty.unit) := by
  obtain ⟨s, rfl⟩ := canonical_string ha
  simp only [Builtin.run, Cast.asString, bind, Except.bind] at h
  split at h
  · cases h; exact hasTypeV_error hasTypeV_unit
  · split at h
    · cases h; exact hasTypeV_ok (HasTypeV.int (.refl _))
    · exact absurd h (by simp)

/-- The builtin **application/saturation** preservation obligation, isolated as a
hypothesis (the **T6** deliverable — it needs the per-builtin `Builtin.run` typing,
and `int_add` may legitimately trap with the sanctioned `Unrepresentable`). When a
typed `Partial (Builtin id)` is applied to a typed argument and the machine takes a
`tau` step (i.e. the builtin did *not* crash), the successor stays well-typed. -/
def BuiltinAppPreserves (m : Type) [BEq m] : Prop :=
  ∀ {id : String} {applied : List (Value m)} {arg : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {argTy retTy ε τ : Ty},
    HasTypeV (.Partial (.Builtin id) applied) (.fun argTy ε retTy) →
    HasTypeV arg argTy →
    StackWf rest retTy ε τ →
    (∀ cfg', reduceCall (.Partial (.Builtin id) applied) arg ann fenv rest = .tau cfg' →
        MStateWf (.run cfg') τ ε) ∧
    (∀ v, reduceCall (.Partial (.Builtin id) applied) arg ann fenv rest = .done (.value v) →
        HasTypeV v τ)

/-- Preservation across a `.V`-control (`reduceApply` frame) step. The closure
application case is the crux; the builtin-application case defers to `hsat`. -/
theorem preservation_V [BEq m] (hsat : BuiltinAppPreserves m)
    {v : Value m} {env : Env m} {kont : Kontinue m} {ann : m} {rest : Stack m}
    {cfg' : Config m} {τ ε : Ty}
    (hwf : MStateWf (.run (.V v, env, (kont, ann) :: rest)) τ ε)
    (hr : reduce1Run (.V v, env, (kont, ann) :: rest) = .tau cfg') :
    MStateWf (.run cfg') τ ε := by
  obtain ⟨τin, hv, hst⟩ := mStateWf_V hwf
  cases hst with
  | trace hrest =>
      simp only [reduce1Run, reduceApply] at hr; cases hr
      exact ⟨τin, hv, hrest⟩
  | assign henvc hbody hrest =>
      simp only [reduce1Run, reduceApply] at hr; cases hr
      refine ⟨_, _, EnvWf.cons (fun args => ?_) henvc, hbody, hrest⟩
      simpa using hv
  | arg henvc harg hrest =>
      simp only [reduce1Run, reduceApply] at hr; cases hr
      exact ⟨_, _, henvc, harg, StackWf.applyf hv hrest⟩
  | applyf hf hrest =>
      rcases canonical_arrow hf with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
      · cases hf with
        | closure henvc hbody heqc =>
            obtain ⟨hA, hE, hR⟩ := Ty.tyEquiv_fun_components heqc
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            refine ⟨_, _, EnvWf.cons (fun args => ?_) henvc,
              HasType.conv hbody hR hE, StackWf.trace hrest⟩
            simpa using hv.conv hA.symm
      · cases hf with
        | partialBuiltin hs hp he =>
            simp only [reduce1Run, reduceApply] at hr
            exact (hsat (.partialBuiltin hs hp he) hv hrest).1 _ hr
        | partialConsNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.partialConsOne (hv.conv hA.symm) hR, hrest⟩
        | partialConsOne hh he =>
            obtain ⟨hD, _, hR⟩ := Ty.tyEquiv_fun_components he
            have hvl := hv.conv hD.symm
            obtain ⟨es, rfl⟩ := canonical_list hvl
            simp only [reduce1Run, reduceApply, reduceCall, Cast.asList] at hr; cases hr
            exact ⟨_, HasTypeV.listCons hh hvl hR, hrest⟩
        | partialTag he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.tagged (hv.conv hA.symm) hR, hrest⟩
        | partialNoCases he =>
            obtain ⟨hA, _, _⟩ := Ty.tyEquiv_fun_components he
            exact absurd (hv.conv hA.symm) canonical_union_empty
        | partialMatchNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.partialMatchOne (hv.conv hA.symm) hR, hrest⟩
        | partialMatchOne hbranch he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.partialMatchTwo hbranch (hv.conv hA.symm) hR, hrest⟩
        | @partialMatchTwo lbl _ _ inner eff ret tail1 _ hbranch hotherwise he =>
            obtain ⟨hD, hEff, hRet⟩ := Ty.tyEquiv_fun_components he
            have hvu := hv.conv hD.symm
            obtain ⟨vl, vp, rfl⟩ := canonical_union hvu
            cases hvu with
            | tagged hvp hetag =>
                obtain ⟨f', hcontains, hf'⟩ :=
                  Ty.tyEquiv_rowContains_mp (Ty.tyEquiv_unionRow hetag) Ty.RowContains.head
                simp only [reduce1Run, reduceApply, reduceCall, Cast.asTagged] at hr
                split at hr
                · -- hit: the tag equals the matched label, so `f' = inner`
                  rename_i hcond; cases hr
                  obtain rfl := eq_of_beq hcond
                  cases hcontains with
                  | head =>
                      exact ⟨_, hvp.conv hf',
                        StackWf.applyf (hbranch.conv (.congrFun (.refl _) hEff hRet)) hrest⟩
                  | tail hne _ => exact absurd rfl hne
                · -- miss: the tag is in the tail, so the value inhabits `union tail`
                  rename_i hcond; cases hr
                  have hvlne : vl ≠ lbl := fun h => by subst h; simp at hcond
                  cases hcontains with
                  | head => exact absurd rfl hvlne
                  | tail _ hc'' =>
                      obtain ⟨rest', htail⟩ := Ty.rowContains_tyEquiv hc''
                      exact ⟨_, HasTypeV.tagged (hvp.conv hf') (Ty.TyEquiv.congrUnion htail),
                        StackWf.applyf (hotherwise.conv (.congrFun (.refl _) hEff hRet)) hrest⟩
        | @partialSelect lbl fieldTy tail _ he =>
            obtain ⟨hD, _, hRet⟩ := Ty.tyEquiv_fun_components he
            have hvr := hv.conv hD.symm
            obtain ⟨fields, rfl⟩ := canonical_record hvr
            cases hvr with
            | record hpres hmatch hetag =>
                obtain ⟨f', hcont, hf'⟩ :=
                  (Ty.tyEquiv_rowContains (Ty.tyEquiv_recordRow hetag)).2 _ _ Ty.RowContains.head
                obtain ⟨value, hget, hvalue⟩ := record_get hpres hmatch hcont
                simp only [reduce1Run, reduceApply, reduceCall, Cast.asRecord, hget] at hr; cases hr
                exact ⟨_, hvalue.conv (hf'.symm.trans hRet), hrest⟩
        | partialExtendNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.partialExtendOne (hv.conv hA.symm) hR, hrest⟩
        | @partialExtendOne lbl _ fieldTy row _ hvf he =>
            obtain ⟨hD, _, hRet⟩ := Ty.tyEquiv_fun_components he
            have hvr := hv.conv hD.symm
            obtain ⟨fields, rfl⟩ := canonical_record hvr
            cases hvr with
            | record hpres hmatch hetag =>
                simp only [reduce1Run, reduceApply, reduceCall, Cast.asRecord] at hr; cases hr
                refine ⟨_, HasTypeV.record ?_ ?_ hRet, hrest⟩
                · intro l' f' hc
                  cases hc with
                  | head => rw [recordInsert_get_eq]; simp
                  | tail hne hc' =>
                      rw [recordInsert_get_ne _ _ (by simp [hne])]
                      obtain ⟨f'', hc'', _⟩ :=
                        (Ty.tyEquiv_rowContains (Ty.tyEquiv_recordRow hetag)).2 _ _ hc'
                      exact hpres l' f'' hc''
                · intro l' f' v' hc hg
                  cases hc with
                  | head =>
                      rw [recordInsert_get_eq] at hg
                      simp only [Option.some.injEq] at hg; subst hg; exact hvf
                  | tail hne hc' =>
                      rw [recordInsert_get_ne _ _ (by simp [hne])] at hg
                      obtain ⟨f'', hc'', heqf⟩ :=
                        (Ty.tyEquiv_rowContains (Ty.tyEquiv_recordRow hetag)).2 _ _ hc'
                      exact (hmatch l' f'' v' hc'' hg).conv heqf.symm
        | partialOverwriteNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.partialOverwriteOne (hv.conv hA.symm) hR, hrest⟩
        | @partialOverwriteOne lbl _ newTy oldTy tail _ hvf he =>
            obtain ⟨hD, _, hRet⟩ := Ty.tyEquiv_fun_components he
            have hvr := hv.conv hD.symm
            obtain ⟨fields, rfl⟩ := canonical_record hvr
            cases hvr with
            | record hpres hmatch hetag =>
                obtain ⟨_, hcontH, _⟩ := (Ty.tyEquiv_rowContains
                  (Ty.tyEquiv_recordRow hetag)).2 _ _ Ty.RowContains.head
                obtain ⟨_, hget, _⟩ := record_get hpres hmatch hcontH
                simp only [reduce1Run, reduceApply, reduceCall, Cast.asRecord, hget] at hr
                cases hr
                refine ⟨_, HasTypeV.record ?_ ?_ hRet, hrest⟩
                · intro l' f' hc
                  cases hc with
                  | head => rw [recordInsert_get_eq]; simp
                  | tail hne hc' =>
                      rw [recordInsert_get_ne _ _ (by simp [hne])]
                      obtain ⟨f'', hc'', _⟩ := (Ty.tyEquiv_rowContains
                        (Ty.tyEquiv_recordRow hetag)).2 _ _ (Ty.RowContains.tail hne hc')
                      exact hpres l' f'' hc''
                · intro l' f' v' hc hg
                  cases hc with
                  | head =>
                      rw [recordInsert_get_eq] at hg
                      simp only [Option.some.injEq] at hg; subst hg; exact hvf
                  | tail hne hc' =>
                      rw [recordInsert_get_ne _ _ (by simp [hne])] at hg
                      obtain ⟨f'', hc'', heqf⟩ := (Ty.tyEquiv_rowContains
                        (Ty.tyEquiv_recordRow hetag)).2 _ _ (Ty.RowContains.tail hne hc')
                      exact (hmatch l' f'' v' hc'' hg).conv heqf.symm
        | partialPerformNil _ =>
            -- the perform partial `reduceCall`s to `.perform` (the stack has no
            -- `Delimit`, so `doPerformR` reports unhandled), never a `.tau` step
            simp only [reduce1Run, reduceApply, reduceCall, reducePerform,
              stackWf_doPerformR_unhandled hrest] at hr
            exact absurd hr (by simp)
  | callwith harg hrest =>
      rcases canonical_arrow hv with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
      · cases hv with
        | closure henvc hbody heqc =>
            obtain ⟨hA, hE, hR⟩ := Ty.tyEquiv_fun_components heqc
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            refine ⟨_, _, EnvWf.cons (fun args => ?_) henvc,
              HasType.conv hbody hR hE, StackWf.trace hrest⟩
            simpa using harg.conv hA.symm
      · cases hv with
        | partialBuiltin hs hp he =>
            simp only [reduce1Run, reduceApply] at hr
            exact (hsat (.partialBuiltin hs hp he) harg hrest).1 _ hr
        | partialConsNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.partialConsOne (harg.conv hA.symm) hR, hrest⟩
        | partialConsOne hh he =>
            obtain ⟨hD, _, hR⟩ := Ty.tyEquiv_fun_components he
            have hvl := harg.conv hD.symm
            obtain ⟨es, rfl⟩ := canonical_list hvl
            simp only [reduce1Run, reduceApply, reduceCall, Cast.asList] at hr; cases hr
            exact ⟨_, HasTypeV.listCons hh hvl hR, hrest⟩
        | partialTag he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.tagged (harg.conv hA.symm) hR, hrest⟩
        | partialNoCases he =>
            obtain ⟨hA, _, _⟩ := Ty.tyEquiv_fun_components he
            exact absurd (harg.conv hA.symm) canonical_union_empty
        | partialMatchNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.partialMatchOne (harg.conv hA.symm) hR, hrest⟩
        | partialMatchOne hbranch he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.partialMatchTwo hbranch (harg.conv hA.symm) hR, hrest⟩
        | @partialMatchTwo lbl _ _ inner eff ret tail1 _ hbranch hotherwise he =>
            obtain ⟨hD, hEff, hRet⟩ := Ty.tyEquiv_fun_components he
            have hvu := harg.conv hD.symm
            obtain ⟨vl, vp, rfl⟩ := canonical_union hvu
            cases hvu with
            | tagged hvp hetag =>
                obtain ⟨f', hcontains, hf'⟩ :=
                  Ty.tyEquiv_rowContains_mp (Ty.tyEquiv_unionRow hetag) Ty.RowContains.head
                simp only [reduce1Run, reduceApply, reduceCall, Cast.asTagged] at hr
                split at hr
                · rename_i hcond; cases hr
                  obtain rfl := eq_of_beq hcond
                  cases hcontains with
                  | head =>
                      exact ⟨_, hvp.conv hf',
                        StackWf.applyf (hbranch.conv (.congrFun (.refl _) hEff hRet)) hrest⟩
                  | tail hne _ => exact absurd rfl hne
                · rename_i hcond; cases hr
                  have hvlne : vl ≠ lbl := fun h => by subst h; simp at hcond
                  cases hcontains with
                  | head => exact absurd rfl hvlne
                  | tail _ hc'' =>
                      obtain ⟨rest', htail⟩ := Ty.rowContains_tyEquiv hc''
                      exact ⟨_, HasTypeV.tagged (hvp.conv hf') (Ty.TyEquiv.congrUnion htail),
                        StackWf.applyf (hotherwise.conv (.congrFun (.refl _) hEff hRet)) hrest⟩
        | @partialSelect lbl fieldTy tail _ he =>
            obtain ⟨hD, _, hRet⟩ := Ty.tyEquiv_fun_components he
            have hvr := harg.conv hD.symm
            obtain ⟨fields, rfl⟩ := canonical_record hvr
            cases hvr with
            | record hpres hmatch hetag =>
                obtain ⟨f', hcont, hf'⟩ :=
                  (Ty.tyEquiv_rowContains (Ty.tyEquiv_recordRow hetag)).2 _ _ Ty.RowContains.head
                obtain ⟨value, hget, hvalue⟩ := record_get hpres hmatch hcont
                simp only [reduce1Run, reduceApply, reduceCall, Cast.asRecord, hget] at hr; cases hr
                exact ⟨_, hvalue.conv (hf'.symm.trans hRet), hrest⟩
        | partialExtendNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.partialExtendOne (harg.conv hA.symm) hR, hrest⟩
        | @partialExtendOne lbl _ fieldTy row _ hvf he =>
            obtain ⟨hD, _, hRet⟩ := Ty.tyEquiv_fun_components he
            have hvr := harg.conv hD.symm
            obtain ⟨fields, rfl⟩ := canonical_record hvr
            cases hvr with
            | record hpres hmatch hetag =>
                simp only [reduce1Run, reduceApply, reduceCall, Cast.asRecord] at hr; cases hr
                refine ⟨_, HasTypeV.record ?_ ?_ hRet, hrest⟩
                · intro l' f' hc
                  cases hc with
                  | head => rw [recordInsert_get_eq]; simp
                  | tail hne hc' =>
                      rw [recordInsert_get_ne _ _ (by simp [hne])]
                      obtain ⟨f'', hc'', _⟩ :=
                        (Ty.tyEquiv_rowContains (Ty.tyEquiv_recordRow hetag)).2 _ _ hc'
                      exact hpres l' f'' hc''
                · intro l' f' v' hc hg
                  cases hc with
                  | head =>
                      rw [recordInsert_get_eq] at hg
                      simp only [Option.some.injEq] at hg; subst hg; exact hvf
                  | tail hne hc' =>
                      rw [recordInsert_get_ne _ _ (by simp [hne])] at hg
                      obtain ⟨f'', hc'', heqf⟩ :=
                        (Ty.tyEquiv_rowContains (Ty.tyEquiv_recordRow hetag)).2 _ _ hc'
                      exact (hmatch l' f'' v' hc'' hg).conv heqf.symm
        | partialOverwriteNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨_, HasTypeV.partialOverwriteOne (harg.conv hA.symm) hR, hrest⟩
        | @partialOverwriteOne lbl _ newTy oldTy tail _ hvf he =>
            obtain ⟨hD, _, hRet⟩ := Ty.tyEquiv_fun_components he
            have hvr := harg.conv hD.symm
            obtain ⟨fields, rfl⟩ := canonical_record hvr
            cases hvr with
            | record hpres hmatch hetag =>
                obtain ⟨_, hcontH, _⟩ := (Ty.tyEquiv_rowContains
                  (Ty.tyEquiv_recordRow hetag)).2 _ _ Ty.RowContains.head
                obtain ⟨_, hget, _⟩ := record_get hpres hmatch hcontH
                simp only [reduce1Run, reduceApply, reduceCall, Cast.asRecord, hget] at hr
                cases hr
                refine ⟨_, HasTypeV.record ?_ ?_ hRet, hrest⟩
                · intro l' f' hc
                  cases hc with
                  | head => rw [recordInsert_get_eq]; simp
                  | tail hne hc' =>
                      rw [recordInsert_get_ne _ _ (by simp [hne])]
                      obtain ⟨f'', hc'', _⟩ := (Ty.tyEquiv_rowContains
                        (Ty.tyEquiv_recordRow hetag)).2 _ _ (Ty.RowContains.tail hne hc')
                      exact hpres l' f'' hc''
                · intro l' f' v' hc hg
                  cases hc with
                  | head =>
                      rw [recordInsert_get_eq] at hg
                      simp only [Option.some.injEq] at hg; subst hg; exact hvf
                  | tail hne hc' =>
                      rw [recordInsert_get_ne _ _ (by simp [hne])] at hg
                      obtain ⟨f'', hc'', heqf⟩ := (Ty.tyEquiv_rowContains
                        (Ty.tyEquiv_recordRow hetag)).2 _ _ (Ty.RowContains.tail hne hc')
                      exact (hmatch l' f'' v' hc'' hg).conv heqf.symm
        | partialPerformNil _ =>
            simp only [reduce1Run, reduceApply, reduceCall, reducePerform,
              stackWf_doPerformR_unhandled hrest] at hr
            exact absurd hr (by simp)

/-! ## Effect safety: a well-typed `.perform` escapes only operations in `ε`

With `Perform` typed (T5), a well-typed state *can* `.perform` — but only an
operation that is a member of the ambient row `ε`. The suspended `wait` successor is
then well-typed (`op ∈ ε`, the stack carries the reply to the answer). Builtins and
the data partials still never perform (their `reduceCall` arms are pure). -/

theorem reduceCallBuiltin_ne_perform [BEq m] {key : String} {applied : List (Value m)}
    {ann : m} {env : Env m} {k : Stack m} {op : String} {lift : Value m}
    {envP : Env m} {kP : Stack m} :
    reduceCallBuiltin key applied ann env k ≠ .perform op lift envP kP := by
  intro h
  unfold reduceCallBuiltin at h
  repeat' split at h
  all_goals simp_all

/-- A `Builtin` partial's `reduceCall` never performs (used by `progress`). -/
theorem reduceCall_builtin_ne_perform [BEq m] {id : String} {applied : List (Value m)}
    {arg : Value m} {ann : m} {env : Env m} {k : Stack m} {op : String} {lift : Value m}
    {envP : Env m} {kP : Stack m} :
    reduceCall (.Partial (.Builtin id) applied) arg ann env k ≠ .perform op lift envP kP := by
  simp only [reduceCall]; exact reduceCallBuiltin_ne_perform

/-- **Effect safety at the call.** A typed function value applied to a typed arg
under a typed rest-stack: every non-`Perform` partial never performs; the `Perform l`
partial does, and the resulting `.perform op` has `op ∈ ε` (`EffContains`) with the
suspended `wait` well-typed at the answer `τ`. The `Perform` case is the only one
that reaches a `.perform`; the stack has no `Delimit` (T5 has not typed `Handle`
yet), so `doPerformR` reports unhandled and the effect escapes. -/
theorem reduceCall_perform_wait [BEq m] {f arg : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {argTy retTy ε τ : Ty} {op : String} {lift : Value m}
    {envP : Env m} {kP : Stack m}
    (hf : HasTypeV f (.fun argTy ε retTy)) (hrest : StackWf rest retTy ε τ)
    (h : reduceCall f arg ann fenv rest = .perform op lift envP kP) :
    MStateWf (.wait op envP kP) τ ε := by
  rcases canonical_arrow hf with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
  · exact absurd h (by simp [reduceCall])
  · cases hf with
    | partialBuiltin _ _ _ => exact absurd h reduceCall_builtin_ne_perform
    | partialConsNil _ => exact absurd h (by simp [reduceCall])
    | partialConsOne _ _ =>
        simp only [reduceCall] at h; split at h <;> exact absurd h (by simp)
    | partialTag _ => exact absurd h (by simp [reduceCall])
    | partialNoCases _ => exact absurd h (by simp [reduceCall])
    | partialMatchNil _ => exact absurd h (by simp [reduceCall])
    | partialMatchOne _ _ => exact absurd h (by simp [reduceCall])
    | partialMatchTwo _ _ _ =>
        simp only [reduceCall] at h
        split at h
        · exact absurd h (by simp)
        · split at h <;> exact absurd h (by simp)
    | partialSelect _ =>
        simp only [reduceCall] at h
        split at h
        · exact absurd h (by simp)
        · split at h <;> exact absurd h (by simp)
    | partialExtendNil _ => exact absurd h (by simp [reduceCall])
    | partialExtendOne _ _ =>
        simp only [reduceCall] at h
        split at h <;> exact absurd h (by simp)
    | partialOverwriteNil _ => exact absurd h (by simp [reduceCall])
    | partialOverwriteOne _ _ =>
        simp only [reduceCall] at h
        split at h
        · exact absurd h (by simp)
        · split at h <;> exact absurd h (by simp)
    | @partialPerformNil label argTy' replyTy' μ _ he =>
        obtain ⟨_, hE, hR⟩ := Ty.tyEquiv_fun_components he
        simp only [reduceCall, reducePerform, stackWf_doPerformR_unhandled hrest] at h
        injection h with hop hlift henv hk; subst hop hlift henv hk
        obtain ⟨a'', b'', hEff, _, hRb⟩ := Ty.tyEquiv_effContains_mp hE Ty.EffContains.head
        exact ⟨a'', b'', retTy, hEff, hRb.symm.trans hR, hrest⟩

/-- **Preservation at the effect boundary.** A well-typed state that `.perform`s
lands a well-typed `wait`: the performed `op` is a member of `ε` (effect safety). -/
theorem preservation_perform [BEq m] {cfg : Config m} {τ ε : Ty}
    {op : String} {lift : Value m} {envP : Env m} {kP : Stack m}
    (hwf : MStateWf (.run cfg) τ ε)
    (h : reduce1Run cfg = .perform op lift envP kP) :
    MStateWf (.wait op envP kP) τ ε := by
  obtain ⟨c, env, k⟩ := cfg
  cases c with
  | E e =>
      obtain ⟨expr, ann⟩ := e
      exact absurd h (by
        cases expr <;> simp only [reduce1Run, reduceEval] <;>
          first | simp | (split <;> simp))
  | V v =>
      cases k with
      | nil => simp only [reduce1Run] at h; exact absurd h (by simp)
      | cons kontann rest =>
          obtain ⟨kont, ann⟩ := kontann
          obtain ⟨τin, hv, hst⟩ := mStateWf_V hwf
          cases hst with
          | trace hrest => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | assign _ _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | arg _ _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | applyf hf hrest =>
              simp only [reduce1Run, reduceApply] at h
              exact reduceCall_perform_wait hf hrest h
          | callwith _ hrest =>
              simp only [reduce1Run, reduceApply] at h
              exact reduceCall_perform_wait hv hrest h

/-- The **effect-reply contract**: when a suspended `wait op` is resumed, the world
supplies a reply value of the operation's declared reply type. Vacuously `True` for
non-reply transitions. Closed `evalR` never replies (a `.perform` is terminal there),
so `soundness_value` does not need it; it is the well-typed-oracle assumption that
`runR`/`BehaviorsR` (T6/T7) will discharge. -/
def ReplyContract {m : Type} [BEq m] (ε : Ty) : MState m → Label m → Prop
  | .wait op _ _, .reply _ v => ∀ a b, Ty.EffContains ε op a b → HasTypeV v b
  | _, _ => True

/-! ## Preservation -/

/-- **Preservation**: a well-typed state stays well-typed under `Reduce` (modulo
the T6 builtin-application obligation `hsat`). The successor is well-typed at *some*
ambient row `ε'` — the same `ε` for the pure/data/`Perform` fragment, but the row
**shrinks** across an effect-discharging `Delimit` pop (T5 `Handle`), so the row is an
*output* not an invariant. This loses nothing for soundness: `soundness_value`
concludes the ε-free `HasTypeV v τ`. `tau` splits into the `.E`/`.V` cases; `perform`
lands a well-typed `wait` (effect safety: `op ∈ ε`, `preservation_perform`); `reply`
resumes with a reply value typed by the `ReplyContract` (`hrep`) — vacuous for
`tau`/`perform`, and never exercised by closed `evalR` (which makes `perform`
terminal). -/
theorem preservation [BEq m] (hsat : BuiltinAppPreserves m)
    {s s' : MState m} {μ : Label m} {τ ε : Ty}
    (hwf : MStateWf s τ ε) (hr : Reduce s μ s') (hrep : ReplyContract ε s μ) :
    ∃ ε', MStateWf s' τ ε' := by
  cases hr with
  | tau h =>
      refine ⟨ε, ?_⟩
      rename_i cfg cfg'
      obtain ⟨c, env, k⟩ := cfg
      cases c with
      | E e => exact preservation_E hwf h
      | V v =>
          cases k with
          | nil => simp only [reduce1Run] at h; exact absurd h (by simp)
          | cons kontann rest =>
              obtain ⟨kont, ann⟩ := kontann
              exact preservation_V hsat hwf h
  | perform h => exact ⟨ε, preservation_perform hwf h⟩
  | reply =>
      obtain ⟨a, b, replyTy, hEff, hbr, hStack⟩ := hwf
      simp only [ReplyContract] at hrep
      exact ⟨ε, replyTy, (hrep a b hEff).conv hbr, hStack⟩

/-- **Preservation across a `tau` step, with the effect row preserved exactly.** Pure
machine moves keep the ambient `ε` (the `tau` case of `preservation` returns the same
`ε`), which the `∃ ε'` wrapper of `preservation` hides — this variant exposes it, so a
soundness fold can thread `ε` through a silent run (used by the effect-escape soundness). -/
theorem preservation_tau [BEq m] (hsat : BuiltinAppPreserves m) {cfg cfg' : Config m}
    {τ ε : Ty} (hwf : MStateWf (.run cfg) τ ε) (h : reduce1Run cfg = .tau cfg') :
    MStateWf (.run cfg') τ ε := by
  obtain ⟨c, env, k⟩ := cfg
  cases c with
  | E e => exact preservation_E hwf h
  | V v =>
      cases k with
      | nil => simp only [reduce1Run] at h; exact absurd h (by simp)
      | cons kontann rest => obtain ⟨kont, ann⟩ := kontann; exact preservation_V hsat hwf h

/-! ## Soundness: a well-typed run never crashes; its result is typed

The terminal-value half of soundness, threaded through `evalR`. When `reduce1Run`
of a well-typed state is `.done (.value v)`, the value is typed at the answer type
`τ`: at the empty stack this is `StackWf.nil` (`τin = τ`); a saturated builtin
defers to `hsat`. -/

theorem reduce1Run_done_value_typed [BEq m] (hsat : BuiltinAppPreserves m)
    {cfg : Config m} {τ ε : Ty} {v : Value m}
    (hwf : MStateWf (.run cfg) τ ε) (h : reduce1Run cfg = .done (.value v)) :
    HasTypeV v τ := by
  obtain ⟨c, env, k⟩ := cfg
  cases c with
  | E e =>
      -- `reduceEval` never yields `.done (.value _)` (only `.tau` or a crash)
      obtain ⟨expr, ann⟩ := e
      cases expr <;> simp only [reduce1Run, reduceEval] at h <;>
        first | exact absurd h (by simp) | (split at h <;> exact absurd h (by simp))
  | V w =>
      cases k with
      | nil =>
          -- terminal: `w = v`, typed at `τ` via `StackWf.nil`
          obtain ⟨τin, hw, hst⟩ := mStateWf_V hwf
          simp only [reduce1Run] at h
          cases h
          cases hst; exact hw
      | cons kontann rest =>
          obtain ⟨kont, ann⟩ := kontann
          obtain ⟨τin, hw, hst⟩ := mStateWf_V hwf
          cases hst with
          | trace _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | assign _ _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | arg _ _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | applyf hf hrest =>
              rcases canonical_arrow hf with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
              · exact absurd h (by simp [reduce1Run, reduceApply, reduceCall])
              · cases hf with
                | partialBuiltin hs hp he =>
                    simp only [reduce1Run, reduceApply] at h
                    exact (hsat (.partialBuiltin hs hp he) hw hrest).2 _ h
                | partialConsNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialConsOne _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h
                    split at h <;> exact absurd h (by simp)
                | partialTag _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialNoCases he =>
                    obtain ⟨hA, _, _⟩ := Ty.tyEquiv_fun_components he
                    exact absurd (hw.conv hA.symm) canonical_union_empty
                | partialMatchNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialMatchOne _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialMatchTwo _ _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h
                    split at h
                    · exact absurd h (by simp)
                    · split at h <;> exact absurd h (by simp)
                | partialSelect _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h
                    split at h
                    · exact absurd h (by simp)
                    · split at h <;> exact absurd h (by simp)
                | partialExtendNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialExtendOne _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h
                    split at h <;> exact absurd h (by simp)
                | partialOverwriteNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialOverwriteOne _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h
                    split at h
                    · exact absurd h (by simp)
                    · split at h <;> exact absurd h (by simp)
                | partialPerformNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall, reducePerform,
                      stackWf_doPerformR_unhandled hrest] at h
                    exact absurd h (by simp)
          | callwith harg hrest =>
              rcases canonical_arrow hw with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
              · exact absurd h (by simp [reduce1Run, reduceApply, reduceCall])
              · cases hw with
                | partialBuiltin hs hp he =>
                    simp only [reduce1Run, reduceApply] at h
                    exact (hsat (.partialBuiltin hs hp he) harg hrest).2 _ h
                | partialConsNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialConsOne _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h
                    split at h <;> exact absurd h (by simp)
                | partialTag _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialNoCases he =>
                    obtain ⟨hA, _, _⟩ := Ty.tyEquiv_fun_components he
                    exact absurd (harg.conv hA.symm) canonical_union_empty
                | partialMatchNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialMatchOne _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialMatchTwo _ _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h
                    split at h
                    · exact absurd h (by simp)
                    · split at h <;> exact absurd h (by simp)
                | partialSelect _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h
                    split at h
                    · exact absurd h (by simp)
                    · split at h <;> exact absurd h (by simp)
                | partialExtendNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialExtendOne _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h
                    split at h <;> exact absurd h (by simp)
                | partialOverwriteNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialOverwriteOne _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h
                    split at h
                    · exact absurd h (by simp)
                    · split at h <;> exact absurd h (by simp)
                | partialPerformNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall, reducePerform,
                      stackWf_doPerformR_unhandled hrest] at h
                    exact absurd h (by simp)

/-- **Soundness (value typing through evaluation).** A well-typed configuration's
fuel-bounded evaluation, if it terminates with a value, terminates with a value of
the answer type `τ` — the type is *preserved through the whole run* (modulo the T6
builtin obligation `hsat`). Proof: fuel induction, `preservation` across each `tau`
step, `reduce1Run_done_value_typed` at the terminal. -/
theorem soundness_value [BEq m] (hsat : BuiltinAppPreserves m) :
    ∀ (fuel : Nat) {cfg : Config m} {τ ε : Ty} {v : Value m},
      MStateWf (.run cfg) τ ε → evalR fuel cfg = .done (.value v) → HasTypeV v τ := by
  intro fuel
  induction fuel with
  | zero => intro cfg τ ε v _ h; simp [evalR] at h
  | succ n ih =>
      intro cfg τ ε v hwf h
      rw [evalR] at h
      cases hrr : reduce1Run cfg with
      | tau cfg' =>
          rw [hrr] at h
          obtain ⟨ε', hwf'⟩ := preservation hsat hwf (Reduce.tau hrr) trivial
          exact ih hwf' h
      | done o =>
          rw [hrr] at h
          cases o with
          | value w => cases h; exact reduce1Run_done_value_typed hsat hwf hrr
          | crash r => simp at h
      | perform op lift envP kP => rw [hrr] at h; simp at h

/-! ## Progress: a well-typed state never gets stuck on a bad crash

The builtin **application** no-bad-crash obligation, isolated as a hypothesis (T6:
a typed builtin call only ever fails with the sanctioned `Unrepresentable`). -/

def BuiltinAppNoBadCrash (m : Type) [BEq m] : Prop :=
  ∀ {id : String} {applied : List (Value m)} {arg : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {argTy retTy ε : Ty} {r : Reason m},
    HasTypeV (.Partial (.Builtin id) applied) (.fun argTy ε retTy) →
    HasTypeV arg argTy →
    reduceCall (.Partial (.Builtin id) applied) arg ann fenv rest = .done (.crash r) →
    ¬ Reason.IsBad r

/-- **Progress (with effect safety).** A well-typed state either steps (`.tau`), is a
terminal value, terminates with a *sanctioned* (`¬ IsBad`) crash, **or** suspends on
a `.perform op` whose operation is a member of the ambient row `ε` (`EffContains` —
the effect-escape clause). Never a bad crash, never a perform outside `ε`. For the
builtin/effect-free core this is always step-or-value; `Unrepresentable` is the only
crash a typed program can reach. -/
theorem progress [BEq m] (hbad : BuiltinAppNoBadCrash m)
    {cfg : Config m} {τ ε : Ty} (hwf : MStateWf (.run cfg) τ ε) :
    (∃ cfg', reduce1Run cfg = .tau cfg') ∨ (∃ v, reduce1Run cfg = .done (.value v)) ∨
    (∃ r, reduce1Run cfg = .done (.crash r) ∧ ¬ Reason.IsBad r) ∨
    (∃ op lift envP kP, reduce1Run cfg = .perform op lift envP kP ∧
      ∃ a b, Ty.EffContains ε op a b) := by
  obtain ⟨c, env, k⟩ := cfg
  cases c with
  | E e =>
      obtain ⟨Γ, τin, henv, hty, hst⟩ := mStateWf_E hwf
      obtain ⟨expr, ann⟩ := e
      cases expr with
      | Variable x =>
          obtain ⟨s, args, hl, _⟩ := inv_var hty
          obtain ⟨v, hvlk, _⟩ := envwf_lookup henv hl
          exact Or.inl ⟨(.V v, env, k), by simp [reduce1Run, reduceEval, hvlk]⟩
      | Builtin id =>
          obtain ⟨s, args, hs, _⟩ := inv_builtin hty
          exact Or.inl ⟨(.V (.Partial (.Builtin id) []), env, k),
            by simp [reduce1Run, reduceEval, builtin_scheme_isBuiltin hs]⟩
      | Integer n => exact Or.inl ⟨_, rfl⟩
      | String s => exact Or.inl ⟨_, rfl⟩
      | Binary b => exact Or.inl ⟨_, rfl⟩
      | Lambda x b => exact Or.inl ⟨_, rfl⟩
      | Apply f a => exact Or.inl ⟨_, rfl⟩
      | Let x d b => exact Or.inl ⟨_, rfl⟩
      | Tail => exact Or.inl ⟨_, rfl⟩
      | Empty => exact Or.inl ⟨_, rfl⟩
      | Cons => exact Or.inl ⟨_, rfl⟩
      | Tag l => exact Or.inl ⟨_, rfl⟩
      | NoCases => exact Or.inl ⟨_, rfl⟩
      | Case l => exact Or.inl ⟨_, rfl⟩
      | Select l => exact Or.inl ⟨_, rfl⟩
      | Extend l => exact Or.inl ⟨_, rfl⟩
      | Overwrite l => exact Or.inl ⟨_, rfl⟩
      | Perform l => exact Or.inl ⟨_, rfl⟩
      | _ =>
          exfalso
          rcases hasType_expr_form hty with ⟨_, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, _, hh⟩ |
            ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ | hh | hh | hh | ⟨_, hh⟩ | hh | ⟨_, hh⟩ |
            ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ <;> simp at hh
  | V w =>
      cases k with
      | nil => exact Or.inr (Or.inl ⟨w, rfl⟩)
      | cons kontann rest =>
          obtain ⟨kont, ann⟩ := kontann
          obtain ⟨τin, hw, hst⟩ := mStateWf_V hwf
          cases hst with
          | trace _ => exact Or.inl ⟨_, rfl⟩
          | assign _ _ _ => exact Or.inl ⟨_, rfl⟩
          | arg _ _ _ => exact Or.inl ⟨_, rfl⟩
          | @applyf _ f fenv _ _ _ _ _ hf hrest =>
              rcases canonical_arrow hf with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
              · exact Or.inl ⟨_, rfl⟩
              · cases hf with
                | @partialBuiltin id _ _ _ _ _ _ _ hs hp he =>
                    simp only [reduce1Run, reduceApply]
                    cases hres : reduceCall (.Partial (.Builtin id) applied) w ann fenv rest with
                    | tau cfg' => exact Or.inl ⟨cfg', rfl⟩
                    | done o =>
                        cases o with
                        | value v => exact Or.inr (Or.inl ⟨v, rfl⟩)
                        | crash r =>
                            exact Or.inr (Or.inr (Or.inl
                              ⟨r, rfl, hbad (.partialBuiltin hs hp he) hw hres⟩))
                    | perform _ _ _ _ => exact absurd hres reduceCall_builtin_ne_perform
                | partialConsNil _ => exact Or.inl ⟨_, rfl⟩
                | partialConsOne hh he =>
                    obtain ⟨hD, _, _⟩ := Ty.tyEquiv_fun_components he
                    obtain ⟨es, rfl⟩ := canonical_list (hw.conv hD.symm)
                    exact Or.inl ⟨_, rfl⟩
                | partialTag _ => exact Or.inl ⟨_, rfl⟩
                | partialNoCases he =>
                    obtain ⟨hA, _, _⟩ := Ty.tyEquiv_fun_components he
                    exact absurd (hw.conv hA.symm) canonical_union_empty
                | partialMatchNil _ => exact Or.inl ⟨_, rfl⟩
                | partialMatchOne _ _ => exact Or.inl ⟨_, rfl⟩
                | @partialMatchTwo lbl _ _ inner eff ret tail1 _ hbranch hotherwise he =>
                    obtain ⟨hD, _, _⟩ := Ty.tyEquiv_fun_components he
                    obtain ⟨vl, vp, rfl⟩ := canonical_union (hw.conv hD.symm)
                    refine Or.inl ?_
                    simp only [reduce1Run, reduceApply, reduceCall, Cast.asTagged]
                    split
                    · exact ⟨_, rfl⟩
                    · exact ⟨_, rfl⟩
                | @partialSelect lbl fieldTy tail _ he =>
                    obtain ⟨hD, _, _⟩ := Ty.tyEquiv_fun_components he
                    have hvr := hw.conv hD.symm
                    obtain ⟨fields, rfl⟩ := canonical_record hvr
                    cases hvr with
                    | record hpres hmatch hetag =>
                        obtain ⟨f', hcont, _⟩ := (Ty.tyEquiv_rowContains
                          (Ty.tyEquiv_recordRow hetag)).2 _ _ Ty.RowContains.head
                        obtain ⟨value, hget, _⟩ := record_get hpres hmatch hcont
                        exact Or.inl ⟨(.V value, fenv, rest),
                          by simp [reduce1Run, reduceApply, reduceCall, Cast.asRecord, hget]⟩
                | partialExtendNil _ => exact Or.inl ⟨_, rfl⟩
                | @partialExtendOne lbl val fieldTy row _ hvf he =>
                    obtain ⟨hD, _, _⟩ := Ty.tyEquiv_fun_components he
                    obtain ⟨fields, rfl⟩ := canonical_record (hw.conv hD.symm)
                    exact Or.inl ⟨(.V (.Record (recordInsert fields lbl val)), fenv, rest),
                      by simp [reduce1Run, reduceApply, reduceCall, Cast.asRecord]⟩
                | partialOverwriteNil _ => exact Or.inl ⟨_, rfl⟩
                | @partialOverwriteOne lbl val newTy oldTy tail _ hvf he =>
                    obtain ⟨hD, _, _⟩ := Ty.tyEquiv_fun_components he
                    have hvr := hw.conv hD.symm
                    obtain ⟨fields, rfl⟩ := canonical_record hvr
                    cases hvr with
                    | record hpres hmatch hetag =>
                        obtain ⟨_, hcont, _⟩ := (Ty.tyEquiv_rowContains
                          (Ty.tyEquiv_recordRow hetag)).2 _ _ Ty.RowContains.head
                        obtain ⟨_, hget, _⟩ := record_get hpres hmatch hcont
                        exact Or.inl ⟨(.V (.Record (recordInsert fields lbl val)), fenv, rest),
                          by simp [reduce1Run, reduceApply, reduceCall, Cast.asRecord, hget]⟩
                | @partialPerformNil label _ _ μ _ he =>
                    -- the perform escapes: `op = label ∈ ε` (no `Delimit` ⇒ unhandled)
                    obtain ⟨_, hE, _⟩ := Ty.tyEquiv_fun_components he
                    obtain ⟨a'', b'', hEff, _, _⟩ := Ty.tyEquiv_effContains_mp hE Ty.EffContains.head
                    refine Or.inr (Or.inr (Or.inr ⟨label, w, fenv, rest, ?_, a'', b'', hEff⟩))
                    simp only [reduce1Run, reduceApply, reduceCall, reducePerform,
                      stackWf_doPerformR_unhandled hrest]
          | @callwith _ arg fenv _ _ _ _ _ harg hrest =>
              rcases canonical_arrow hw with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
              · exact Or.inl ⟨_, rfl⟩
              · cases hw with
                | @partialBuiltin id _ _ _ _ _ _ _ hs hp he =>
                    simp only [reduce1Run, reduceApply]
                    cases hres : reduceCall (.Partial (.Builtin id) applied) arg ann fenv rest with
                    | tau cfg' => exact Or.inl ⟨cfg', rfl⟩
                    | done o =>
                        cases o with
                        | value v => exact Or.inr (Or.inl ⟨v, rfl⟩)
                        | crash r =>
                            exact Or.inr (Or.inr (Or.inl
                              ⟨r, rfl, hbad (.partialBuiltin hs hp he) harg hres⟩))
                    | perform _ _ _ _ => exact absurd hres reduceCall_builtin_ne_perform
                | partialConsNil _ => exact Or.inl ⟨_, rfl⟩
                | partialConsOne hh he =>
                    obtain ⟨hD, _, _⟩ := Ty.tyEquiv_fun_components he
                    obtain ⟨es, rfl⟩ := canonical_list (harg.conv hD.symm)
                    exact Or.inl ⟨_, rfl⟩
                | partialTag _ => exact Or.inl ⟨_, rfl⟩
                | partialNoCases he =>
                    obtain ⟨hA, _, _⟩ := Ty.tyEquiv_fun_components he
                    exact absurd (harg.conv hA.symm) canonical_union_empty
                | partialMatchNil _ => exact Or.inl ⟨_, rfl⟩
                | partialMatchOne _ _ => exact Or.inl ⟨_, rfl⟩
                | @partialMatchTwo lbl _ _ inner eff ret tail1 _ hbranch hotherwise he =>
                    obtain ⟨hD, _, _⟩ := Ty.tyEquiv_fun_components he
                    obtain ⟨vl, vp, rfl⟩ := canonical_union (harg.conv hD.symm)
                    refine Or.inl ?_
                    simp only [reduce1Run, reduceApply, reduceCall, Cast.asTagged]
                    split
                    · exact ⟨_, rfl⟩
                    · exact ⟨_, rfl⟩
                | @partialSelect lbl fieldTy tail _ he =>
                    obtain ⟨hD, _, _⟩ := Ty.tyEquiv_fun_components he
                    have hvr := harg.conv hD.symm
                    obtain ⟨fields, rfl⟩ := canonical_record hvr
                    cases hvr with
                    | record hpres hmatch hetag =>
                        obtain ⟨f', hcont, _⟩ := (Ty.tyEquiv_rowContains
                          (Ty.tyEquiv_recordRow hetag)).2 _ _ Ty.RowContains.head
                        obtain ⟨value, hget, _⟩ := record_get hpres hmatch hcont
                        exact Or.inl ⟨(.V value, fenv, rest),
                          by simp [reduce1Run, reduceApply, reduceCall, Cast.asRecord, hget]⟩
                | partialExtendNil _ => exact Or.inl ⟨_, rfl⟩
                | @partialExtendOne lbl val fieldTy row _ hvf he =>
                    obtain ⟨hD, _, _⟩ := Ty.tyEquiv_fun_components he
                    obtain ⟨fields, rfl⟩ := canonical_record (harg.conv hD.symm)
                    exact Or.inl ⟨(.V (.Record (recordInsert fields lbl val)), fenv, rest),
                      by simp [reduce1Run, reduceApply, reduceCall, Cast.asRecord]⟩
                | partialOverwriteNil _ => exact Or.inl ⟨_, rfl⟩
                | @partialOverwriteOne lbl val newTy oldTy tail _ hvf he =>
                    obtain ⟨hD, _, _⟩ := Ty.tyEquiv_fun_components he
                    have hvr := harg.conv hD.symm
                    obtain ⟨fields, rfl⟩ := canonical_record hvr
                    cases hvr with
                    | record hpres hmatch hetag =>
                        obtain ⟨_, hcont, _⟩ := (Ty.tyEquiv_rowContains
                          (Ty.tyEquiv_recordRow hetag)).2 _ _ Ty.RowContains.head
                        obtain ⟨_, hget, _⟩ := record_get hpres hmatch hcont
                        exact Or.inl ⟨(.V (.Record (recordInsert fields lbl val)), fenv, rest),
                          by simp [reduce1Run, reduceApply, reduceCall, Cast.asRecord, hget]⟩
                | @partialPerformNil label _ _ μ _ he =>
                    obtain ⟨_, hE, _⟩ := Ty.tyEquiv_fun_components he
                    obtain ⟨a'', b'', hEff, _, _⟩ := Ty.tyEquiv_effContains_mp hE Ty.EffContains.head
                    refine Or.inr (Or.inr (Or.inr ⟨label, arg, fenv, rest, ?_, a'', b'', hEff⟩))
                    simp only [reduce1Run, reduceApply, reduceCall, reducePerform,
                      stackWf_doPerformR_unhandled hrest]

/-! ## T6b — discharging the builtin-saturation obligations

The `BuiltinAppPreserves`/`BuiltinAppNoBadCrash` hypotheses are now discharged for
the **general (non-`fix`) builtins** via the per-builtin `run_*` typing lemmas above.
The single stack-coupled special, `fix` (its `reduceCallBuiltin` arm pushes an
`Apply` frame rather than calling `Builtin.run`, and produces an unscheme'd `fixed`
partial), is isolated as the `FixPreserves`/`FixNoBadCrash` sub-hypotheses. -/

/-- Extend a builtin-partial's peeling by one more typed argument: applying an
argument of the next domain peels one arrow off the residual. -/
theorem builtinPartialWf_append {m : Type} {base resid : Ty} {applied : List (Value m)}
    {a ε r : Ty} {arg : Value m}
    (hpw : BuiltinPartialWf base applied resid)
    (hr : resid = .fun a ε r) (harg : HasTypeV arg a) :
    BuiltinPartialWf base (applied ++ [arg]) r := by
  induction applied generalizing base with
  | nil =>
      cases hpw; subst hr; exact BuiltinPartialWf.cons harg BuiltinPartialWf.nil
  | cons hd tl ih =>
      cases hpw with
      | cons hv hrest => exact BuiltinPartialWf.cons hv (ih hrest)

/-- For any builtin key that is **not** one of the four stack-coupled specials
(`fix`/`fixed`/`list_fold`/`binary_fold`), `reduceCallBuiltin` is the generic
arity-dispatch branch: under-applied ⇒ accumulate a partial; saturated ⇒ run. -/
theorem reduceCallBuiltin_other [BEq m] {key : String} {applied : List (Value m)}
    {ann : m} {env : Env m} {k : Stack m}
    (h1 : key ≠ "fix") (h2 : key ≠ "fixed") (h3 : key ≠ "list_fold") (h4 : key ≠ "binary_fold") :
    reduceCallBuiltin key applied ann env k =
      (match Builtin.builtinArity key with
       | none => .done (.crash (.UndefinedBuiltin key))
       | some n => if applied.length == n then
            (match Builtin.run key applied with
             | .error e => .done (.crash e)
             | .ok v => .tau (.V v, env, k))
          else .tau (.V (.Partial (.Builtin key) applied), env, k)) := by
  unfold reduceCallBuiltin
  split <;> first | rfl | simp_all

/-- A `Builtin id` partial's `reduceCall` dispatches to `reduceCallBuiltin id (applied ++ [arg])`. -/
theorem reduceCall_builtin_eq [BEq m] {id : String} {applied : List (Value m)}
    {arg : Value m} {ann : m} {env : Env m} {k : Stack m} :
    reduceCall (.Partial (.Builtin id) applied) arg ann env k
      = reduceCallBuiltin id (applied ++ [arg]) ann env k := by
  simp only [reduceCall]

/-- Saturated general builtin: when the arg count hits the arity and `run` succeeds,
the machine `tau`-steps to the run result on the value stack. -/
theorem reduceCallBuiltin_sat [BEq m] {key : String} {applied : List (Value m)}
    {ann : m} {env : Env m} {k : Stack m} {n : Nat} {value : Value m}
    (h1 : key ≠ "fix") (h2 : key ≠ "fixed") (h3 : key ≠ "list_fold") (h4 : key ≠ "binary_fold")
    (harity : Builtin.builtinArity key = some n) (hlen : applied.length = n)
    (hrun : Builtin.run key applied = .ok value) :
    reduceCallBuiltin key applied ann env k = .tau (.V value, env, k) := by
  rw [reduceCallBuiltin_other h1 h2 h3 h4, harity]
  simp [hlen, hrun]

/-- Under-applied general builtin: when the arg count is short of the arity, the
machine `tau`-steps accumulating the partial. -/
theorem reduceCallBuiltin_acc [BEq m] {key : String} {applied : List (Value m)}
    {ann : m} {env : Env m} {k : Stack m} {n : Nat}
    (h1 : key ≠ "fix") (h2 : key ≠ "fixed") (h3 : key ≠ "list_fold") (h4 : key ≠ "binary_fold")
    (harity : Builtin.builtinArity key = some n) (hlen : applied.length ≠ n) :
    reduceCallBuiltin key applied ann env k
      = .tau (.V (.Partial (.Builtin key) applied), env, k) := by
  rw [reduceCallBuiltin_other h1 h2 h3 h4, harity]
  simp [hlen]

/-- Saturated general builtin whose `run` traps: the machine `done`-crashes. -/
theorem reduceCallBuiltin_sat_crash [BEq m] {key : String} {applied : List (Value m)}
    {ann : m} {env : Env m} {k : Stack m} {n : Nat} {e : Reason m}
    (h1 : key ≠ "fix") (h2 : key ≠ "fixed") (h3 : key ≠ "list_fold") (h4 : key ≠ "binary_fold")
    (harity : Builtin.builtinArity key = some n) (hlen : applied.length = n)
    (hrun : Builtin.run key applied = .error e) :
    reduceCallBuiltin key applied ann env k = .done (.crash e) := by
  rw [reduceCallBuiltin_other h1 h2 h3 h4, harity]
  simp [hlen, hrun]

/-- A saturating/accumulating general builtin never returns `.done (.value _)`
(its only outcomes are `.tau`-steps and `.done (.crash _)`). -/
theorem reduceCallBuiltin_ne_value [BEq m] {key : String} {applied : List (Value m)}
    {ann : m} {env : Env m} {k : Stack m} {v : Value m}
    (h1 : key ≠ "fix") (h2 : key ≠ "fixed") (h3 : key ≠ "list_fold") (h4 : key ≠ "binary_fold") :
    reduceCallBuiltin key applied ann env k ≠ .done (.value v) := by
  rw [reduceCallBuiltin_other h1 h2 h3 h4]
  split
  · simp
  · split
    · split <;> simp
    · simp

/-- **Arity-1 general builtin preservation driver.** Given the builtin's domain `D`,
non-arrow codomain `R`, and a per-builtin `run`-typing, both `BuiltinAppPreserves`
clauses hold. The partial is forced fully-applied (`applied = []`), so the machine
saturates. -/
theorem builtinApp_arity1 [BEq m] {key : String} {D R : Ty}
    (h1 : key ≠ "fix") (h2 : key ≠ "fixed") (h3 : key ≠ "list_fold") (h4 : key ≠ "binary_fold")
    (harity : Builtin.builtinArity key = some 1)
    (hRna : ∀ a e r, R ≠ .fun a e r)
    (hrunTy : ∀ {x v : Value m}, HasTypeV x D → Builtin.run key [x] = .ok v → HasTypeV v R)
    {applied : List (Value m)} {arg : Value m} {ann : m} {fenv : Env m} {rest : Stack m}
    {a' ε' r' retTy ε τ : Ty}
    (hpw : BuiltinPartialWf (.fun D .empty R) applied (.fun a' ε' r'))
    (harg' : HasTypeV arg a') (hr : Ty.TyEquiv r' retTy) (hst : StackWf rest retTy ε τ) :
    (∀ cfg', reduceCall (.Partial (.Builtin key) applied) arg ann fenv rest = .tau cfg' →
        MStateWf (.run cfg') τ ε) ∧
    (∀ v, reduceCall (.Partial (.Builtin key) applied) arg ann fenv rest = .done (.value v) →
        HasTypeV v τ) := by
  cases hpw with
  | nil =>
      refine ⟨?_, ?_⟩
      · intro cfg' htau
        rw [reduceCall_builtin_eq, List.nil_append] at htau
        cases hrun : Builtin.run key [arg] with
        | error e =>
            rw [reduceCallBuiltin_sat_crash h1 h2 h3 h4 harity rfl hrun] at htau; simp at htau
        | ok value =>
            rw [reduceCallBuiltin_sat h1 h2 h3 h4 harity rfl hrun] at htau
            injection htau with htau'; subst htau'
            exact ⟨retTy, (hrunTy harg' hrun).conv hr, hst⟩
      · intro v hval
        rw [reduceCall_builtin_eq, List.nil_append] at hval
        exact absurd hval (reduceCallBuiltin_ne_value h1 h2 h3 h4)
  | cons hv hrest =>
      cases hrest with
      | nil => exact absurd rfl (hRna _ _ _)
      | cons => exact absurd rfl (hRna _ _ _)

/-- **Arity-2 general builtin preservation driver.** `D1`/`D2` are the domains, `R`
the non-arrow codomain. Either the partial is one-short (`applied = []`, accumulate a
partial typed at the residual arrow) or saturated (`applied = [v]`, run). -/
theorem builtinApp_arity2 [BEq m] {key : String} {s : Scheme} {sargs : List Ty} {D1 D2 R : Ty}
    (h1 : key ≠ "fix") (h2 : key ≠ "fixed") (h3 : key ≠ "list_fold") (h4 : key ≠ "binary_fold")
    (harity : Builtin.builtinArity key = some 2)
    (hRna : ∀ a e r, R ≠ .fun a e r)
    (hsch : Builtins.scheme key = some s)
    (hbase : s.instantiate sargs = .fun D1 .empty (.fun D2 .empty R))
    (hrunTy : ∀ {x y v : Value m}, HasTypeV x D1 → HasTypeV y D2 →
      Builtin.run key [x, y] = .ok v → HasTypeV v R)
    {applied : List (Value m)} {arg : Value m} {ann : m} {fenv : Env m} {rest : Stack m}
    {a' ε' r' retTy ε τ : Ty}
    (hpw : BuiltinPartialWf (.fun D1 .empty (.fun D2 .empty R)) applied (.fun a' ε' r'))
    (harg' : HasTypeV arg a') (hr : Ty.TyEquiv r' retTy) (hst : StackWf rest retTy ε τ) :
    (∀ cfg', reduceCall (.Partial (.Builtin key) applied) arg ann fenv rest = .tau cfg' →
        MStateWf (.run cfg') τ ε) ∧
    (∀ v, reduceCall (.Partial (.Builtin key) applied) arg ann fenv rest = .done (.value v) →
        HasTypeV v τ) := by
  cases hpw with
  | nil =>
      -- accumulate: applied = [], successor partial typed at the residual arrow r'
      refine ⟨?_, ?_⟩
      · intro cfg' htau
        rw [reduceCall_builtin_eq, List.nil_append,
          reduceCallBuiltin_acc h1 h2 h3 h4 harity (by simp)] at htau
        injection htau with htau'; subst htau'
        refine ⟨retTy, ?_, hst⟩
        refine HasTypeV.partialBuiltin (args := sargs) hsch ?_ hr
        rw [hbase]
        exact BuiltinPartialWf.cons harg' BuiltinPartialWf.nil
      · intro v hval
        rw [reduceCall_builtin_eq, List.nil_append] at hval
        exact absurd hval (reduceCallBuiltin_ne_value h1 h2 h3 h4)
  | @cons _ _ _ vval _ _ hv hrest =>
      cases hrest with
      | nil =>
          -- saturate: applied = [vval], run on [vval, arg]
          refine ⟨?_, ?_⟩
          · intro cfg' htau
            rw [reduceCall_builtin_eq] at htau
            cases hrun : Builtin.run key [vval, arg] with
            | error e =>
                rw [show [vval] ++ [arg] = [vval, arg] from rfl,
                  reduceCallBuiltin_sat_crash h1 h2 h3 h4 harity rfl hrun] at htau; simp at htau
            | ok value =>
                rw [show [vval] ++ [arg] = [vval, arg] from rfl,
                  reduceCallBuiltin_sat h1 h2 h3 h4 harity rfl hrun] at htau
                injection htau with htau'; subst htau'
                exact ⟨retTy, (hrunTy hv harg' hrun).conv hr, hst⟩
          · intro v hval
            rw [reduceCall_builtin_eq] at hval
            exact absurd hval (reduceCallBuiltin_ne_value h1 h2 h3 h4)
      | cons _ hrest2 => cases hrest2 <;> exact absurd rfl (hRna _ _ _)

open Ty in
/-- Enumerate the builtin scheme table: a scheme entry pins both the builtin name
and its scheme. -/
theorem scheme_cases {id : String} {s : Scheme} (h : Builtins.scheme id = some s) :
    (id = "equal" ∧ s = ⟨1, pure2 (q 0) (q 0) boolean⟩) ∨
    (id = "fix" ∧ s = ⟨2, .fun (.fun (q 0) (q 1) (q 0)) (q 1) (q 0)⟩) ∨
    (id = "int_compare" ∧ s = .mono (pure2 integer integer Builtins.intCompareResult)) ∨
    (id = "int_add" ∧ s = .mono (pure2 integer integer integer)) ∨
    (id = "int_subtract" ∧ s = .mono (pure2 integer integer integer)) ∨
    (id = "int_multiply" ∧ s = .mono (pure2 integer integer integer)) ∨
    (id = "int_divide" ∧ s = .mono (pure2 integer integer (result integer unit))) ∨
    (id = "int_absolute" ∧ s = .mono (pure1 integer integer)) ∨
    (id = "int_parse" ∧ s = .mono (pure1 string (result integer unit))) ∨
    (id = "int_to_string" ∧ s = .mono (pure1 integer string)) ∨
    (id = "string_append" ∧ s = .mono (pure2 string string string)) ∨
    (id = "string_length" ∧ s = .mono (pure1 string integer)) ∨
    (id = "string_uppercase" ∧ s = .mono (pure1 string string)) ∨
    (id = "string_lowercase" ∧ s = .mono (pure1 string string)) ∨
    (id = "string_starts_with" ∧ s = .mono (pure2 string string boolean)) ∨
    (id = "string_ends_with" ∧ s = .mono (pure2 string string boolean)) := by
  unfold Builtins.scheme at h
  split at h <;> simp_all

/-- The stack-coupled `fix` builtin's preservation, isolated as a sub-hypothesis
(its `reduceCallBuiltin` arm pushes an `Apply` frame and yields the unscheme'd
`fixed` partial, so it is not covered by the generic `run`-typing). -/
def FixPreserves (m : Type) [BEq m] : Prop :=
  ∀ {applied : List (Value m)} {arg : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {argTy retTy ε τ : Ty},
    HasTypeV (.Partial (.Builtin "fix") applied) (.fun argTy ε retTy) →
    HasTypeV arg argTy →
    StackWf rest retTy ε τ →
    (∀ cfg', reduceCall (.Partial (.Builtin "fix") applied) arg ann fenv rest = .tau cfg' →
        MStateWf (.run cfg') τ ε) ∧
    (∀ v, reduceCall (.Partial (.Builtin "fix") applied) arg ann fenv rest = .done (.value v) →
        HasTypeV v τ)

/-- **`BuiltinAppPreserves` discharged** for the general builtins (every schemed
builtin except `fix`, which defers to `hfix`). Per builtin: `scheme_cases` pins the
name+scheme, the arity-1/2 driver peels the typed args and runs `Builtin.run`, and the
`run_*` lemma types the result. -/
theorem builtinAppPreserves [BEq m] (hfix : FixPreserves m) : BuiltinAppPreserves m := by
  intro id applied arg ann fenv rest argTy retTy ε τ hp harg hst
  cases hp with
  | @partialBuiltin _id s args _applied a' ε' r' _τ hs hpw he =>
    obtain ⟨ha, _, hr⟩ := Ty.tyEquiv_fun_components he
    have harg' : HasTypeV arg a' := harg.conv ha.symm
    rcases scheme_cases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- equal : ∀α. α → α → boolean
      exact builtinApp_arity2 (sargs := args) (D1 := args.getD 0 (Ty.var 0))
        (D2 := args.getD 0 (Ty.var 0))
        (R := Ty.boolean) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) hs
        (by simp [Scheme.instantiate, Ty.subst, Ty.pure2, Ty.q, Ty.boolean, Ty.union', Ty.rows,
          Ty.unit, Ty.record'])
        (fun _ _ hh => run_equal hh)
        (by simpa [Scheme.instantiate, Ty.subst, Ty.pure2, Ty.q] using hpw) harg' hr hst
    · -- fix (isolated)
      exact hfix (HasTypeV.partialBuiltin hs hpw he) harg hst
    · -- int_compare
      exact builtinApp_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) hs (sargs := args) (by simp [Scheme.instantiate_mono, Ty.pure2])
        (fun hx hy hh => run_int_compare hx hy hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hr hst
    · -- int_add
      exact builtinApp_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) hs (sargs := args) (by simp [Scheme.instantiate_mono, Ty.pure2])
        (fun hx hy hh => run_int_add hx hy hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hr hst
    · -- int_subtract
      exact builtinApp_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) hs (sargs := args) (by simp [Scheme.instantiate_mono, Ty.pure2])
        (fun hx hy hh => run_int_subtract hx hy hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hr hst
    · -- int_multiply
      exact builtinApp_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) hs (sargs := args) (by simp [Scheme.instantiate_mono, Ty.pure2])
        (fun hx hy hh => run_int_multiply hx hy hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hr hst
    · -- int_divide
      exact builtinApp_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) hs (sargs := args) (by simp [Scheme.instantiate_mono, Ty.pure2])
        (fun hx hy hh => run_int_divide hx hy hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hr hst
    · -- int_absolute
      exact builtinApp_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) (fun hx hh => run_int_absolute hx hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hr hst
    · -- int_parse
      exact builtinApp_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) (fun hx hh => run_int_parse hx hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hr hst
    · -- int_to_string
      exact builtinApp_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) (fun hx hh => run_int_to_string hx hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hr hst
    · -- string_append
      exact builtinApp_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) hs (sargs := args) (by simp [Scheme.instantiate_mono, Ty.pure2])
        (fun hx hy hh => run_string_append hx hy hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hr hst
    · -- string_length
      exact builtinApp_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) (fun hx hh => run_string_length hx hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hr hst
    · -- string_uppercase
      exact builtinApp_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) (fun hx hh => run_string_uppercase hx hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hr hst
    · -- string_lowercase
      exact builtinApp_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) (fun hx hh => run_string_lowercase hx hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hr hst
    · -- string_starts_with
      exact builtinApp_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) hs (sargs := args) (by simp [Scheme.instantiate_mono, Ty.pure2])
        (fun hx hy hh => run_string_starts_with hx hy hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hr hst
    · -- string_ends_with
      exact builtinApp_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro a e r h; cases h) hs (sargs := args) (by simp [Scheme.instantiate_mono, Ty.pure2])
        (fun hx hy hh => run_string_ends_with hx hy hh)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hr hst

/-! ### Discharging `BuiltinAppNoBadCrash` -/

/-- The `fix` builtin's no-bad-crash obligation, isolated. -/
def FixNoBadCrash (m : Type) [BEq m] : Prop :=
  ∀ {applied : List (Value m)} {arg : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {argTy retTy ε : Ty} {r : Reason m},
    HasTypeV (.Partial (.Builtin "fix") applied) (.fun argTy ε retTy) →
    HasTypeV arg argTy →
    reduceCall (.Partial (.Builtin "fix") applied) arg ann fenv rest = .done (.crash r) →
    ¬ Reason.IsBad r

/-- **Arity-1 no-bad-crash driver.** A typed arity-1 general builtin only crashes at
saturation when `run` traps, and a typed-arg trap is the sanctioned `Unrepresentable`. -/
theorem builtinNoBad_arity1 [BEq m] {key : String} {D R : Ty}
    (h1 : key ≠ "fix") (h2 : key ≠ "fixed") (h3 : key ≠ "list_fold") (h4 : key ≠ "binary_fold")
    (harity : Builtin.builtinArity key = some 1)
    {applied : List (Value m)} {arg : Value m} {ann : m} {fenv : Env m} {rest : Stack m}
    {a' ε' r' : Ty} {reason : Reason m}
    (hpw : BuiltinPartialWf (.fun D .empty R) applied (.fun a' ε' r'))
    (harg' : HasTypeV arg a')
    (hcrash : reduceCall (.Partial (.Builtin key) applied) arg ann fenv rest = .done (.crash reason))
    (hRna : ∀ a e r, R ≠ .fun a e r)
    (hrunNB : ∀ {x : Value m} {e}, HasTypeV x D → Builtin.run key [x] = .error e → ¬ Reason.IsBad e) :
    ¬ Reason.IsBad reason := by
  cases hpw with
  | nil =>
      rw [reduceCall_builtin_eq, List.nil_append] at hcrash
      cases hrun : Builtin.run key [arg] with
      | error e =>
          rw [reduceCallBuiltin_sat_crash h1 h2 h3 h4 harity rfl hrun] at hcrash
          simp only [ReduceStep.done.injEq, Outcome.crash.injEq] at hcrash
          subst hcrash; exact hrunNB harg' hrun
      | ok value =>
          rw [reduceCallBuiltin_sat h1 h2 h3 h4 harity rfl hrun] at hcrash; simp at hcrash
  | cons hv hrest =>
      cases hrest with
      | nil => exact absurd rfl (hRna _ _ _)
      | cons => exact absurd rfl (hRna _ _ _)

/-- **Arity-2 no-bad-crash driver.** Accumulation never crashes; saturation only
crashes on a sanctioned `Unrepresentable` trap (given typed args). -/
theorem builtinNoBad_arity2 [BEq m] {key : String} {D1 D2 R : Ty}
    (h1 : key ≠ "fix") (h2 : key ≠ "fixed") (h3 : key ≠ "list_fold") (h4 : key ≠ "binary_fold")
    (harity : Builtin.builtinArity key = some 2)
    {applied : List (Value m)} {arg : Value m} {ann : m} {fenv : Env m} {rest : Stack m}
    {a' ε' r' : Ty} {reason : Reason m}
    (hpw : BuiltinPartialWf (.fun D1 .empty (.fun D2 .empty R)) applied (.fun a' ε' r'))
    (harg' : HasTypeV arg a')
    (hcrash : reduceCall (.Partial (.Builtin key) applied) arg ann fenv rest = .done (.crash reason))
    (hRna : ∀ a e r, R ≠ .fun a e r)
    (hrunNB : ∀ {x y : Value m} {e}, HasTypeV x D1 → HasTypeV y D2 →
      Builtin.run key [x, y] = .error e → ¬ Reason.IsBad e) :
    ¬ Reason.IsBad reason := by
  cases hpw with
  | nil =>
      rw [reduceCall_builtin_eq, List.nil_append,
        reduceCallBuiltin_acc h1 h2 h3 h4 harity (by simp)] at hcrash
      simp at hcrash
  | @cons _ _ _ vval _ _ hv hrest =>
      cases hrest with
      | nil =>
          rw [reduceCall_builtin_eq] at hcrash
          cases hrun : Builtin.run key [vval, arg] with
          | error e =>
              rw [show [vval] ++ [arg] = [vval, arg] from rfl,
                reduceCallBuiltin_sat_crash h1 h2 h3 h4 harity rfl hrun] at hcrash
              simp only [ReduceStep.done.injEq, Outcome.crash.injEq] at hcrash
              subst hcrash; exact hrunNB hv harg' hrun
          | ok value =>
              rw [show [vval] ++ [arg] = [vval, arg] from rfl,
                reduceCallBuiltin_sat h1 h2 h3 h4 harity rfl hrun] at hcrash; simp at hcrash
      | cons _ hrest2 => cases hrest2 <;> exact absurd rfl (hRna _ _ _)

/-- **`BuiltinAppNoBadCrash` discharged** for the general builtins (all schemed
builtins except `fix`). A typed builtin application never crashes badly: the only
crash is a sanctioned `Unrepresentable` trap. -/
theorem builtinAppNoBadCrash [BEq m] (hfix : FixNoBadCrash m) : BuiltinAppNoBadCrash m := by
  intro id applied arg ann fenv rest argTy retTy ε r hp harg hcrash
  cases hp with
  | @partialBuiltin _id s args _applied a' ε' r' _τ hs hpw he =>
    obtain ⟨ha, _, _⟩ := Ty.tyEquiv_fun_components he
    have harg' : HasTypeV arg a' := harg.conv ha.symm
    rcases scheme_cases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- equal (never errors)
      exact builtinNoBad_arity2 (D1 := args.getD 0 (Ty.var 0)) (D2 := args.getD 0 (Ty.var 0))
        (R := Ty.boolean) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate, Ty.subst, Ty.pure2, Ty.q] using hpw) harg' hcrash
        (by intro a e r h; cases h) (fun _ _ herr => by simp [Builtin.run] at herr)
    · -- fix (isolated)
      exact hfix (HasTypeV.partialBuiltin hs hpw he) harg hcrash
    · -- int_compare (never errors)
      exact builtinNoBad_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hcrash
        (by intro a e r h; cases h)
        (fun hx hy herr => by
          obtain ⟨_, rfl⟩ := canonical_integer hx; obtain ⟨_, rfl⟩ := canonical_integer hy
          simp [Builtin.run, Cast.asInteger, bind, Except.bind] at herr)
    · -- int_add
      exact builtinNoBad_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hcrash
        (by intro a e r h; cases h) (fun hx hy herr => run_int_add_noBad hx hy herr)
    · -- int_subtract
      exact builtinNoBad_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hcrash
        (by intro a e r h; cases h) (fun hx hy herr => run_int_subtract_noBad hx hy herr)
    · -- int_multiply
      exact builtinNoBad_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hcrash
        (by intro a e r h; cases h) (fun hx hy herr => run_int_multiply_noBad hx hy herr)
    · -- int_divide (never errors)
      exact builtinNoBad_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hcrash
        (by intro a e r h; cases h)
        (fun hx hy herr => by
          obtain ⟨_, rfl⟩ := canonical_integer hx; obtain ⟨_, rfl⟩ := canonical_integer hy
          simp [Builtin.run, Cast.asInteger, bind, Except.bind] at herr)
    · -- int_absolute (never errors)
      exact builtinNoBad_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hcrash
        (by intro a e r h; cases h)
        (fun hx herr => by
          obtain ⟨_, rfl⟩ := canonical_integer hx
          simp [Builtin.run, Cast.asInteger, bind, Except.bind] at herr)
    · -- int_parse
      exact builtinNoBad_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hcrash
        (by intro a e r h; cases h) (fun hx herr => run_int_parse_noBad hx herr)
    · -- int_to_string (never errors)
      exact builtinNoBad_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hcrash
        (by intro a e r h; cases h)
        (fun hx herr => by
          obtain ⟨_, rfl⟩ := canonical_integer hx
          simp [Builtin.run, Cast.asInteger, bind, Except.bind] at herr)
    · -- string_append (never errors)
      exact builtinNoBad_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hcrash
        (by intro a e r h; cases h)
        (fun hx hy herr => by
          obtain ⟨_, rfl⟩ := canonical_string hx; obtain ⟨_, rfl⟩ := canonical_string hy
          simp [Builtin.run, Cast.asString, bind, Except.bind] at herr)
    · -- string_length (never errors)
      exact builtinNoBad_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hcrash
        (by intro a e r h; cases h)
        (fun hx herr => by
          obtain ⟨_, rfl⟩ := canonical_string hx
          simp [Builtin.run, Cast.asString, bind, Except.bind] at herr)
    · -- string_uppercase (never errors)
      exact builtinNoBad_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hcrash
        (by intro a e r h; cases h)
        (fun hx herr => by
          obtain ⟨_, rfl⟩ := canonical_string hx
          simp [Builtin.run, Cast.asString, bind, Except.bind] at herr)
    · -- string_lowercase (never errors)
      exact builtinNoBad_arity1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure1] using hpw) harg' hcrash
        (by intro a e r h; cases h)
        (fun hx herr => by
          obtain ⟨_, rfl⟩ := canonical_string hx
          simp [Builtin.run, Cast.asString, bind, Except.bind] at herr)
    · -- string_starts_with (never errors)
      exact builtinNoBad_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hcrash
        (by intro a e r h; cases h)
        (fun hx hy herr => by
          obtain ⟨_, rfl⟩ := canonical_string hx; obtain ⟨_, rfl⟩ := canonical_string hy
          simp [Builtin.run, Cast.asString, bind, Except.bind] at herr)
    · -- string_ends_with (never errors)
      exact builtinNoBad_arity2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simpa [Scheme.instantiate_mono, Ty.pure2] using hpw) harg' hcrash
        (by intro a e r h; cases h)
        (fun hx hy herr => by
          obtain ⟨_, rfl⟩ := canonical_string hx; obtain ⟨_, rfl⟩ := canonical_string hy
          simp [Builtin.run, Cast.asString, bind, Except.bind] at herr)

/-! ## Headline theorems with the builtin obligations discharged

`preservation`/`progress`/`soundness_value` were stated relative to the isolated
`BuiltinAppPreserves`/`BuiltinAppNoBadCrash` hypotheses (T3/T6 fork). T6b discharges
those for the entire general-builtin table, so the only residual builtin assumption is
the stack-coupled `fix` (`FixPreserves`/`FixNoBadCrash`). -/

/-- **Preservation** with the general-builtin obligation discharged (only `fix` left). -/
theorem preservation_fix [BEq m] (hfix : FixPreserves m)
    {s s' : MState m} {μ : Label m} {τ ε : Ty}
    (hwf : MStateWf s τ ε) (hr : Reduce s μ s') (hrep : ReplyContract ε s μ) :
    ∃ ε', MStateWf s' τ ε' :=
  preservation (builtinAppPreserves hfix) hwf hr hrep

/-- **Value soundness** with the general-builtin obligation discharged (only `fix` left). -/
theorem soundness_value_fix [BEq m] (hfix : FixPreserves m) (fuel : Nat) {cfg : Config m}
    {τ ε : Ty} {v : Value m} (hwf : MStateWf (.run cfg) τ ε)
    (h : evalR fuel cfg = .done (.value v)) : HasTypeV v τ :=
  soundness_value (builtinAppPreserves hfix) fuel hwf h

/-- **Progress** with the general-builtin no-bad-crash obligation discharged (only `fix`
left): a well-typed state steps, is a value, suspends on an in-row effect, or crashes
only with the sanctioned `Unrepresentable`. -/
theorem progress_fix [BEq m] (hfix : FixNoBadCrash m)
    {cfg : Config m} {τ ε : Ty} (hwf : MStateWf (.run cfg) τ ε) :
    (∃ cfg', reduce1Run cfg = .tau cfg') ∨ (∃ v, reduce1Run cfg = .done (.value v)) ∨
    (∃ r, reduce1Run cfg = .done (.crash r) ∧ ¬ Reason.IsBad r) ∨
    (∃ op lift envP kP, reduce1Run cfg = .perform op lift envP kP ∧
      ∃ a b, Ty.EffContains ε op a b) :=
  progress (builtinAppNoBadCrash hfix) hwf

/-- **Whole-program value soundness over `evalR`.** A closed well-typed program whose
transparent `evalR` terminates with a value yields a value of the program's type — the
end-to-end statement combining `mStateWf_initial` (a well-typed program is a well-typed
initial state) with `soundness_value_fix`. Modulo the isolated `fix` obligation, this
holds for the whole general-builtin language. -/
theorem soundness_evalR_value [BEq m] (hfix : FixPreserves m) {prog : Tree.Node m}
    {τ ε : Ty} {v : Value m} (fuel : Nat) (hty : HasType [] prog τ ε)
    (h : evalR fuel (Config.initial prog) = .done (.value v)) : HasTypeV v τ :=
  soundness_value_fix hfix fuel (mStateWf_initial hty) h

/-- **No-bad-crash over `evalR`.** A well-typed config whose `evalR` terminates in a
crash only ever reaches the *sanctioned* `Unrepresentable` trap — never a type-error
crash (`Vacant`/`NotAFunction`/`NoMatch`/…). Fuel induction folding `preservation_fix`
(step) and `progress_fix` (the terminal crash is `¬ IsBad`). -/
theorem soundnessR_noBadCrash [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m) :
    ∀ (fuel : Nat) {cfg : Config m} {τ ε : Ty} {r : Reason m},
      MStateWf (.run cfg) τ ε → evalR fuel cfg = .done (.crash r) → ¬ Reason.IsBad r := by
  intro fuel
  induction fuel with
  | zero => intro cfg τ ε r _ h; simp [evalR] at h
  | succ n ih =>
      intro cfg τ ε r hwf h
      rw [evalR_succ] at h
      cases hrr : reduce1Run cfg with
      | tau cfg' =>
          rw [hrr] at h
          obtain ⟨ε', hwf'⟩ := preservation_fix hpres hwf (Reduce.tau hrr) trivial
          exact ih hwf' h
      | done o =>
          rw [hrr] at h
          obtain rfl : o = .crash r := by injection h
          rcases progress_fix hbad hwf with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc, hnb⟩ | ⟨_, _, _, _, hc, _⟩
          · rw [hrr] at hc; simp at hc
          · rw [hrr] at hc; simp at hc
          · rw [hrr] at hc; simp only [ReduceStep.done.injEq, Outcome.crash.injEq] at hc
            subst hc; exact hnb
          · rw [hrr] at hc; simp at hc
      | perform op lift envP kP => rw [hrr] at h; simp [evalR] at h

/-- **Whole-program no-bad-crash over `evalR`.** A closed well-typed program's `evalR`
never terminates in a *bad* crash (only the sanctioned `Unrepresentable`), modulo the
isolated `fix` obligation. -/
theorem soundness_evalR_noBadCrash [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m)
    {prog : Tree.Node m} {τ ε : Ty} {r : Reason m} (fuel : Nat) (hty : HasType [] prog τ ε)
    (h : evalR fuel (Config.initial prog) = .done (.crash r)) : ¬ Reason.IsBad r :=
  soundnessR_noBadCrash hpres hbad fuel (mStateWf_initial hty) h

/-- Tau-preservation keeping `ε`, in `fix`-discharged form. -/
theorem preservation_tau_fix [BEq m] (hfix : FixPreserves m) {cfg cfg' : Config m} {τ ε : Ty}
    (hwf : MStateWf (.run cfg) τ ε) (h : reduce1Run cfg = .tau cfg') :
    MStateWf (.run cfg') τ ε :=
  preservation_tau (builtinAppPreserves hfix) hwf h

/-- **Effect safety over `evalR`.** If a well-typed config's `evalR` terminates by
*emitting an effect* `op`, then `op` is a member of the ambient row `ε` (the run can
only escape on a declared effect). Fuel induction threading `ε` across silent steps
(`preservation_tau_fix`) and reading the membership off `progress_fix`'s effect-escape
disjunct at the boundary. -/
theorem soundnessR_effect [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m) :
    ∀ (fuel : Nat) {cfg : Config m} {τ ε : Ty} {op : String} {lift : Value m}
      {resume : Value m → Config m},
      MStateWf (.run cfg) τ ε → evalR fuel cfg = .effect op lift resume →
      ∃ a b, Ty.EffContains ε op a b := by
  intro fuel
  induction fuel with
  | zero => intro cfg τ ε op lift resume _ h; simp [evalR] at h
  | succ n ih =>
      intro cfg τ ε op lift resume hwf h
      rw [evalR_succ] at h
      cases hrr : reduce1Run cfg with
      | tau cfg' => rw [hrr] at h; exact ih (preservation_tau_fix hpres hwf hrr) h
      | done o => rw [hrr] at h; simp [evalR] at h
      | perform op' lift' envP kP =>
          rw [hrr] at h
          obtain ⟨rfl, rfl, _⟩ := by simpa only [Result.effect.injEq] using h
          rcases progress_fix hbad hwf with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc, _⟩ |
            ⟨_, _, _, _, hc, ha⟩
          · rw [hrr] at hc; simp at hc
          · rw [hrr] at hc; simp at hc
          · rw [hrr] at hc; simp at hc
          · rw [hrr] at hc
            obtain ⟨rfl, _, _, _⟩ := by simpa only [ReduceStep.perform.injEq] using hc
            exact ha

/-- **Whole-program soundness over `evalR` (the trichotomy + effect escape).** A closed
well-typed program's `evalR` at any fuel is: a timeout; a value of type `τ`; a
*sanctioned* `Unrepresentable` crash (never a type-error crash); or an emitted effect
`op ∈ ε`. Modulo the isolated `fix` obligation, this is whole-program soundness for the
general-builtin language over the transparent evaluator. -/
theorem soundness_evalR [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m)
    {prog : Tree.Node m} {τ ε : Ty} (fuel : Nat) (hty : HasType [] prog τ ε) :
    evalR fuel (Config.initial prog) = .timeout ∨
    (∃ v, evalR fuel (Config.initial prog) = .done (.value v) ∧ HasTypeV v τ) ∨
    (∃ r, evalR fuel (Config.initial prog) = .done (.crash r) ∧ ¬ Reason.IsBad r) ∨
    (∃ op lift resume, evalR fuel (Config.initial prog) = .effect op lift resume ∧
      ∃ a b, Ty.EffContains ε op a b) := by
  cases h : evalR fuel (Config.initial prog) with
  | timeout => exact Or.inl rfl
  | done o =>
      cases o with
      | value v => exact Or.inr (Or.inl ⟨v, rfl, soundness_evalR_value hpres fuel hty h⟩)
      | crash r =>
          exact Or.inr (Or.inr (Or.inl ⟨r, rfl, soundness_evalR_noBadCrash hpres hbad fuel hty h⟩))
  | effect op lift resume =>
      exact Or.inr (Or.inr (Or.inr ⟨op, lift, resume, rfl,
        soundnessR_effect hpres hbad fuel (mStateWf_initial hty) h⟩))

/-- **Purity certificate (`A ! ∅`).** A program typed at the **empty** effect row never
emits an effect: its `evalR` is never `.effect _ _ _`. (Eff's `A!∅` purity certificate —
follows from effect safety, since the empty row has no members.) -/
theorem pure_no_perform_evalR [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m)
    {prog : Tree.Node m} {τ : Ty} {op : String} {lift : Value m} {resume : Value m → Config m}
    (fuel : Nat) (hty : HasType [] prog τ .empty)
    (h : evalR fuel (Config.initial prog) = .effect op lift resume) : False := by
  obtain ⟨a, b, hc⟩ := soundnessR_effect hpres hbad fuel (mStateWf_initial hty) h
  cases hc

/-- **Whole-program soundness for a pure program.** A program typed at the empty effect
row has only three `evalR` outcomes — timeout, a typed value, or a sanctioned
`Unrepresentable` crash — *never* an emitted effect. The pure specialization of
`soundness_evalR`. -/
theorem soundness_evalR_pure [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m)
    {prog : Tree.Node m} {τ : Ty} (fuel : Nat) (hty : HasType [] prog τ .empty) :
    evalR fuel (Config.initial prog) = .timeout ∨
    (∃ v, evalR fuel (Config.initial prog) = .done (.value v) ∧ HasTypeV v τ) ∨
    (∃ r, evalR fuel (Config.initial prog) = .done (.crash r) ∧ ¬ Reason.IsBad r) := by
  rcases soundness_evalR hpres hbad fuel hty with h | h | h | ⟨op, lift, resume, h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (pure_no_perform_evalR hpres hbad fuel hty h).elim

/-! ## Soundness at the `BehaviorsR` level (silent terminations)

Lifting the per-fuel `evalR` soundness to observable `BehaviorsR` membership via the
`MTr ⟶ evalR` bridge (`evalR_complete`). A *silent* terminating behaviour (the trace a
closed run exhibits up to its terminal outcome) of a well-typed program is never a bad
crash, and a terminating value is typed. (The general, reply-containing traces are the
open-system T7 remainder, needing the `ReplyContract` across `reply` steps.) -/

/-- **No bad crash in `BehaviorsR`.** A well-typed program never has a silent
terminating behaviour that crashes badly. -/
theorem soundness_behaviorsR_noBadCrash [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m)
    {prog : Tree.Node m} {τ ε : Ty} {trace : List (Label m)} {r : Reason m}
    (hty : HasType [] prog τ ε) (hsilent : ∀ μ ∈ trace, μ = Label.tau)
    (hmem : Behavior.terminates trace (.crash r) ∈ BehaviorsR (Config.initial prog)) :
    ¬ Reason.IsBad r := by
  obtain ⟨s', hmtr, hterm⟩ := hmem
  obtain ⟨fuel, hf⟩ := evalR_complete hmtr hsilent hterm _ rfl
  exact soundness_evalR_noBadCrash hpres hbad fuel hty hf

/-- **Typed value in `BehaviorsR`.** A well-typed program's silent terminating value
behaviour yields a value of the program's type. -/
theorem soundness_behaviorsR_value [BEq m] (hpres : FixPreserves m)
    {prog : Tree.Node m} {τ ε : Ty} {trace : List (Label m)} {v : Value m}
    (hty : HasType [] prog τ ε) (hsilent : ∀ μ ∈ trace, μ = Label.tau)
    (hmem : Behavior.terminates trace (.value v) ∈ BehaviorsR (Config.initial prog)) :
    HasTypeV v τ := by
  obtain ⟨s', hmtr, hterm⟩ := hmem
  obtain ⟨fuel, hf⟩ := evalR_complete hmtr hsilent hterm _ rfl
  exact soundness_evalR_value hpres fuel hty hf

/-- **Effect safety in `BehaviorsR` (open-boundary suspension).** A well-typed program
that *suspends* at the boundary performing `op` does so on an operation **in its declared
effect row** `ε` (`op ∈ ε`) — the open-system effect-safety statement. Via the
`evalR_complete_effect` bridge (a single-`perform` observable trace is realized by an
`evalR` effect emission) + `soundnessR_effect`. -/
theorem soundness_behaviorsR_suspended [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m)
    {prog : Tree.Node m} {τ ε : Ty} {trace : List (Label m)} {op : String} {lift : Value m}
    (hty : HasType [] prog τ ε)
    (hmem : Behavior.suspended trace op lift ∈ BehaviorsR (Config.initial prog)) :
    ∃ a b, Ty.EffContains ε op a b := by
  obtain ⟨envP, kP, hmtr, hobs⟩ := hmem
  obtain ⟨fuel, resume, hf⟩ := evalR_complete_effect hmtr hobs _ rfl
  exact soundnessR_effect hpres hbad fuel (mStateWf_initial hty) hf

/-- **Headline soundness (T7).** A closed well-typed program `prog : τ ! ε` does not go
wrong. Bundling the per-shape results over the transparent observable layer `BehaviorsR`
(modulo the isolated `fix`), every behaviour the program exhibits satisfies:

1. a *silent* terminating **value** is well-typed (`HasTypeV v τ`);
2. a *silent* terminating **crash** is never *bad* — only the sanctioned
   `Unrepresentable` trap, never a type-error crash (`Vacant`/`NotAFunction`/`NoMatch`/…);
3. a boundary **suspension** performs an operation **in the declared row** (`op ∈ ε`).

(The remaining `BehaviorsR` shapes — reply-resumed terminations and `diverges` — are the
open-system / coinductive T7 remainder.) -/
theorem soundness [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m)
    {prog : Tree.Node m} {τ ε : Ty} (hty : HasType [] prog τ ε) :
    (∀ {trace : List (Label m)} {v : Value m}, (∀ μ ∈ trace, μ = Label.tau) →
        Behavior.terminates trace (.value v) ∈ BehaviorsR (Config.initial prog) →
        HasTypeV v τ) ∧
    (∀ {trace : List (Label m)} {r : Reason m}, (∀ μ ∈ trace, μ = Label.tau) →
        Behavior.terminates trace (.crash r) ∈ BehaviorsR (Config.initial prog) →
        ¬ Reason.IsBad r) ∧
    (∀ {trace : List (Label m)} {op : String} {lift : Value m},
        Behavior.suspended trace op lift ∈ BehaviorsR (Config.initial prog) →
        ∃ a b, Ty.EffContains ε op a b) :=
  ⟨fun hs hm => soundness_behaviorsR_value hpres hty hs hm,
   fun hs hm => soundness_behaviorsR_noBadCrash hpres hbad hty hs hm,
   fun hm => soundness_behaviorsR_suspended hpres hbad hty hm⟩

end Eyg.Types
