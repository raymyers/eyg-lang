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

/-! ## Effect weakening is admissible (T6b / Open Question 3)

With the generalized `app` rule (latent `εf` weakenable to ambient `ε`), the term-level
weakening `HasType Γ e τ ε₁ → EffWeaken ε₁ ε₂ → HasType Γ e τ ε₂` becomes **admissible**:
values/literals/data/`perform` are already `ε`-polymorphic, `app` threads
`effWeaken_trans`, and `conv` absorbs the ambient `TyEquiv`. This is what re-types a
closure's body at the ambient when its latent was weakened (the preservation crux), and
the lemma the `fix` slice uses (via `effWeaken_empty` for the pure builder). -/

/-- Auxiliary: weakening with the target row `ε₂` explicit, for a clean induction motive. -/
theorem weakenEffAux {Γ : Ctx} {e : Tree.Node m} {τ ε₁ : Ty}
    (h : HasType Γ e τ ε₁) : ∀ (ε₂ : Ty), Ty.EffWeaken ε₁ ε₂ → HasType Γ e τ ε₂ := by
  induction h with
  | var hl => exact fun _ _ => HasType.var hl
  | lam hbody _ => exact fun _ _ => HasType.lam hbody
  | @app _ _ _ _ εf _ _ _ _ hwf _ ihf iharg =>
      exact fun ε₂ hw => HasType.app (ihf ε₂ hw) (Ty.effWeaken_trans hwf hw) (iharg ε₂ hw)
  | let_ _ _ ihdefn ihbody => exact fun ε₂ hw => HasType.let_ (ihdefn ε₂ hw) (ihbody ε₂ hw)
  | int => exact fun _ _ => HasType.int
  | str => exact fun _ _ => HasType.str
  | bin => exact fun _ _ => HasType.bin
  | builtin hs => exact fun _ _ => HasType.builtin hs
  | tail => exact fun _ _ => HasType.tail
  | cons => exact fun _ _ => HasType.cons
  | tag => exact fun _ _ => HasType.tag
  | nocases => exact fun _ _ => HasType.nocases
  | case_ => exact fun _ _ => HasType.case_
  | select => exact fun _ _ => HasType.select
  | extend => exact fun _ _ => HasType.extend
  | overwrite => exact fun _ _ => HasType.overwrite
  | empty => exact fun _ _ => HasType.empty
  | perform => exact fun _ _ => HasType.perform
  | handle => exact fun _ _ => HasType.handle
  | @conv _ _ _ _ _ _ _ hτ hε ih =>
      exact fun ε₂ hw => HasType.conv (ih ε₂ (Ty.effWeaken_trans (.inl hε) hw)) hτ (.refl _)

/-- **Effect weakening** (admissible): a well-typed term stays well-typed when its
ambient effect row is weakened. -/
theorem weakenEff {Γ : Ctx} {e : Tree.Node m} {τ ε₁ ε₂ : Ty}
    (h : HasType Γ e τ ε₁) (hw : Ty.EffWeaken ε₁ ε₂) : HasType Γ e τ ε₂ :=
  weakenEffAux h ε₂ hw

/-- **A performed operation is in the (weakened) ambient.** If a function's latent row
`εf` is `TyEquiv`-headed by `l : (a, b)` and `εf` weakens to `ε`, then `ε` carries `l`
(the weakening cannot be the empty case, since `εf` has a member). This is the
effect-safety hinge across application weakening. -/
theorem perform_op_mem_ambient {l : String} {a b μ εf ε : Ty}
    (hE : Ty.TyEquiv (.effectExtend l a b μ) εf) (hw : Ty.EffWeaken εf ε) :
    ∃ a' b', Ty.EffContains ε l a' b' ∧ Ty.TyEquiv a a' ∧ Ty.TyEquiv b b' := by
  obtain ⟨_, _, hcf, _, _⟩ := Ty.tyEquiv_effContains_mp hE Ty.EffContains.head
  have hee : Ty.TyEquiv εf ε := by
    rcases hw with hw | hw
    · exact hw
    · obtain ⟨_, _, hc', _, _⟩ := Ty.tyEquiv_effContains_mp hw hcf; nomatch hc'
  exact Ty.tyEquiv_effContains_mp (hE.trans hee) Ty.EffContains.head

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

/-- **`doPerformR` only ever errors with `UnhandledEffect label arg`** (structural —
the matching-`Delimit` arm returns `.ok`, the `[]` base is the only `.error`, every
other frame recurses). This replaces the now-false `stackWf_doPerformR_unhandled` (a
typed stack *can* carry a `Delimit` once `Handle` is typed) for recovering `op = label`
on an escape. -/
theorem doPerformR_error_form [BEq m] {label : String} {arg : Value m} {env : Env m}
    {e : Reason m} (k : Stack m) (acc : List (Kontinue m × m))
    (h : doPerformR label arg env k acc = .error e) : e = .UnhandledEffect label arg := by
  induction k generalizing acc with
  | nil => simp only [doPerformR] at h; cases h; rfl
  | cons hd rest ih =>
      obtain ⟨kont, mt⟩ := hd
      cases kont with
      | Delimit l hh ee shallow =>
          simp only [doPerformR] at h
          split at h
          · exact absurd h (by simp)
          · exact ih _ h
      | _ => simp only [doPerformR] at h <;> exact ih _ h

/-- A `reducePerform` that reports a `.perform` did so **unhandled** at the boundary:
the performed op/lift/env/stack are exactly the call's. (Via `doPerformR_error_form`.) -/
theorem reducePerform_perform_inv [BEq m] {label : String} {arg : Value m} {env : Env m}
    {k : Stack m} {op : String} {lift : Value m} {envP : Env m} {kP : Stack m}
    (h : reducePerform label arg env k = .perform op lift envP kP) :
    op = label ∧ lift = arg ∧ envP = env ∧ kP = k := by
  unfold reducePerform at h
  split at h
  · exact absurd h (by simp)
  · next o l hde =>
      injection h with h1 h2 h3 h4
      have hee := doPerformR_error_form _ _ hde
      injection hee with ho hl
      exact ⟨h1.symm.trans ho, h2.symm.trans hl, h3.symm, h4.symm⟩
  · exact absurd h (by simp)

/-- Move a `wait`-state's ambient row across a `TyEquiv` (the inversion lemmas expose an
`ε0` with `TyEquiv ε ε0`; this carries the `wait` typing back to the outer `ε`). -/
theorem mStateWf_wait_conv [BEq m] {op : String} {e : Env m} {k : Stack m} {τ ε ε0 : Ty}
    (h : MStateWf (.wait op e k) τ ε0) (hε : Ty.TyEquiv ε ε0) :
    MStateWf (.wait op e k) τ ε := by
  obtain ⟨a, b, replyTy, hEff, hbr, hsk⟩ := h
  obtain ⟨a', b', hEff', _, hbb'⟩ := (Ty.tyEquiv_effContains hε).2 op a b hEff
  exact ⟨a', b', replyTy, hEff', hbb'.symm.trans hbr, StackWf.conv hsk (.refl _) hε.symm⟩

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
      obtain ⟨argTy, εf, hw, hf, harg⟩ := inv_app hty
      exact ⟨Γ, _, henv, hf, StackWf.arg henv harg hw hst⟩
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
  | Handle l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨lift, reply, tail, ret, heq⟩ := inv_handle hty
      exact ⟨τin, HasTypeV.partialHandleNil heq, hst⟩
  | _ =>
      exfalso
      rcases hasType_expr_form hty with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ |
        ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h | h | h | ⟨_, h⟩ | h | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h

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

/-! ## The `fixed` partial: re-application (`fix` unrolling)

`fix builder = builder (fix builder)`. When the internal `fixed builder` value (typed
via `HasTypeV.partialFixed` at an arrow `D →⟨γ⟩ R`) is applied to an argument, the
machine pushes `Apply builder :: CallWith arg`: it computes `builder (fixed builder)`
(the unrolled recursive function) and applies it to `arg`. The two lemmas below — the
reduction equation and its preservation — are shared by `preservation_V` and
`builtinAppPreserves` (both reach the `fixed` value). -/

/-- The `fixed` partial's `reduceCall` always pushes the unrolling frames (`fix`'s
`builder (fix builder)`). A `rfl` reduction over the concrete `"fixed"` key. -/
theorem reduceCall_fixed [BEq m] (builder arg : Value m) (ann : m) (fenv : Env m)
    (rest : Stack m) :
    reduceCall (.Partial (.Builtin "fixed") [builder]) arg ann fenv rest =
      .tau (.V (.Partial (.Builtin "fixed") [builder]), fenv,
        (Kontinue.Apply builder fenv, ann) :: (Kontinue.CallWith arg fenv, ann) :: rest) :=
  rfl

/-- **`fixed` re-application preserves typing.** The unrolling successor `builder (fixed
builder) arg` is well-typed at the answer `τ`: feed the `fixed builder : D→⟨γ⟩R` value
into `Apply builder` (the **pure** builder consumes it, `EffWeaken ∅ ε` discharged by
`effWeaken_empty`), yielding the recursive function, then `CallWith arg` applies it
(`EffWeaken γ ε = hw`, supplied by the calling frame). The builder is converted to the
frame's exact arrow form, sidestepping any stack-endpoint conversion. -/
theorem fixed_reapply_preserves [BEq m] {builder arg : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {D γ R argTy εf retTy ε τ : Ty}
    (hbuilder : HasTypeV builder (.fun (.fun D γ R) .empty (.fun D γ R)))
    (he : Ty.TyEquiv (.fun D γ R) (.fun argTy εf retTy))
    (harg : HasTypeV arg argTy) (hw : Ty.EffWeaken εf ε) (hrest : StackWf rest retTy ε τ) :
    MStateWf (.run (.V (.Partial (.Builtin "fixed") [builder]), fenv,
      (Kontinue.Apply builder fenv, ann) :: (Kontinue.CallWith arg fenv, ann) :: rest)) τ ε := by
  have hb' : HasTypeV builder (.fun (.fun argTy εf retTy) .empty (.fun argTy εf retTy)) :=
    hbuilder.conv (.congrFun he (.refl _) he)
  exact ⟨_, HasTypeV.partialFixed hb' (.refl _),
    StackWf.applyf hb' (Ty.effWeaken_empty _) (StackWf.callwith harg hw hrest)⟩

/-- The builtin **application/saturation** preservation obligation, isolated as a
hypothesis (the **T6** deliverable — it needs the per-builtin `Builtin.run` typing,
and `int_add` may legitimately trap with the sanctioned `Unrepresentable`). When a
typed `Partial (Builtin id)` is applied to a typed argument and the machine takes a
`tau` step (i.e. the builtin did *not* crash), the successor stays well-typed. -/
def BuiltinAppPreserves (m : Type) [BEq m] : Prop :=
  ∀ {id : String} {applied : List (Value m)} {arg : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {argTy εf retTy ε τ : Ty},
    HasTypeV (.Partial (.Builtin id) applied) (.fun argTy εf retTy) →
    HasTypeV arg argTy →
    Ty.EffWeaken εf ε →
    StackWf rest retTy ε τ →
    (∀ cfg', reduceCall (.Partial (.Builtin id) applied) arg ann fenv rest = .tau cfg' →
        MStateWf (.run cfg') τ ε) ∧
    (∀ v, reduceCall (.Partial (.Builtin id) applied) arg ann fenv rest = .done (.value v) →
        HasTypeV v τ)

/-! **The three handler-dispatch obligations are now all DISCHARGED** (the T5 novel core —
no precedent — plus the effect-weakening row-threading at `Delimit`), proved below and
called directly from `preservation_V`:
* `install` — saturated `Handle l` (`reduceDeep`): `install_preserves`, via the generalized
  `StackWf.delimit` (row subsumption `tail ⊑ ε`).
* `resume` — `Resume acc` applied to a reply: `resume_preserves`, via the generalized
  `StackSegWf.delimit` + the quantified `partialResume`.
* `perform` — `Perform l` whose stack has a matching `Delimit` (the stack walk to it,
  building the reified `Resume`): `perform_preserves`/`perform_walk`, via the generalized
  `StackSegWf.nil` + `stackSeg_conv_input`/`_output` + `hasType_ctxConv`.
So there is no remaining handler-dispatch hypothesis — `preservation`/`progress`/`soundness*`
no longer assume any `HandlerObligations`. -/

/-! ### Discharging the handler dispatches

`install_preserves` and `resume_preserves` below discharge the `install` and `resume`
dispatches **fully generally** (no exact-row hypothesis), via the generalized
`StackWf.delimit`/`StackSegWf.delimit` (which discharge a label from the *ambient* with
`tail ⊑ ε`) and the discharge-row-quantified `partialResume`. They are called directly from
`preservation_V`, as is the `perform` stack-walk dispatch (`perform_preserves`/`perform_walk`,
design §5). All three handler dispatches are proved — no `HandlerObligations` hypothesis remains. -/

/-- **`Resume` dispatch — fully general.** Feeding the reply `v` into the reified
continuation `move acc rest` is well-typed at any ambient `ε`. The captured segment is
stored **quantified over its discharge row** (`partialResume`), so instantiate it at the
call ambient `ε` (the handler's `tail ⊑ ε` via the frame's `EffWeaken`), then compose it
onto `rest` (still at `ε`) with `stackWf_resume`. This is what handles the escaping
pure-tail resumption (`tail ≈ ∅`) invoked in an effectful context — no exact-row
hypothesis needed (the earlier `resume_preserves_exact` was the `ε ≈ tail` special case). -/
theorem resume_preserves [BEq m] {acc : Stack m} {iEnv : Env m} {v : Value m}
    {ann : m} {fenv : Env m} {rest : Stack m} {argTy εf retTy ε τ : Ty} {cfg' : Config m}
    (hres : HasTypeV (.Partial (.Resume acc iEnv) [] : Value m) (.fun argTy εf retTy))
    (hv : HasTypeV v argTy) (hw : Ty.EffWeaken εf ε) (hrest : StackWf rest retTy ε τ)
    (hr : reduceCall (.Partial (.Resume acc iEnv) []) v ann fenv rest = .tau cfg') :
    ∃ ε', MStateWf (.run cfg') τ ε' := by
  cases hres with
  | partialResume hseg he =>
      obtain ⟨ha, heff, hr'⟩ := Ty.tyEquiv_fun_components he
      rw [show reduceCall (.Partial (.Resume acc iEnv) []) v ann fenv rest
          = .tau (.V v, iEnv, move acc rest) from rfl] at hr
      cases hr
      have htailW : Ty.EffWeaken _ ε := hw.imp (fun h => heff.trans h) (fun h => heff.trans h)
      exact ⟨_, _, hv.conv ha.symm,
        stackWf_resume (hseg ε htailW) (StackWf.conv hrest hr'.symm (.refl _))⟩

/-- **`Handle` install dispatch — fully general.** `reduceDeep` pushes `Apply exec ::
Delimit l handler :: rest`: the exec runs under the handled row `⟨l:(lift,reply)|tail⟩`, the
**generalized** `Delimit` discharges `l` and lets `rest` continue at the call ambient `ε`
with `tail ⊑ ε` (`EffWeaken tail ε`, derived from the handle's `EffWeaken εf ε` since the
discharged latent `εf ≈ tail`). No exact-row hypothesis is needed — the successor is
well-typed at `ε' = ⟨l:(lift,reply)|tail⟩` (the exec's row). -/
theorem install_preserves [BEq m] {l : String} {handler v : Value m}
    {ann : m} {fenv : Env m} {rest : Stack m} {argTy εf retTy ε τ : Ty} {cfg' : Config m}
    (hh : HasTypeV (.Partial (.Handle l) [handler] : Value m) (.fun argTy εf retTy))
    (hv : HasTypeV v argTy) (hw : Ty.EffWeaken εf ε) (hrest : StackWf rest retTy ε τ)
    (hr : reduceCall (.Partial (.Handle l) [handler]) v ann fenv rest = .tau cfg') :
    ∃ ε', MStateWf (.run cfg') τ ε' := by
  cases hh with
  | partialHandleOne hhandler he =>
      obtain ⟨ha, heff, hr'⟩ := Ty.tyEquiv_fun_components he
      rw [show reduceCall (.Partial (.Handle l) [handler]) v ann fenv rest
          = .tau (.V unit, fenv,
              (Kontinue.Apply v fenv, ann) :: (Kontinue.Delimit l handler fenv false, ann) :: rest)
          from rfl] at hr
      cases hr
      exact ⟨_, _, hasTypeV_unit,
        StackWf.applyf (hv.conv ha.symm) (Ty.effWeaken_refl _)
          (StackWf.delimit hhandler (hw.imp (fun h => heff.trans h) (fun h => heff.trans h))
            (StackWf.conv hrest hr'.symm (.refl _)))⟩

/-- No operation is a member of the empty effect row. -/
theorem effContains_empty {l : String} {a b : Ty} (h : Ty.EffContains .empty l a b) : False := by
  cases h

/-- **`perform` dispatch — the stack walk (design §5).** `doPerformR` walks `rest`,
accumulating the traversed frames into `acc` (the deep re-push), to the nearest matching
`Delimit label`; on `.ok` the handled successor (`handler` applied to `arg : lift` then
`resume : kontTy`) is well-typed. Proved by induction on `rest`: the invariant threads
`StackWf rest σcur εcur τ`, the current operation binding `EffContains εcur label lift
reply` (with `v : lift`), and the captured prefix as a segment `StackSegWf acc.reverse
reply εtop σcur εcur`. Non-`Delimit` frames extend the segment (`stackSeg_append`, bridging
the inversion `TyEquiv` slack via `stackSeg_conv_input/output`); a non-matching `Delimit l'`
discharges `l'` and keeps `label` in the shrunk row; the matching `Delimit` builds the
resume via the quantified `partialResume` and types the handler application. -/
theorem perform_walk [BEq m] {label : String} {v : Value m} {iEnv : Env m} (rest : Stack m) :
    ∀ {acc : Stack m} {σcur εcur εtop τ lift reply : Ty} {cfg' : Config m},
      HasTypeV v lift →
      StackWf rest σcur εcur τ →
      Ty.EffContains εcur label lift reply →
      StackSegWf acc.reverse reply εtop σcur εcur →
      doPerformR label v iEnv rest acc = .ok cfg' →
      ∃ ε', MStateWf (.run cfg') τ ε' := by
  induction rest with
  | nil => intro acc σcur εcur εtop τ lift reply cfg' _ _ _ _ hdp; simp [doPerformR] at hdp
  | cons hd rest' ih =>
      intro acc σcur εcur εtop τ lift reply cfg' hv hrest hmem hacc hdp
      obtain ⟨kont, mt⟩ := hd
      cases kont with
      | Trace w =>
          simp only [doPerformR] at hdp
          have hacc' : StackSegWf ((Kontinue.Trace w, mt) :: acc).reverse reply εtop σcur εcur := by
            rw [List.reverse_cons]; exact stackSeg_append hacc (.trace (.nil (.refl _) (.refl _)))
          exact ih hv (stackWf_trace_inv hrest) hmem hacc' hdp
      | Assign x body fenv =>
          simp only [doPerformR] at hdp
          obtain ⟨Γ, defnTy, bodyTy, ε0, hσ', hε', henv, hbody, hrest'⟩ := stackWf_assign_inv hrest
          obtain ⟨a', b', hmem', hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
          have hacc' : StackSegWf ((Kontinue.Assign x body fenv, mt) :: acc).reverse b' εtop
              bodyTy ε0 := by
            rw [List.reverse_cons]
            exact stackSeg_append
              (stackSeg_conv_input (stackSeg_conv_output hacc hσ' hε') hrb.symm (.refl _))
              (.assign henv hbody (.nil (.refl _) (.refl _)))
          exact ih (hv.conv hla) hrest' hmem' hacc' hdp
      | Arg arg fenv =>
          simp only [doPerformR] at hdp
          obtain ⟨Γ, argTy, εfa, retTya, ε0, hσ', hε', henv, harg, hweff, hrest'⟩ :=
            stackWf_arg_inv hrest
          obtain ⟨a', b', hmem', hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
          have hacc' : StackSegWf ((Kontinue.Arg arg fenv, mt) :: acc).reverse b' εtop
              retTya ε0 := by
            rw [List.reverse_cons]
            exact stackSeg_append
              (stackSeg_conv_input (stackSeg_conv_output hacc hσ' hε') hrb.symm (.refl _))
              (.arg henv harg hweff (.nil (.refl _) (.refl _)))
          exact ih (hv.conv hla) hrest' hmem' hacc' hdp
      | Apply f fenv =>
          simp only [doPerformR] at hdp
          obtain ⟨argTy, εfa, retTya, ε0, hσ', hε', hf, hweff, hrest'⟩ := stackWf_applyf_inv hrest
          obtain ⟨a', b', hmem', hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
          have hacc' : StackSegWf ((Kontinue.Apply f fenv, mt) :: acc).reverse b' εtop
              retTya ε0 := by
            rw [List.reverse_cons]
            exact stackSeg_append
              (stackSeg_conv_input (stackSeg_conv_output hacc hσ' hε') hrb.symm (.refl _))
              (.applyf hf hweff (.nil (.refl _) (.refl _)))
          exact ih (hv.conv hla) hrest' hmem' hacc' hdp
      | CallWith arg fenv =>
          simp only [doPerformR] at hdp
          obtain ⟨argTy, εfa, retTya, ε0, hσ', hε', harg, hweff, hrest'⟩ := stackWf_callwith_inv hrest
          obtain ⟨a', b', hmem', hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
          have hacc' : StackSegWf ((Kontinue.CallWith arg fenv, mt) :: acc).reverse b' εtop
              retTya ε0 := by
            rw [List.reverse_cons]
            exact stackSeg_append
              (stackSeg_conv_input (stackSeg_conv_output hacc hσ' hε') hrb.symm (.refl _))
              (.callwith harg hweff (.nil (.refl _) (.refl _)))
          exact ih (hv.conv hla) hrest' hmem' hacc' hdp
      | Delimit l h e_ shallow =>
          obtain ⟨lift_d, reply_d, tail_d, ret_d, εInner, rfl, hσ', hε', hweff, hh, hrest'⟩ :=
            stackWf_delimit_inv hrest
          by_cases hll : (l == label) = true
          · -- matching Delimit: handled, build the resume
            obtain rfl := eq_of_beq hll
            simp only [doPerformR, hll, if_true] at hdp
            -- εcur ≈ ⟨l:(lift_d,reply_d)|tail_d⟩, and label = l carries (lift,reply): so they match
            obtain ⟨a', b', hmemH, hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
            cases hmemH with
            | head =>
                -- a' = lift_d, b' = reply_d
                cases hdp
                refine ⟨εInner, _, hh, ?_⟩
                -- stack: CallWith v :: CallWith resume :: rest', control = handler h
                refine StackWf.callwith (hv.conv hla) (Ty.effWeaken_empty _) ?_
                refine StackWf.callwith ?_ hweff hrest'
                -- resume : kontTy reply_d tail_d ret_d
                refine HasTypeV.partialResume (εtop := εtop) (fun εBelow hwB => ?_) (.refl _)
                simp only [Bool.false_eq_true, if_false]
                rw [List.reverse_cons]
                exact stackSeg_append
                  (stackSeg_conv_input (stackSeg_conv_output hacc hσ' (.refl _)) hrb.symm (.refl _))
                  (.delimit hh hε' hwB (.nil (.refl _) (.refl _)))
            | tail hne _ => exact absurd rfl hne
          · -- non-matching Delimit l' ≠ label: walk past, discharge l'
            simp only [doPerformR, hll, Bool.false_eq_true, if_false] at hdp
            obtain ⟨a', b', hmemT, hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
            -- label is in ⟨l:…|tail_d⟩ and l ≠ label, so it is in tail_d, hence in εInner
            have hlne : l ≠ label := fun h => by subst h; simp at hll
            have hmemTail : Ty.EffContains tail_d label a' b' := by
              cases hmemT with
              | head => exact absurd rfl hlne
              | tail _ hc => exact hc
            obtain ⟨a'', b'', hc, ha'', hb''⟩ :
                ∃ a'' b'', Ty.EffContains εInner label a'' b'' ∧ Ty.TyEquiv a' a'' ∧
                  Ty.TyEquiv b' b'' := by
              rcases hweff with he | he
              · exact Ty.tyEquiv_effContains_mp he hmemTail
              · exact absurd (Ty.tyEquiv_effContains_mp he hmemTail)
                  (fun ⟨_, _, hcc, _, _⟩ => effContains_empty hcc)
            have hacc' : StackSegWf ((Kontinue.Delimit l h e_ false, mt) :: acc).reverse b'' εtop
                ret_d εInner := by
              rw [List.reverse_cons]
              exact stackSeg_append
                (stackSeg_conv_input (stackSeg_conv_output hacc hσ' (.refl _))
                  (hrb.trans hb'').symm (.refl _))
                (.delimit hh hε' hweff (.nil (.refl _) (.refl _)))
            exact ih (hv.conv (hla.trans ha'')) hrest' hc hacc' hdp

/-- **`perform` dispatch DISCHARGED.** The handled-`perform` successor is well-typed —
the last handler dispatch, proved via `perform_walk`; called directly from `preservation_V`. -/
theorem perform_preserves [BEq m] {label : String} {v : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {argTy εf retTy ε τ : Ty} {cfg' : Config m}
    (hperf : HasTypeV (.Partial (.Perform label) [] : Value m) (.fun argTy εf retTy))
    (hv : HasTypeV v argTy) (hw : Ty.EffWeaken εf ε) (hrest : StackWf rest retTy ε τ)
    (hr : reduceCall (.Partial (.Perform label) []) v ann fenv rest = .tau cfg') :
    ∃ ε', MStateWf (.run cfg') τ ε' := by
  cases hperf with
  | @partialPerformNil _ argTy' replyTy' μ _ he =>
      obtain ⟨ha, heff, hr'⟩ := Ty.tyEquiv_fun_components he
      -- εf ≈ ⟨label:(argTy',replyTy')|μ⟩, so the exact disjunct of EffWeaken holds and label ∈ ε
      obtain ⟨a1, b1, hc1, e1a, e1b⟩ := Ty.tyEquiv_effContains_mp heff Ty.EffContains.head
      obtain ⟨a2, b2, hmemE, e2a, e2b⟩ :
          ∃ a2 b2, Ty.EffContains ε label a2 b2 ∧ Ty.TyEquiv argTy' a2 ∧ Ty.TyEquiv replyTy' b2 := by
        rcases hw with hwe | hwe
        · obtain ⟨a2, b2, hc2, e2a, e2b⟩ := Ty.tyEquiv_effContains_mp hwe hc1
          exact ⟨a2, b2, hc2, e1a.trans e2a, e1b.trans e2b⟩
        · exact absurd (Ty.tyEquiv_effContains_mp hwe hc1)
            (fun ⟨_, _, hcc, _, _⟩ => effContains_empty hcc)
      -- extract `doPerformR … = .ok cfg'` from the `.tau` step
      rw [show reduceCall (.Partial (.Perform label) []) v ann fenv rest
          = reducePerform label v fenv rest from rfl, reducePerform] at hr
      split at hr
      · next p hdp =>
          cases hr
          -- v : a2 (= argTy' ≈ argTy); segment input b2 (≈ replyTy' ≈ retTy)
          refine perform_walk rest (hv.conv (ha.symm.trans e2a)) hrest hmemE (acc := [])
            (.nil ?_ (.refl _)) hdp
          exact e2b.symm.trans hr'
      · next hdp => exact absurd hr (by simp)
      · next hdp => exact absurd hr (by simp)

/-- Preservation across a `.V`-control (`reduceApply` frame) step. The closure
application case is the crux; the builtin-application case defers to `hsat`; the three
effect-partial dispatches (`perform`/`install`/`resume`) are discharged directly. The
successor row is an *output* `∃ε'` —
it equals the ambient `ε` (up to `TyEquiv`) for the pure/data fragment, but **shrinks**
across a `Delimit` pop and **grows** across a `reduceDeep` handler-install. -/
theorem preservation_V [BEq m] (hsat : BuiltinAppPreserves m)
    {v : Value m} {env : Env m} {kont : Kontinue m} {ann : m} {rest : Stack m}
    {cfg' : Config m} {τ ε : Ty}
    (hwf : MStateWf (.run (.V v, env, (kont, ann) :: rest)) τ ε)
    (hr : reduce1Run (.V v, env, (kont, ann) :: rest) = .tau cfg') :
    ∃ ε', MStateWf (.run cfg') τ ε' := by
  obtain ⟨τin, hv, hst⟩ := mStateWf_V hwf
  cases kont with
  | Trace w =>
      have hrest := stackWf_trace_inv hst
      simp only [reduce1Run, reduceApply] at hr; cases hr
      exact ⟨ε, τin, hv, hrest⟩
  | Assign x body fenv =>
      obtain ⟨Γ, defnTy, bodyTy, ε0, hσ, hε, henvc, hbody, hrest⟩ := stackWf_assign_inv hst
      simp only [reduce1Run, reduceApply] at hr; cases hr
      refine ⟨ε0, _, _, EnvWf.cons (fun args => ?_) henvc, hbody, hrest⟩
      simpa using hv.conv hσ
  | Arg arg fenv =>
      obtain ⟨Γ, argTy, εf, retTy, ε0, hσ, hε, henvc, harg, hw, hrest⟩ := stackWf_arg_inv hst
      simp only [reduce1Run, reduceApply] at hr; cases hr
      exact ⟨ε0, _, _, henvc, harg, StackWf.applyf (hv.conv hσ) hw hrest⟩
  | Delimit l handler henv sh =>
      obtain ⟨lift, reply, tail, ret, εInner, rfl, hσ, hε, hweff, hh, hrest⟩ :=
        stackWf_delimit_inv hst
      simp only [reduce1Run, reduceApply] at hr; cases hr
      exact ⟨εInner, ret, hv.conv hσ, hrest⟩
  | Apply f fenv =>
      obtain ⟨argTy, εf, retTy, ε0, hσ, hε, hf, hw, hrest⟩ := stackWf_applyf_inv hst
      replace hv := hv.conv hσ
      rcases canonical_arrow hf with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
      · cases hf with
        | closure henvc hbody heqc =>
            obtain ⟨hA, hE, hR⟩ := Ty.tyEquiv_fun_components heqc
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            refine ⟨ε0, _, _, EnvWf.cons (fun args => ?_) henvc,
              weakenEff (HasType.conv hbody hR (.refl _)) (Ty.effWeaken_trans (.inl hE) hw),
              StackWf.trace hrest⟩
            simpa using hv.conv hA.symm
      · cases hf with
        | partialBuiltin hs hp he =>
            simp only [reduce1Run, reduceApply] at hr
            exact ⟨ε0, (hsat (.partialBuiltin hs hp he) hv hw hrest).1 _ hr⟩
        | partialFixed hbuilder he =>
            simp only [reduce1Run, reduceApply, reduceCall_fixed] at hr; cases hr
            exact ⟨ε0, fixed_reapply_preserves hbuilder he hv hw hrest⟩
        | partialConsNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.partialConsOne (hv.conv hA.symm) hR, hrest⟩
        | partialConsOne hh he =>
            obtain ⟨hD, _, hR⟩ := Ty.tyEquiv_fun_components he
            have hvl := hv.conv hD.symm
            obtain ⟨es, rfl⟩ := canonical_list hvl
            simp only [reduce1Run, reduceApply, reduceCall, Cast.asList] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.listCons hh hvl hR, hrest⟩
        | partialTag he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.tagged (hv.conv hA.symm) hR, hrest⟩
        | partialNoCases he =>
            obtain ⟨hA, _, _⟩ := Ty.tyEquiv_fun_components he
            exact absurd (hv.conv hA.symm) canonical_union_empty
        | partialMatchNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.partialMatchOne (hv.conv hA.symm) hR, hrest⟩
        | partialMatchOne hbranch he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.partialMatchTwo hbranch (hv.conv hA.symm) hR, hrest⟩
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
                      exact ⟨ε0, _, hvp.conv hf',
                        StackWf.applyf (hbranch.conv (.congrFun (.refl _) hEff hRet)) hw hrest⟩
                  | tail hne _ => exact absurd rfl hne
                · -- miss: the tag is in the tail, so the value inhabits `union tail`
                  rename_i hcond; cases hr
                  have hvlne : vl ≠ lbl := fun h => by subst h; simp at hcond
                  cases hcontains with
                  | head => exact absurd rfl hvlne
                  | tail _ hc'' =>
                      obtain ⟨rest', htail⟩ := Ty.rowContains_tyEquiv hc''
                      exact ⟨ε0, _, HasTypeV.tagged (hvp.conv hf') (Ty.TyEquiv.congrUnion htail),
                        StackWf.applyf (hotherwise.conv (.congrFun (.refl _) hEff hRet)) hw hrest⟩
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
                exact ⟨ε0, _, hvalue.conv (hf'.symm.trans hRet), hrest⟩
        | partialExtendNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.partialExtendOne (hv.conv hA.symm) hR, hrest⟩
        | @partialExtendOne lbl _ fieldTy row _ hvf he =>
            obtain ⟨hD, _, hRet⟩ := Ty.tyEquiv_fun_components he
            have hvr := hv.conv hD.symm
            obtain ⟨fields, rfl⟩ := canonical_record hvr
            cases hvr with
            | record hpres hmatch hetag =>
                simp only [reduce1Run, reduceApply, reduceCall, Cast.asRecord] at hr; cases hr
                refine ⟨ε0, _, HasTypeV.record ?_ ?_ hRet, hrest⟩
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
            exact ⟨ε0, _, HasTypeV.partialOverwriteOne (hv.conv hA.symm) hR, hrest⟩
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
                refine ⟨ε0, _, HasTypeV.record ?_ ?_ hRet, hrest⟩
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
        | partialHandleNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.partialHandleOne (hv.conv hA.symm) hR, hrest⟩
        | partialHandleOne hh he =>
            simp only [reduce1Run, reduceApply] at hr
            exact install_preserves (.partialHandleOne hh he) hv hw hrest hr
        | partialResume hseg he =>
            simp only [reduce1Run, reduceApply] at hr
            exact resume_preserves (.partialResume hseg he) hv hw hrest hr
        | partialPerformNil he =>
            simp only [reduce1Run, reduceApply] at hr
            exact perform_preserves (.partialPerformNil he) hv hw hrest hr
  | CallWith arg fenv =>
      obtain ⟨argTy, εf, retTy, ε0, hσ, hε, harg, hw, hrest⟩ := stackWf_callwith_inv hst
      replace hv := hv.conv hσ
      rcases canonical_arrow hv with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
      · cases hv with
        | closure henvc hbody heqc =>
            obtain ⟨hA, hE, hR⟩ := Ty.tyEquiv_fun_components heqc
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            refine ⟨ε0, _, _, EnvWf.cons (fun args => ?_) henvc,
              weakenEff (HasType.conv hbody hR (.refl _)) (Ty.effWeaken_trans (.inl hE) hw),
              StackWf.trace hrest⟩
            simpa using harg.conv hA.symm
      · cases hv with
        | partialBuiltin hs hp he =>
            simp only [reduce1Run, reduceApply] at hr
            exact ⟨ε0, (hsat (.partialBuiltin hs hp he) harg hw hrest).1 _ hr⟩
        | partialFixed hbuilder he =>
            simp only [reduce1Run, reduceApply, reduceCall_fixed] at hr; cases hr
            exact ⟨ε0, fixed_reapply_preserves hbuilder he harg hw hrest⟩
        | partialConsNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.partialConsOne (harg.conv hA.symm) hR, hrest⟩
        | partialConsOne hh he =>
            obtain ⟨hD, _, hR⟩ := Ty.tyEquiv_fun_components he
            have hvl := harg.conv hD.symm
            obtain ⟨es, rfl⟩ := canonical_list hvl
            simp only [reduce1Run, reduceApply, reduceCall, Cast.asList] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.listCons hh hvl hR, hrest⟩
        | partialTag he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.tagged (harg.conv hA.symm) hR, hrest⟩
        | partialNoCases he =>
            obtain ⟨hA, _, _⟩ := Ty.tyEquiv_fun_components he
            exact absurd (harg.conv hA.symm) canonical_union_empty
        | partialMatchNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.partialMatchOne (harg.conv hA.symm) hR, hrest⟩
        | partialMatchOne hbranch he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.partialMatchTwo hbranch (harg.conv hA.symm) hR, hrest⟩
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
                      exact ⟨ε0, _, hvp.conv hf',
                        StackWf.applyf (hbranch.conv (.congrFun (.refl _) hEff hRet)) hw hrest⟩
                  | tail hne _ => exact absurd rfl hne
                · rename_i hcond; cases hr
                  have hvlne : vl ≠ lbl := fun h => by subst h; simp at hcond
                  cases hcontains with
                  | head => exact absurd rfl hvlne
                  | tail _ hc'' =>
                      obtain ⟨rest', htail⟩ := Ty.rowContains_tyEquiv hc''
                      exact ⟨ε0, _, HasTypeV.tagged (hvp.conv hf') (Ty.TyEquiv.congrUnion htail),
                        StackWf.applyf (hotherwise.conv (.congrFun (.refl _) hEff hRet)) hw hrest⟩
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
                exact ⟨ε0, _, hvalue.conv (hf'.symm.trans hRet), hrest⟩
        | partialExtendNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.partialExtendOne (harg.conv hA.symm) hR, hrest⟩
        | @partialExtendOne lbl _ fieldTy row _ hvf he =>
            obtain ⟨hD, _, hRet⟩ := Ty.tyEquiv_fun_components he
            have hvr := harg.conv hD.symm
            obtain ⟨fields, rfl⟩ := canonical_record hvr
            cases hvr with
            | record hpres hmatch hetag =>
                simp only [reduce1Run, reduceApply, reduceCall, Cast.asRecord] at hr; cases hr
                refine ⟨ε0, _, HasTypeV.record ?_ ?_ hRet, hrest⟩
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
            exact ⟨ε0, _, HasTypeV.partialOverwriteOne (harg.conv hA.symm) hR, hrest⟩
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
                refine ⟨ε0, _, HasTypeV.record ?_ ?_ hRet, hrest⟩
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
        | partialHandleNil he =>
            obtain ⟨hA, _, hR⟩ := Ty.tyEquiv_fun_components he
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            exact ⟨ε0, _, HasTypeV.partialHandleOne (harg.conv hA.symm) hR, hrest⟩
        | partialHandleOne hh he =>
            simp only [reduce1Run, reduceApply] at hr
            exact install_preserves (.partialHandleOne hh he) harg hw hrest hr
        | partialResume hseg he =>
            simp only [reduce1Run, reduceApply] at hr
            exact resume_preserves (.partialResume hseg he) harg hw hrest hr
        | partialPerformNil he =>
            simp only [reduce1Run, reduceApply] at hr
            exact perform_preserves (.partialPerformNil he) harg hw hrest hr

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
    {rest : Stack m} {argTy εf retTy ε τ : Ty} {op : String} {lift : Value m}
    {envP : Env m} {kP : Stack m}
    (hf : HasTypeV f (.fun argTy εf retTy)) (hw : Ty.EffWeaken εf ε)
    (hrest : StackWf rest retTy ε τ)
    (h : reduceCall f arg ann fenv rest = .perform op lift envP kP) :
    MStateWf (.wait op envP kP) τ ε := by
  rcases canonical_arrow hf with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
  · exact absurd h (by simp [reduceCall])
  · cases hf with
    | partialBuiltin _ _ _ => exact absurd h reduceCall_builtin_ne_perform
    | partialFixed _ _ => rw [reduceCall_fixed] at h; exact absurd h (by simp)
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
    | partialHandleNil _ => simp only [reduceCall] at h; exact absurd h (by simp)
    | partialHandleOne _ _ => simp only [reduceCall, reduceDeep] at h; exact absurd h (by simp)
    | partialResume _ _ => simp only [reduceCall] at h; exact absurd h (by simp)
    | @partialPerformNil label argTy' replyTy' μ _ he =>
        obtain ⟨_, hE, hR⟩ := Ty.tyEquiv_fun_components he
        simp only [reduceCall] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := reducePerform_perform_inv h
        obtain ⟨a'', b'', hEff, _, hRb⟩ := perform_op_mem_ambient hE hw
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
          cases kont with
          | Trace _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Assign _ _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Arg _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Delimit _ _ _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Apply f fenv =>
              obtain ⟨argTy, εf, retTy, ε0, hσ, hε, hf, hw, hrest⟩ := stackWf_applyf_inv hst
              simp only [reduce1Run, reduceApply] at h
              exact mStateWf_wait_conv (reduceCall_perform_wait hf hw hrest h) hε
          | CallWith arg fenv =>
              obtain ⟨argTy, εf, retTy, ε0, hσ, hε, harg, hw, hrest⟩ := stackWf_callwith_inv hst
              simp only [reduce1Run, reduceApply] at h
              exact mStateWf_wait_conv (reduceCall_perform_wait (hv.conv hσ) hw hrest h) hε

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
      rename_i cfg cfg'
      obtain ⟨c, env, k⟩ := cfg
      cases c with
      | E e => exact ⟨ε, preservation_E hwf h⟩
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
theorem preservation_tau [BEq m] (hsat : BuiltinAppPreserves m)
    {cfg cfg' : Config m}
    {τ ε : Ty} (hwf : MStateWf (.run cfg) τ ε) (h : reduce1Run cfg = .tau cfg') :
    ∃ ε', MStateWf (.run cfg') τ ε' := by
  obtain ⟨c, env, k⟩ := cfg
  cases c with
  | E e => exact ⟨ε, preservation_E hwf h⟩
  | V v =>
      cases k with
      | nil => simp only [reduce1Run] at h; exact absurd h (by simp)
      | cons kontann rest =>
          obtain ⟨kont, ann⟩ := kontann; exact preservation_V hsat hwf h

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
          exact hw.conv (stackWf_nil_inv hst)
      | cons kontann rest =>
          obtain ⟨kont, ann⟩ := kontann
          obtain ⟨τin, hw, hst⟩ := mStateWf_V hwf
          cases kont with
          | Trace _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Assign _ _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Arg _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Delimit _ _ _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Apply f fenv =>
              obtain ⟨argTy0, εf0, retTy0, ε0, hσ, _, hf, hwk, hrest⟩ := stackWf_applyf_inv hst
              replace hw := hw.conv hσ
              rcases canonical_arrow hf with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
              · exact absurd h (by simp [reduce1Run, reduceApply, reduceCall])
              · cases hf with
                | partialBuiltin hs hp he =>
                    simp only [reduce1Run, reduceApply] at h
                    exact (hsat (.partialBuiltin hs hp he) hw hwk hrest).2 _ h
                | partialFixed _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall_fixed] at h
                    exact absurd h (by simp)
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
                    simp only [reduce1Run, reduceApply, reduceCall, reducePerform] at h
                    split at h <;> exact absurd h (by simp)
                | partialHandleNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialHandleOne _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall, reduceDeep] at h
                    exact absurd h (by simp)
                | partialResume _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
          | CallWith arg fenv =>
              obtain ⟨argTy0, εf0, retTy0, ε0, hσ, _, harg, hwk, hrest⟩ := stackWf_callwith_inv hst
              replace hw := hw.conv hσ
              rcases canonical_arrow hw with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
              · exact absurd h (by simp [reduce1Run, reduceApply, reduceCall])
              · cases hw with
                | partialBuiltin hs hp he =>
                    simp only [reduce1Run, reduceApply] at h
                    exact (hsat (.partialBuiltin hs hp he) harg hwk hrest).2 _ h
                | partialFixed _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall_fixed] at h
                    exact absurd h (by simp)
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
                    simp only [reduce1Run, reduceApply, reduceCall, reducePerform] at h
                    split at h <;> exact absurd h (by simp)
                | partialHandleNil _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)
                | partialHandleOne _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall, reduceDeep] at h
                    exact absurd h (by simp)
                | partialResume _ _ =>
                    simp only [reduce1Run, reduceApply, reduceCall] at h; exact absurd h (by simp)

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
      | Handle l => exact Or.inl ⟨_, rfl⟩
      | _ =>
          exfalso
          rcases hasType_expr_form hty with ⟨_, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, _, hh⟩ |
            ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ | hh | hh | hh | ⟨_, hh⟩ | hh | ⟨_, hh⟩ |
            ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ <;> simp at hh
  | V w =>
      cases k with
      | nil => exact Or.inr (Or.inl ⟨w, rfl⟩)
      | cons kontann rest =>
          obtain ⟨kont, ann⟩ := kontann
          obtain ⟨τin, hw, hst⟩ := mStateWf_V hwf
          cases kont with
          | Trace _ => exact Or.inl ⟨_, rfl⟩
          | Assign _ _ _ => exact Or.inl ⟨_, rfl⟩
          | Arg _ _ => exact Or.inl ⟨_, rfl⟩
          | Delimit _ _ _ _ => exact Or.inl ⟨_, rfl⟩
          | Apply f fenv =>
              obtain ⟨argTy0, εf0, retTy0, ε0, hσ, hε, hf, hwk, hrest⟩ := stackWf_applyf_inv hst
              replace hw := hw.conv hσ
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
                | partialFixed _ _ => exact Or.inl ⟨_, reduceCall_fixed _ _ _ _ _⟩
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
                    obtain ⟨_, hE, _⟩ := Ty.tyEquiv_fun_components he
                    cases hdp : doPerformR label w fenv rest [] with
                    | ok r =>
                        -- handled (matching `Delimit`): a `.tau` step
                        exact Or.inl ⟨r, by
                          simp only [reduce1Run, reduceApply, reduceCall, reducePerform, hdp]⟩
                    | error e =>
                        -- unhandled: escapes performing `label`, with `label ∈ ε`
                        obtain rfl := doPerformR_error_form _ _ hdp
                        obtain ⟨a'', b'', hEff0, _, _⟩ := perform_op_mem_ambient hE hwk
                        obtain ⟨a''', b''', hEff, _, _⟩ := (Ty.tyEquiv_effContains hε).2 _ _ _ hEff0
                        exact Or.inr (Or.inr (Or.inr ⟨label, w, fenv, rest, by
                          simp only [reduce1Run, reduceApply, reduceCall, reducePerform, hdp],
                          a''', b''', hEff⟩))
                | partialHandleNil _ => exact Or.inl ⟨_, rfl⟩
                | partialHandleOne _ _ => exact Or.inl ⟨_, rfl⟩
                | partialResume _ _ => exact Or.inl ⟨_, rfl⟩
          | CallWith arg fenv =>
              obtain ⟨argTy0, εf0, retTy0, ε0, hσ, hε, harg, hwk, hrest⟩ := stackWf_callwith_inv hst
              replace hw := hw.conv hσ
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
                | partialFixed _ _ => exact Or.inl ⟨_, reduceCall_fixed _ _ _ _ _⟩
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
                    cases hdp : doPerformR label arg fenv rest [] with
                    | ok r =>
                        exact Or.inl ⟨r, by
                          simp only [reduce1Run, reduceApply, reduceCall, reducePerform, hdp]⟩
                    | error e =>
                        obtain rfl := doPerformR_error_form _ _ hdp
                        obtain ⟨a'', b'', hEff0, _, _⟩ := perform_op_mem_ambient hE hwk
                        obtain ⟨a''', b''', hEff, _, _⟩ := (Ty.tyEquiv_effContains hε).2 _ _ _ hEff0
                        exact Or.inr (Or.inr (Or.inr ⟨label, arg, fenv, rest, by
                          simp only [reduce1Run, reduceApply, reduceCall, reducePerform, hdp],
                          a''', b''', hEff⟩))
                | partialHandleNil _ => exact Or.inl ⟨_, rfl⟩
                | partialHandleOne _ _ => exact Or.inl ⟨_, rfl⟩
                | partialResume _ _ => exact Or.inl ⟨_, rfl⟩

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
    (id = "fix" ∧ s = ⟨4, .fun (.fun (.fun (q 0) (q 2) (q 3)) (q 1) (.fun (q 0) (q 2) (q 3)))
        (q 1) (.fun (q 0) (q 2) (q 3))⟩) ∨
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
    {rest : Stack m} {argTy εf retTy ε τ : Ty},
    HasTypeV (.Partial (.Builtin "fix") applied) (.fun argTy εf retTy) →
    HasTypeV arg argTy →
    Ty.EffWeaken εf ε →
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
  intro id applied arg ann fenv rest argTy εf retTy ε τ hp harg hw hst
  cases hp with
  | @partialFixed builder _D _γ _R _τ hbuilder he =>
    -- the `fixed` re-application (`fix builder = builder (fix builder)`): provable here
    -- (the builder is pure, so `Apply builder` weakens via `effWeaken_empty`; the
    -- recursion arrow's latent is `hw` from the calling frame)
    refine ⟨fun cfg' hrr => ?_, fun v hvv => ?_⟩
    · rw [reduceCall_fixed] at hrr; cases hrr
      exact fixed_reapply_preserves hbuilder he harg hw hst
    · rw [reduceCall_fixed] at hvv; exact absurd hvv (by simp)
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
      exact hfix (HasTypeV.partialBuiltin hs hpw he) harg hw hst
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
  | @partialFixed builder _D _γ _R _τ _hbuilder _he =>
    -- the `fixed` re-application only ever `.tau`-steps, so it never crashes
    rw [reduceCall_fixed] at hcrash; exact absurd hcrash (by simp)
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
theorem soundness_value_fix [BEq m] (hfix : FixPreserves m)
    (fuel : Nat) {cfg : Config m}
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
theorem soundness_evalR_value [BEq m] (hfix : FixPreserves m)
    {prog : Tree.Node m}
    {τ ε : Ty} {v : Value m} (fuel : Nat) (hty : HasType [] prog τ ε)
    (h : evalR fuel (Config.initial prog) = .done (.value v)) : HasTypeV v τ :=
  soundness_value_fix hfix fuel (mStateWf_initial hty) h

/-- **No-bad-crash over `evalR`.** A well-typed config whose `evalR` terminates in a
crash only ever reaches the *sanctioned* `Unrepresentable` trap — never a type-error
crash (`Vacant`/`NotAFunction`/`NoMatch`/…). Fuel induction folding `preservation_fix`
(step) and `progress_fix` (the terminal crash is `¬ IsBad`). -/
theorem soundnessR_noBadCrash [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m)
    :
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

/-! ## T7 row-evolution groundwork: bottom-row tracking (`StackWfB`) + escape membership

`StackWf` augmented with the **base row** `εbot` (the row at the bottom of the stack, reached
by walking down through the row-discharging `Delimit` frames). The escape lemma below proves
that an *unhandled* operation in the top row is a member of the base row — the membership
transfer down the stack that the genuine effect-escape soundness needs (replacing the
`TauKeepsRow` gate, once the base-row preservation re-thread lands; see
`progress/2026-06-18-T7-rowevolves.md`). Self-contained (no preservation needed). -/
inductive StackWfB {m : Type} : Stack m → Ty → Ty → Ty → Ty → Prop where
  | nil {τ ε} : StackWfB [] τ ε ε τ
  | trace {a w rest τin ε εbot τout} :
      StackWfB rest τin ε εbot τout →
      StackWfB ((Kontinue.Trace w, a) :: rest) τin ε εbot τout
  | assign {a x body fenv Γ defnTy bodyTy ε εbot τout rest} :
      EnvWf fenv Γ → HasType ((x, .mono defnTy) :: Γ) body bodyTy ε →
      StackWfB rest bodyTy ε εbot τout →
      StackWfB ((Kontinue.Assign x body fenv, a) :: rest) defnTy ε εbot τout
  | arg {a arg fenv Γ argTy εf retTy ε εbot τout rest} :
      EnvWf fenv Γ → HasType Γ arg argTy ε → Ty.EffWeaken εf ε →
      StackWfB rest retTy ε εbot τout →
      StackWfB ((Kontinue.Arg arg fenv, a) :: rest) (.fun argTy εf retTy) ε εbot τout
  | applyf {a f fenv argTy εf retTy ε εbot τout rest} :
      HasTypeV f (.fun argTy εf retTy) → Ty.EffWeaken εf ε →
      StackWfB rest retTy ε εbot τout →
      StackWfB ((Kontinue.Apply f fenv, a) :: rest) argTy ε εbot τout
  | callwith {a arg fenv argTy εf retTy ε εbot τout rest} :
      HasTypeV arg argTy → Ty.EffWeaken εf ε →
      StackWfB rest retTy ε εbot τout →
      StackWfB ((Kontinue.CallWith arg fenv, a) :: rest) (.fun argTy εf retTy) ε εbot τout
  | delimit {a l handler henv lift reply tail ret εInner εbot τout rest} :
      HasTypeV handler (handlerTy lift reply tail ret) → Ty.EffWeaken tail εInner →
      StackWfB rest ret εInner εbot τout →
      StackWfB ((Kontinue.Delimit l handler henv false, a) :: rest)
        ret (.effectExtend l lift reply tail) εbot τout
  /-- **Conversion closure** (mirrors `StackWf.conv`): the input type and the *top*
  ambient row may be replaced by `TyEquiv`-equal ones; the base row `εbot` is untouched.
  The preservation re-thread needs `StackWfB` closed under conversion exactly as `StackWf`
  is (the `Resume`/`Handle` frame typing produces `conv`-wrapped stacks). -/
  | conv {k σ σ' εtop εtop' εbot τout} :
      StackWfB k σ εtop εbot τout → Ty.TyEquiv σ σ' → Ty.TyEquiv εtop εtop' →
      StackWfB k σ' εtop' εbot τout

/-- The stack has no `Delimit` frame handling `op` (so a `perform op` walks past every
`Delimit` and escapes to the base). -/
def noHandlerFor {m : Type} (op : String) : Stack m → Prop
  | [] => True
  | (k, _) :: rest =>
      (match k with | Kontinue.Delimit l _ _ _ => l ≠ op | _ => True) ∧ noHandlerFor op rest

/-- **Escape membership transfer.** An operation present in the *top* row that no `Delimit`
in the stack handles is present (up to `TyEquiv` of its payload types) in the *base* row.
Each `Delimit l` (with `l ≠ op`) transfers membership from `⟨l|tail⟩` down to `tail`
(`effContains_extend_inv`) and then across `EffWeaken tail εInner` to the row below; the
`tail ≈ ∅` weakening branch is impossible (`op ∈ ∅`). -/
theorem stackWfB_escape {m : Type} {k : Stack m} {σ εtop εbot τ : Ty} {op : String} :
    StackWfB k σ εtop εbot τ → ∀ {a b : Ty}, noHandlerFor op k →
    Ty.EffContains εtop op a b → ∃ a' b', Ty.EffContains εbot op a' b' := by
  intro h
  induction h with
  | nil => intro a b _ hc; exact ⟨a, b, hc⟩
  | trace _ ih => intro a b hnh hc; exact ih (by simp only [noHandlerFor] at hnh; exact hnh.2) hc
  | assign _ _ _ ih => intro a b hnh hc; exact ih (by simp only [noHandlerFor] at hnh; exact hnh.2) hc
  | arg _ _ _ _ ih => intro a b hnh hc; exact ih (by simp only [noHandlerFor] at hnh; exact hnh.2) hc
  | applyf _ _ _ ih => intro a b hnh hc; exact ih (by simp only [noHandlerFor] at hnh; exact hnh.2) hc
  | callwith _ _ _ ih => intro a b hnh hc; exact ih (by simp only [noHandlerFor] at hnh; exact hnh.2) hc
  | @delimit _ l _ _ lift reply tail ret εInner εbot τout rest _ hwk _ ih =>
      intro a b hnh hc
      simp only [noHandlerFor] at hnh
      obtain ⟨hne, hnh'⟩ := hnh
      cases hc with
      | head => exact (hne rfl).elim
      | tail _ hct =>
          rcases hwk with htyeq | htyeq
          · obtain ⟨a', b', hcI, _, _⟩ := Ty.tyEquiv_effContains_mp htyeq hct
            exact ih hnh' hcI
          · obtain ⟨a', b', hcE, _, _⟩ := Ty.tyEquiv_effContains_mp htyeq hct
            exact (effContains_empty hcE).elim
  | @conv _ _ _ εtop εtop' _ _ _ _ hε ih =>
      intro a b hnh hc
      obtain ⟨a', b', hc', _, _⟩ := Ty.tyEquiv_effContains_mp hε.symm hc
      exact ih hnh hc'

/-- **Forget the base row.** A `StackWfB` is in particular a `StackWf` at its *top* row
(drop `εbot`; each constructor maps to the matching `StackWf` one). -/
theorem stackWfB_toStackWf {m : Type} {k : Stack m} {σ εtop εbot τ : Ty}
    (h : StackWfB k σ εtop εbot τ) : StackWf k σ εtop τ := by
  induction h with
  | nil => exact .nil
  | trace _ ih => exact .trace ih
  | assign henv hbody _ ih => exact .assign henv hbody ih
  | arg henv harg hw _ ih => exact .arg henv harg hw ih
  | applyf hf hw _ ih => exact .applyf hf hw ih
  | callwith harg hw _ ih => exact .callwith harg hw ih
  | delimit hh hw _ ih => exact .delimit hh hw ih
  | conv _ hσ hε ih => exact .conv ih hσ hε

/-! ### `StackWfB` per-frame inversion lemmas

The base-row analogues of the `stackWf_*_inv` lemmas (`Machine.lean`), folding the new
`conv` constructor via `TyEquiv.trans`. The base row `εbot` is an extra passive output,
unchanged by every non-`delimit` frame and recursed-into by `delimit`. -/

theorem stackWfB_trace_inv {m : Type} {w : Value m} {a : m} {rest : Stack m}
    {σ εtop εbot τ : Ty}
    (h : StackWfB ((Kontinue.Trace w, a) :: rest) σ εtop εbot τ) :
    StackWfB rest σ εtop εbot τ := by
  generalize hs : ((Kontinue.Trace w, a) :: rest) = s at h
  induction h with
  | trace h' => cases hs; exact h'
  | conv h' hσ hε ih => exact .conv (ih hs) hσ hε
  | _ => simp at hs

theorem stackWfB_assign_inv {m : Type} {x : String} {body : Tree.Node m} {fenv : Env m}
    {a : m} {rest : Stack m} {σ εtop εbot τ : Ty}
    (h : StackWfB ((Kontinue.Assign x body fenv, a) :: rest) σ εtop εbot τ) :
    ∃ Γ defnTy bodyTy εtop0, Ty.TyEquiv σ defnTy ∧ Ty.TyEquiv εtop εtop0 ∧ EnvWf fenv Γ ∧
      HasType ((x, .mono defnTy) :: Γ) body bodyTy εtop0 ∧
      StackWfB rest bodyTy εtop0 εbot τ := by
  generalize hs : ((Kontinue.Assign x body fenv, a) :: rest) = s at h
  induction h with
  | assign henv hbody hrest =>
      cases hs; exact ⟨_, _, _, _, .refl _, .refl _, henv, hbody, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨Γ, dT, bT, ε0, hσ', hε', henv, hbody, hrest⟩ := ih hs
      exact ⟨Γ, dT, bT, ε0, hσ.symm.trans hσ', hε.symm.trans hε', henv, hbody, hrest⟩
  | _ => simp at hs

theorem stackWfB_arg_inv {m : Type} {arg : Tree.Node m} {fenv : Env m} {a : m}
    {rest : Stack m} {σ εtop εbot τ : Ty}
    (h : StackWfB ((Kontinue.Arg arg fenv, a) :: rest) σ εtop εbot τ) :
    ∃ Γ argTy εf retTy εtop0, Ty.TyEquiv σ (.fun argTy εf retTy) ∧ Ty.TyEquiv εtop εtop0 ∧
      EnvWf fenv Γ ∧ HasType Γ arg argTy εtop0 ∧ Ty.EffWeaken εf εtop0 ∧
      StackWfB rest retTy εtop0 εbot τ := by
  generalize hs : ((Kontinue.Arg arg fenv, a) :: rest) = s at h
  induction h with
  | arg henv harg hw hrest =>
      cases hs; exact ⟨_, _, _, _, _, .refl _, .refl _, henv, harg, hw, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨Γ, aT, εf, rT, ε0, hσ', hε', henv, harg, hw, hrest⟩ := ih hs
      exact ⟨Γ, aT, εf, rT, ε0, hσ.symm.trans hσ', hε.symm.trans hε', henv, harg, hw, hrest⟩
  | _ => simp at hs

theorem stackWfB_applyf_inv {m : Type} {f : Value m} {fenv : Env m} {a : m}
    {rest : Stack m} {σ εtop εbot τ : Ty}
    (h : StackWfB ((Kontinue.Apply f fenv, a) :: rest) σ εtop εbot τ) :
    ∃ argTy εf retTy εtop0, Ty.TyEquiv σ argTy ∧ Ty.TyEquiv εtop εtop0 ∧
      HasTypeV f (.fun argTy εf retTy) ∧ Ty.EffWeaken εf εtop0 ∧
      StackWfB rest retTy εtop0 εbot τ := by
  generalize hs : ((Kontinue.Apply f fenv, a) :: rest) = s at h
  induction h with
  | applyf hf hw hrest => cases hs; exact ⟨_, _, _, _, .refl _, .refl _, hf, hw, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨aT, εf, rT, ε0, hσ', hε', hf, hw, hrest⟩ := ih hs
      exact ⟨aT, εf, rT, ε0, hσ.symm.trans hσ', hε.symm.trans hε', hf, hw, hrest⟩
  | _ => simp at hs

theorem stackWfB_callwith_inv {m : Type} {arg : Value m} {fenv : Env m} {a : m}
    {rest : Stack m} {σ εtop εbot τ : Ty}
    (h : StackWfB ((Kontinue.CallWith arg fenv, a) :: rest) σ εtop εbot τ) :
    ∃ argTy εf retTy εtop0, Ty.TyEquiv σ (.fun argTy εf retTy) ∧ Ty.TyEquiv εtop εtop0 ∧
      HasTypeV arg argTy ∧ Ty.EffWeaken εf εtop0 ∧ StackWfB rest retTy εtop0 εbot τ := by
  generalize hs : ((Kontinue.CallWith arg fenv, a) :: rest) = s at h
  induction h with
  | callwith harg hw hrest => cases hs; exact ⟨_, _, _, _, .refl _, .refl _, harg, hw, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨aT, εf, rT, ε0, hσ', hε', harg, hw, hrest⟩ := ih hs
      exact ⟨aT, εf, rT, ε0, hσ.symm.trans hσ', hε.symm.trans hε', harg, hw, hrest⟩
  | _ => simp at hs

theorem stackWfB_delimit_inv {m : Type} {l : String} {handler : Value m} {henv : Env m}
    {shallow : Bool} {a : m} {rest : Stack m} {σ εtop εbot τ : Ty}
    (h : StackWfB ((Kontinue.Delimit l handler henv shallow, a) :: rest) σ εtop εbot τ) :
    ∃ lift reply tail ret εInner, shallow = false ∧ Ty.TyEquiv σ ret ∧
      Ty.TyEquiv εtop (.effectExtend l lift reply tail) ∧ Ty.EffWeaken tail εInner ∧
      HasTypeV handler (handlerTy lift reply tail ret) ∧
      StackWfB rest ret εInner εbot τ := by
  generalize hs : ((Kontinue.Delimit l handler henv shallow, a) :: rest) = s at h
  induction h with
  | delimit hh hw hrest =>
      cases hs; exact ⟨_, _, _, _, _, rfl, .refl _, .refl _, hw, hh, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨li, r, t, re, ei, hsh, hσ', hε', hweff, hh, hrest⟩ := ih hs
      exact ⟨li, r, t, re, ei, hsh, hσ.symm.trans hσ', hε.symm.trans hε', hweff, hh, hrest⟩
  | _ => simp at hs

theorem stackWfB_nil_inv {m : Type} {σ εtop εbot τ : Ty}
    (h : StackWfB ([] : Stack m) σ εtop εbot τ) : Ty.TyEquiv σ τ := by
  generalize hs : ([] : Stack m) = s at h
  induction h with
  | nil => exact .refl _
  | conv _ hσ hε ih => exact hσ.symm.trans (ih hs)
  | _ => simp at hs

/-- **Segment → `StackWfB` composition** (the base-row analogue of `stackSeg_toStackWf`).
The captured segment `seg` carries no base row — `εbot` lives only on the base stack `k`,
threaded unchanged through each frame (the segment's own `delimit` recurses to the base). -/
theorem stackSeg_toStackWfB {m : Type} {seg k : Stack m} {σin εin σmid εmid εbot τ : Ty}
    (hseg : StackSegWf seg σin εin σmid εmid) (hk : StackWfB k σmid εmid εbot τ) :
    StackWfB (seg ++ k) σin εin εbot τ := by
  induction seg generalizing σin εin with
  | nil => cases hseg with | nil h1 h2 => exact StackWfB.conv hk h1.symm h2.symm
  | cons hd rest ih =>
      obtain ⟨kont, ann⟩ := hd
      cases hseg with
      | trace h => exact .trace (ih h)
      | assign henv hbody h => exact .assign henv hbody (ih h)
      | arg henv harg hw h => exact .arg henv harg hw (ih h)
      | applyf hf hw h => exact .applyf hf hw (ih h)
      | callwith harg hw h => exact .callwith harg hw (ih h)
      | delimit hh he hweak h => exact StackWfB.conv (.delimit hh hweak (ih h)) (.refl _) he.symm

/-- Feeding a reply into the reified `move acc k` continuation preserves the base row. -/
theorem stackWfB_resume {m : Type} {acc k : Stack m} {σin εin σmid εmid εbot τ : Ty}
    (hseg : StackSegWf acc.reverse σin εin σmid εmid) (hk : StackWfB k σmid εmid εbot τ) :
    StackWfB (move acc k) σin εin εbot τ := by
  rw [move_eq]; exact stackSeg_toStackWfB hseg hk

/-- **`MStateWfB`** — the base-row-tracking analogue of `MStateWf`: the stack is typed by
`StackWfB` carrying the bottom-of-stack row `εbot` (invariantly `ε_init` across a run), while
the control runs at the current *top* row `εtop`. The discharge of `TauKeepsRow` uses it: an
escaping `op ∈ εtop` with no handler reflects to `op ∈ εbot` via `stackWfB_escape`. -/
def MStateWfB {m : Type} : MState m → Ty → Ty → Prop
  | .run (.E e, env, k), τ, εbot =>
      ∃ Γ τin εtop, EnvWf env Γ ∧ HasType Γ e τin εtop ∧ StackWfB k τin εtop εbot τ
  | .run (.V v, _, k), τ, εbot =>
      ∃ τin εtop, HasTypeV v τin ∧ StackWfB k τin εtop εbot τ
  | .wait op _ k, τ, εbot =>
      ∃ a b replyTy εtop, Ty.EffContains εtop op a b ∧ Ty.TyEquiv b replyTy ∧
        StackWfB k replyTy εtop εbot τ

/-- A well-typed program's initial state is `MStateWfB` at base row = its declared row
(empty stack ⇒ `εtop = εbot = εinit`). -/
theorem mStateWfB_initial {m : Type} {prog : Tree.Node m} {τ εinit : Ty}
    (h : HasType [] prog τ εinit) : MStateWfB (.run (Config.initial prog)) τ εinit :=
  ⟨[], τ, εinit, EnvWf.nil, h, StackWfB.nil⟩

/-- Unfold `MStateWfB` on a running `.E` state. -/
theorem mStateWfB_E {m : Type} {e : Tree.Node m} {env k τ εbot}
    (h : MStateWfB (.run (.E e, env, k)) τ εbot) :
    ∃ Γ τin εtop, EnvWf env Γ ∧ HasType Γ e τin εtop ∧ StackWfB k τin εtop εbot τ := h

/-- Unfold `MStateWfB` on a running `.V` state. -/
theorem mStateWfB_V {m : Type} {v : Value m} {env k τ εbot}
    (h : MStateWfB (.run (.V v, env, k)) τ εbot) :
    ∃ τin εtop, HasTypeV v τin ∧ StackWfB k τin εtop εbot τ := h

/-- **Base-row preservation across an `.E` (eval) `tau` step** — the `StackWfB` analogue of
`preservation_E`, threading the base row `εbot` (the top row `εtop` is existential and
unchanged across eval steps; only the base row is the exposed invariant). A direct mirror:
every case keeps the stack `hst` (now `StackWfB`), pushing the `arg`/`assign` frames via the
`StackWfB` constructors. -/
theorem preservation_E_B [BEq m] {e : Tree.Node m} {env : Env m} {k : Stack m}
    {cfg' : Config m} {τ εbot : Ty}
    (hwf : MStateWfB (.run (.E e, env, k)) τ εbot)
    (hr : reduce1Run (.E e, env, k) = .tau cfg') :
    MStateWfB (.run cfg') τ εbot := by
  obtain ⟨Γ, τin, εtop, henv, hty, hst⟩ := mStateWfB_E hwf
  obtain ⟨expr, ann⟩ := e
  cases expr with
  | Integer n =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      exact ⟨τin, εtop, HasTypeV.int (inv_int hty), hst⟩
  | String s =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      exact ⟨τin, εtop, HasTypeV.str (inv_str hty), hst⟩
  | Binary b =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      exact ⟨τin, εtop, HasTypeV.bin (inv_bin hty), hst⟩
  | Lambda x body =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨argTy, εb, retTy, hbody, heq⟩ := inv_lambda hty
      exact ⟨τin, εtop, HasTypeV.closure henv hbody heq, hst⟩
  | Variable x =>
      obtain ⟨s, args, hlookup, heq⟩ := inv_var hty
      obtain ⟨v, hvlk, hvty⟩ := envwf_lookup henv hlookup
      simp only [reduce1Run, reduceEval, hvlk] at hr; cases hr
      exact ⟨τin, εtop, (hvty args).conv heq, hst⟩
  | Apply f arg =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨argTy, εf, hw, hf, harg⟩ := inv_app hty
      exact ⟨Γ, _, εtop, henv, hf, StackWfB.arg henv harg hw hst⟩
  | Let x defn body =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨defnTy, hdefn, hbody⟩ := inv_let hty
      exact ⟨Γ, defnTy, εtop, henv, hdefn, StackWfB.assign henv hbody hst⟩
  | Builtin id =>
      obtain ⟨s, args, hs, heq⟩ := inv_builtin hty
      obtain ⟨a, e, r, harrow⟩ := builtin_instantiate_arrow args hs
      rw [harrow] at heq
      simp only [reduce1Run, reduceEval] at hr
      split at hr
      · cases hr
        refine ⟨τin, εtop, HasTypeV.partialBuiltin (args := args) hs ?_ heq, hst⟩
        rw [harrow]; exact BuiltinPartialWf.nil
      · exact absurd hr (by simp)
  | Tail =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨elem, heq⟩ := inv_tail hty
      exact ⟨τin, εtop, HasTypeV.listNil heq, hst⟩
  | Empty =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      exact ⟨τin, εtop, HasTypeV.record (fun _ _ hc => by cases hc)
        (fun _ _ _ hc _ => by cases hc) (inv_empty hty), hst⟩
  | Cons =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨elem, heq⟩ := inv_cons hty
      exact ⟨τin, εtop, HasTypeV.partialConsNil heq, hst⟩
  | Tag l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨elem, tail, heq⟩ := inv_tag hty
      exact ⟨τin, εtop, HasTypeV.partialTag heq, hst⟩
  | NoCases =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨ret, heq⟩ := inv_nocases hty
      exact ⟨τin, εtop, HasTypeV.partialNoCases heq, hst⟩
  | Case l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨inner, eff, ret, tail, heq⟩ := inv_case hty
      exact ⟨τin, εtop, HasTypeV.partialMatchNil heq, hst⟩
  | Select l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨fieldTy, tail, heq⟩ := inv_select hty
      exact ⟨τin, εtop, HasTypeV.partialSelect heq, hst⟩
  | Extend l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨fieldTy, row, heq⟩ := inv_extend hty
      exact ⟨τin, εtop, HasTypeV.partialExtendNil heq, hst⟩
  | Overwrite l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨newTy, oldTy, tail, heq⟩ := inv_overwrite hty
      exact ⟨τin, εtop, HasTypeV.partialOverwriteNil heq, hst⟩
  | Perform l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨argTy, replyTy, μ, heq⟩ := inv_perform hty
      exact ⟨τin, εtop, HasTypeV.partialPerformNil heq, hst⟩
  | Handle l =>
      simp only [reduce1Run, reduceEval] at hr; cases hr
      obtain ⟨lift, reply, tail, ret, heq⟩ := inv_handle hty
      exact ⟨τin, εtop, HasTypeV.partialHandleNil heq, hst⟩
  | _ =>
      exfalso
      rcases hasType_expr_form hty with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ |
        ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h | h | h | ⟨_, h⟩ | h | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h

/-! ### Base-row dispatch lemmas (the `StackWfB` mirrors of the handler dispatches)

`fixed`/`resume`/`install`/`perform` all build the successor stack from the input base
stack `rest` (push frames, or `move acc rest`); since `StackSegWf` carries no base row, the
captured segment is reused verbatim and only the base `StackWfB rest … εbot` threads `εbot`
through. Each mirrors its non-`B` counterpart, with `stackWfB_*_inv` / `stackWfB_resume`
replacing the `StackWf` versions and the result an `MStateWfB … εbot`. -/

/-- Base-row mirror of `fixed_reapply_preserves`. -/
theorem fixed_reapply_preserves_B [BEq m] {builder arg : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {D γ R argTy εf retTy ε εbot τ : Ty}
    (hbuilder : HasTypeV builder (.fun (.fun D γ R) .empty (.fun D γ R)))
    (he : Ty.TyEquiv (.fun D γ R) (.fun argTy εf retTy))
    (harg : HasTypeV arg argTy) (hw : Ty.EffWeaken εf ε) (hrest : StackWfB rest retTy ε εbot τ) :
    MStateWfB (.run (.V (.Partial (.Builtin "fixed") [builder]), fenv,
      (Kontinue.Apply builder fenv, ann) :: (Kontinue.CallWith arg fenv, ann) :: rest)) τ εbot := by
  have hb' : HasTypeV builder (.fun (.fun argTy εf retTy) .empty (.fun argTy εf retTy)) :=
    hbuilder.conv (.congrFun he (.refl _) he)
  exact ⟨_, _, HasTypeV.partialFixed hb' (.refl _),
    StackWfB.applyf hb' (Ty.effWeaken_empty _) (StackWfB.callwith harg hw hrest)⟩

/-- Base-row mirror of `resume_preserves`. -/
theorem resume_preserves_B [BEq m] {acc : Stack m} {iEnv : Env m} {v : Value m}
    {ann : m} {fenv : Env m} {rest : Stack m} {argTy εf retTy ε εbot τ : Ty} {cfg' : Config m}
    (hres : HasTypeV (.Partial (.Resume acc iEnv) [] : Value m) (.fun argTy εf retTy))
    (hv : HasTypeV v argTy) (hw : Ty.EffWeaken εf ε) (hrest : StackWfB rest retTy ε εbot τ)
    (hr : reduceCall (.Partial (.Resume acc iEnv) []) v ann fenv rest = .tau cfg') :
    MStateWfB (.run cfg') τ εbot := by
  cases hres with
  | partialResume hseg he =>
      obtain ⟨ha, heff, hr'⟩ := Ty.tyEquiv_fun_components he
      rw [show reduceCall (.Partial (.Resume acc iEnv) []) v ann fenv rest
          = .tau (.V v, iEnv, move acc rest) from rfl] at hr
      cases hr
      have htailW : Ty.EffWeaken _ ε := hw.imp (fun h => heff.trans h) (fun h => heff.trans h)
      exact ⟨_, _, hv.conv ha.symm,
        stackWfB_resume (hseg ε htailW) (StackWfB.conv hrest hr'.symm (.refl _))⟩

/-- Base-row mirror of `install_preserves`. -/
theorem install_preserves_B [BEq m] {l : String} {handler v : Value m}
    {ann : m} {fenv : Env m} {rest : Stack m} {argTy εf retTy ε εbot τ : Ty} {cfg' : Config m}
    (hh : HasTypeV (.Partial (.Handle l) [handler] : Value m) (.fun argTy εf retTy))
    (hv : HasTypeV v argTy) (hw : Ty.EffWeaken εf ε) (hrest : StackWfB rest retTy ε εbot τ)
    (hr : reduceCall (.Partial (.Handle l) [handler]) v ann fenv rest = .tau cfg') :
    MStateWfB (.run cfg') τ εbot := by
  cases hh with
  | partialHandleOne hhandler he =>
      obtain ⟨ha, heff, hr'⟩ := Ty.tyEquiv_fun_components he
      rw [show reduceCall (.Partial (.Handle l) [handler]) v ann fenv rest
          = .tau (.V unit, fenv,
              (Kontinue.Apply v fenv, ann) :: (Kontinue.Delimit l handler fenv false, ann) :: rest)
          from rfl] at hr
      cases hr
      exact ⟨_, _, hasTypeV_unit,
        StackWfB.applyf (hv.conv ha.symm) (Ty.effWeaken_refl _)
          (StackWfB.delimit hhandler (hw.imp (fun h => heff.trans h) (fun h => heff.trans h))
            (StackWfB.conv hrest hr'.symm (.refl _)))⟩

/-- Base-row mirror of `perform_walk` (design §5). Threads the base row `εbot` through the
stack walk; the captured segment `acc` is unchanged (no base row), and at the matching
`Delimit` the resume is composed onto the base below it (`StackWfB rest' ret_d εInner εbot`),
keeping `εbot`. -/
theorem perform_walk_B [BEq m] {label : String} {v : Value m} {iEnv : Env m} {εbot : Ty}
    (rest : Stack m) :
    ∀ {acc : Stack m} {σcur εcur εtop τ lift reply : Ty} {cfg' : Config m},
      HasTypeV v lift →
      StackWfB rest σcur εcur εbot τ →
      Ty.EffContains εcur label lift reply →
      StackSegWf acc.reverse reply εtop σcur εcur →
      doPerformR label v iEnv rest acc = .ok cfg' →
      MStateWfB (.run cfg') τ εbot := by
  induction rest with
  | nil => intro acc σcur εcur εtop τ lift reply cfg' _ _ _ _ hdp; simp [doPerformR] at hdp
  | cons hd rest' ih =>
      intro acc σcur εcur εtop τ lift reply cfg' hv hrest hmem hacc hdp
      obtain ⟨kont, mt⟩ := hd
      cases kont with
      | Trace w =>
          simp only [doPerformR] at hdp
          have hacc' : StackSegWf ((Kontinue.Trace w, mt) :: acc).reverse reply εtop σcur εcur := by
            rw [List.reverse_cons]; exact stackSeg_append hacc (.trace (.nil (.refl _) (.refl _)))
          exact ih hv (stackWfB_trace_inv hrest) hmem hacc' hdp
      | Assign x body fenv =>
          simp only [doPerformR] at hdp
          obtain ⟨Γ, defnTy, bodyTy, ε0, hσ', hε', henv, hbody, hrest'⟩ := stackWfB_assign_inv hrest
          obtain ⟨a', b', hmem', hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
          have hacc' : StackSegWf ((Kontinue.Assign x body fenv, mt) :: acc).reverse b' εtop
              bodyTy ε0 := by
            rw [List.reverse_cons]
            exact stackSeg_append
              (stackSeg_conv_input (stackSeg_conv_output hacc hσ' hε') hrb.symm (.refl _))
              (.assign henv hbody (.nil (.refl _) (.refl _)))
          exact ih (hv.conv hla) hrest' hmem' hacc' hdp
      | Arg arg fenv =>
          simp only [doPerformR] at hdp
          obtain ⟨Γ, argTy, εfa, retTya, ε0, hσ', hε', henv, harg, hweff, hrest'⟩ :=
            stackWfB_arg_inv hrest
          obtain ⟨a', b', hmem', hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
          have hacc' : StackSegWf ((Kontinue.Arg arg fenv, mt) :: acc).reverse b' εtop
              retTya ε0 := by
            rw [List.reverse_cons]
            exact stackSeg_append
              (stackSeg_conv_input (stackSeg_conv_output hacc hσ' hε') hrb.symm (.refl _))
              (.arg henv harg hweff (.nil (.refl _) (.refl _)))
          exact ih (hv.conv hla) hrest' hmem' hacc' hdp
      | Apply f fenv =>
          simp only [doPerformR] at hdp
          obtain ⟨argTy, εfa, retTya, ε0, hσ', hε', hf, hweff, hrest'⟩ := stackWfB_applyf_inv hrest
          obtain ⟨a', b', hmem', hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
          have hacc' : StackSegWf ((Kontinue.Apply f fenv, mt) :: acc).reverse b' εtop
              retTya ε0 := by
            rw [List.reverse_cons]
            exact stackSeg_append
              (stackSeg_conv_input (stackSeg_conv_output hacc hσ' hε') hrb.symm (.refl _))
              (.applyf hf hweff (.nil (.refl _) (.refl _)))
          exact ih (hv.conv hla) hrest' hmem' hacc' hdp
      | CallWith arg fenv =>
          simp only [doPerformR] at hdp
          obtain ⟨argTy, εfa, retTya, ε0, hσ', hε', harg, hweff, hrest'⟩ := stackWfB_callwith_inv hrest
          obtain ⟨a', b', hmem', hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
          have hacc' : StackSegWf ((Kontinue.CallWith arg fenv, mt) :: acc).reverse b' εtop
              retTya ε0 := by
            rw [List.reverse_cons]
            exact stackSeg_append
              (stackSeg_conv_input (stackSeg_conv_output hacc hσ' hε') hrb.symm (.refl _))
              (.callwith harg hweff (.nil (.refl _) (.refl _)))
          exact ih (hv.conv hla) hrest' hmem' hacc' hdp
      | Delimit l h e_ shallow =>
          obtain ⟨lift_d, reply_d, tail_d, ret_d, εInner, rfl, hσ', hε', hweff, hh, hrest'⟩ :=
            stackWfB_delimit_inv hrest
          by_cases hll : (l == label) = true
          · obtain rfl := eq_of_beq hll
            simp only [doPerformR, hll, if_true] at hdp
            obtain ⟨a', b', hmemH, hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
            cases hmemH with
            | head =>
                cases hdp
                refine ⟨_, εInner, hh, ?_⟩
                refine StackWfB.callwith (hv.conv hla) (Ty.effWeaken_empty _) ?_
                refine StackWfB.callwith ?_ hweff hrest'
                refine HasTypeV.partialResume (εtop := εtop) (fun εBelow hwB => ?_) (.refl _)
                simp only [Bool.false_eq_true, if_false]
                rw [List.reverse_cons]
                exact stackSeg_append
                  (stackSeg_conv_input (stackSeg_conv_output hacc hσ' (.refl _)) hrb.symm (.refl _))
                  (.delimit hh hε' hwB (.nil (.refl _) (.refl _)))
            | tail hne _ => exact absurd rfl hne
          · simp only [doPerformR, hll, Bool.false_eq_true, if_false] at hdp
            obtain ⟨a', b', hmemT, hla, hrb⟩ := Ty.tyEquiv_effContains_mp hε' hmem
            have hlne : l ≠ label := fun h => by subst h; simp at hll
            have hmemTail : Ty.EffContains tail_d label a' b' := by
              cases hmemT with
              | head => exact absurd rfl hlne
              | tail _ hc => exact hc
            obtain ⟨a'', b'', hc, ha'', hb''⟩ :
                ∃ a'' b'', Ty.EffContains εInner label a'' b'' ∧ Ty.TyEquiv a' a'' ∧
                  Ty.TyEquiv b' b'' := by
              rcases hweff with he | he
              · exact Ty.tyEquiv_effContains_mp he hmemTail
              · exact absurd (Ty.tyEquiv_effContains_mp he hmemTail)
                  (fun ⟨_, _, hcc, _, _⟩ => effContains_empty hcc)
            have hacc' : StackSegWf ((Kontinue.Delimit l h e_ false, mt) :: acc).reverse b'' εtop
                ret_d εInner := by
              rw [List.reverse_cons]
              exact stackSeg_append
                (stackSeg_conv_input (stackSeg_conv_output hacc hσ' (.refl _))
                  (hrb.trans hb'').symm (.refl _))
                (.delimit hh hε' hweff (.nil (.refl _) (.refl _)))
            exact ih (hv.conv (hla.trans ha'')) hrest' hc hacc' hdp

/-- Base-row mirror of `perform_preserves`. -/
theorem perform_preserves_B [BEq m] {label : String} {v : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {argTy εf retTy ε εbot τ : Ty} {cfg' : Config m}
    (hperf : HasTypeV (.Partial (.Perform label) [] : Value m) (.fun argTy εf retTy))
    (hv : HasTypeV v argTy) (hw : Ty.EffWeaken εf ε) (hrest : StackWfB rest retTy ε εbot τ)
    (hr : reduceCall (.Partial (.Perform label) []) v ann fenv rest = .tau cfg') :
    MStateWfB (.run cfg') τ εbot := by
  cases hperf with
  | @partialPerformNil _ argTy' replyTy' μ _ he =>
      obtain ⟨ha, heff, hr'⟩ := Ty.tyEquiv_fun_components he
      obtain ⟨a1, b1, hc1, e1a, e1b⟩ := Ty.tyEquiv_effContains_mp heff Ty.EffContains.head
      obtain ⟨a2, b2, hmemE, e2a, e2b⟩ :
          ∃ a2 b2, Ty.EffContains ε label a2 b2 ∧ Ty.TyEquiv argTy' a2 ∧ Ty.TyEquiv replyTy' b2 := by
        rcases hw with hwe | hwe
        · obtain ⟨a2, b2, hc2, e2a, e2b⟩ := Ty.tyEquiv_effContains_mp hwe hc1
          exact ⟨a2, b2, hc2, e1a.trans e2a, e1b.trans e2b⟩
        · exact absurd (Ty.tyEquiv_effContains_mp hwe hc1)
            (fun ⟨_, _, hcc, _, _⟩ => effContains_empty hcc)
      rw [show reduceCall (.Partial (.Perform label) []) v ann fenv rest
          = reducePerform label v fenv rest from rfl, reducePerform] at hr
      split at hr
      · next p hdp =>
          cases hr
          refine perform_walk_B rest (hv.conv (ha.symm.trans e2a)) hrest hmemE (acc := [])
            (.nil ?_ (.refl _)) hdp
          exact e2b.symm.trans hr'
      · next hdp => exact absurd hr (by simp)
      · next hdp => exact absurd hr (by simp)

/-- Base-row mirror of `reduceCall_perform_wait`. -/
theorem reduceCall_perform_wait_B [BEq m] {f arg : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {argTy εf retTy ε εbot τ : Ty} {op : String} {lift : Value m}
    {envP : Env m} {kP : Stack m}
    (hf : HasTypeV f (.fun argTy εf retTy)) (hw : Ty.EffWeaken εf ε)
    (hrest : StackWfB rest retTy ε εbot τ)
    (h : reduceCall f arg ann fenv rest = .perform op lift envP kP) :
    MStateWfB (.wait op envP kP) τ εbot := by
  rcases canonical_arrow hf with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
  · exact absurd h (by simp [reduceCall])
  · cases hf with
    | partialBuiltin _ _ _ => exact absurd h reduceCall_builtin_ne_perform
    | partialFixed _ _ => rw [reduceCall_fixed] at h; exact absurd h (by simp)
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
    | partialHandleNil _ => simp only [reduceCall] at h; exact absurd h (by simp)
    | partialHandleOne _ _ => simp only [reduceCall, reduceDeep] at h; exact absurd h (by simp)
    | partialResume _ _ => simp only [reduceCall] at h; exact absurd h (by simp)
    | @partialPerformNil label argTy' replyTy' μ _ he =>
        obtain ⟨_, hE, hR⟩ := Ty.tyEquiv_fun_components he
        simp only [reduceCall] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := reducePerform_perform_inv h
        obtain ⟨a'', b'', hEff, _, hRb⟩ := perform_op_mem_ambient hE hw
        exact ⟨a'', b'', retTy, _, hEff, hRb.symm.trans hR, hrest⟩

/-- Base-row mirror of `preservation_perform`. -/
theorem preservation_perform_B [BEq m] {cfg : Config m} {τ εbot : Ty}
    {op : String} {lift : Value m} {envP : Env m} {kP : Stack m}
    (hwf : MStateWfB (.run cfg) τ εbot)
    (h : reduce1Run cfg = .perform op lift envP kP) :
    MStateWfB (.wait op envP kP) τ εbot := by
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
          obtain ⟨τin, εtop, hv, hst⟩ := mStateWfB_V hwf
          cases kont with
          | Trace _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Assign _ _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Arg _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Delimit _ _ _ _ => simp only [reduce1Run, reduceApply] at h; exact absurd h (by simp)
          | Apply f fenv =>
              obtain ⟨argTy, εf, retTy, ε0, hσ, hε, hf, hw, hrest⟩ := stackWfB_applyf_inv hst
              simp only [reduce1Run, reduceApply] at h
              exact reduceCall_perform_wait_B hf hw hrest h
          | CallWith arg fenv =>
              obtain ⟨argTy, εf, retTy, ε0, hσ, hε, harg, hw, hrest⟩ := stackWfB_callwith_inv hst
              simp only [reduce1Run, reduceApply] at h
              exact reduceCall_perform_wait_B (hv.conv hσ) hw hrest h

/-- **Exact-row tau-preservation, isolated.** A silent step keeps the ambient row `ε`
*exactly*. This holds for the **handler-discharge-free** fragment (pure/data/`Perform`/
`Resume`-reply): there every `tau` move keeps `ε`. It is **false in general once
`Handle`/`Delimit` lands** — a `Delimit`-value-pop discharges a label and *shrinks* the
row (`⟨l|tail⟩ → tail`), so the successor is well-typed only at `tail`. Threading the
genuine *row-evolution* (membership of an unhandled `op` reflecting back across the
discharges) is the remaining T7 proof; until then the row-dependent effect-safety /
divergence results below are gated on this hypothesis (the `ε`-free value / no-bad-crash
results are **not** — they hold unconditionally for the full language incl. `Handle`).
Isolated exactly like `FixPreserves`/`HandlerObligations`. -/
def TauKeepsRow (m : Type) [BEq m] : Prop :=
  ∀ {cfg cfg' : Config m} {τ ε : Ty},
    MStateWf (.run cfg) τ ε → reduce1Run cfg = .tau cfg' → MStateWf (.run cfg') τ ε

/-- **Preservation keeping `ε` exactly**, in `fix`-discharged form, gated on `TauKeepsRow`
(the `tau` case) — see its docstring. The `reply` case needs the `ReplyContract` (`hrep`):
the world's supplied reply value inhabits the operation's declared reply type. -/
theorem preservation_keep_fix [BEq m] (hkeep : TauKeepsRow m)
    {s s' : MState m} {μ : Label m} {τ ε : Ty}
    (hwf : MStateWf s τ ε) (hr : Reduce s μ s') (hrep : ReplyContract ε s μ) :
    MStateWf s' τ ε := by
  cases hr with
  | tau h => exact hkeep hwf h
  | perform h => exact preservation_perform hwf h
  | reply =>
      obtain ⟨a, b, replyTy, hEff, hbr, hStack⟩ := hwf
      simp only [ReplyContract] at hrep
      exact ⟨replyTy, (hrep a b hEff).conv hbr, hStack⟩

/-- **Effect safety over `evalR`.** If a well-typed config's `evalR` terminates by
*emitting an effect* `op`, then `op` is a member of the ambient row `ε` (the run can
only escape on a declared effect). Fuel induction threading `ε` across silent steps
(`preservation_tau_fix`) and reading the membership off `progress_fix`'s effect-escape
disjunct at the boundary. -/
theorem soundnessR_effect [BEq m] (hkeep : TauKeepsRow m) (hbad : FixNoBadCrash m) :
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
      | tau cfg' => rw [hrr] at h; exact ih (hkeep hwf hrr) h
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
    (hkeep : TauKeepsRow m)
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
          exact Or.inr (Or.inr (Or.inl
            ⟨r, rfl, soundness_evalR_noBadCrash hpres hbad fuel hty h⟩))
  | effect op lift resume =>
      exact Or.inr (Or.inr (Or.inr ⟨op, lift, resume, rfl,
        soundnessR_effect hkeep hbad fuel (mStateWf_initial hty) h⟩))

/-- **Purity certificate (`A ! ∅`).** A program typed at the **empty** effect row never
emits an effect: its `evalR` is never `.effect _ _ _`. (Eff's `A!∅` purity certificate —
follows from effect safety, since the empty row has no members.) -/
theorem pure_no_perform_evalR [BEq m] (hkeep : TauKeepsRow m) (hbad : FixNoBadCrash m)
    {prog : Tree.Node m} {τ : Ty} {op : String} {lift : Value m} {resume : Value m → Config m}
    (fuel : Nat) (hty : HasType [] prog τ .empty)
    (h : evalR fuel (Config.initial prog) = .effect op lift resume) : False := by
  obtain ⟨a, b, hc⟩ := soundnessR_effect hkeep hbad fuel (mStateWf_initial hty) h
  cases hc

/-- **Whole-program soundness for a pure program.** A program typed at the empty effect
row has only three `evalR` outcomes — timeout, a typed value, or a sanctioned
`Unrepresentable` crash — *never* an emitted effect. The pure specialization of
`soundness_evalR`. -/
theorem soundness_evalR_pure [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m)
    (hkeep : TauKeepsRow m)
    {prog : Tree.Node m} {τ : Ty} (fuel : Nat) (hty : HasType [] prog τ .empty) :
    evalR fuel (Config.initial prog) = .timeout ∨
    (∃ v, evalR fuel (Config.initial prog) = .done (.value v) ∧ HasTypeV v τ) ∨
    (∃ r, evalR fuel (Config.initial prog) = .done (.crash r) ∧ ¬ Reason.IsBad r) := by
  rcases soundness_evalR hpres hbad hkeep fuel hty with h | h | h | ⟨op, lift, resume, h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (pure_no_perform_evalR hkeep hbad fuel hty h).elim

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
theorem soundness_behaviorsR_suspended [BEq m] (hkeep : TauKeepsRow m) (hbad : FixNoBadCrash m)
    {prog : Tree.Node m} {τ ε : Ty} {trace : List (Label m)} {op : String} {lift : Value m}
    (hty : HasType [] prog τ ε)
    (hmem : Behavior.suspended trace op lift ∈ BehaviorsR (Config.initial prog)) :
    ∃ a b, Ty.EffContains ε op a b := by
  obtain ⟨envP, kP, hmtr, hobs⟩ := hmem
  obtain ⟨fuel, resume, hf⟩ := evalR_complete_effect hmtr hobs _ rfl
  exact soundnessR_effect hkeep hbad fuel (mStateWf_initial hty) hf

/-! ## Soundness of divergent behaviours (ω-effect-safety, T7)

A *divergent* `BehaviorsR` behaviour is an infinite `Reduce` execution
(`reduceLTS.ωTr ss μs`). Effect safety for it ("every `perform` the run emits is in the
declared row `ε`") is an ordinary induction over `ℕ` — no coinduction — folding
`preservation_keep_fix` along the execution: every state stays well-typed at `(τ, ε)`,
so by `preservation_perform` each emitted `perform op` lands an in-row `op`. The only
world input is the `ReplyContract` at the `reply` steps (the world supplies well-typed
replies); closed `evalR` never replies, but an open divergent run may. This closes the
"`diverges` (ω-effect-safety)" T7 remainder for the current (pre-`Handle`) fragment,
modulo the isolated `fix`. -/

/-- Inversion of a `perform`-labelled `Reduce` step: it runs a config to the effect
boundary, landing a `wait`. States generalized (so usable when the endpoints are stuck
`ωSequence` applications `ss i`). -/
theorem reduce_perform_inv [BEq m] {s s' : MState m} {op : String} {lift : Value m}
    (h : Reduce s (.perform op lift) s') :
    ∃ cfg envP kP, s = .run cfg ∧ s' = .wait op envP kP ∧
      reduce1Run cfg = .perform op lift envP kP := by
  cases h with
  | perform h => exact ⟨_, _, _, rfl, rfl, h⟩

/-- Every state along an infinite well-typed execution stays well-typed at `(τ, ε)`
(induction over `ℕ`, folding `preservation_keep_fix`). -/
theorem ωTr_all_wf [BEq m] (hkeep : TauKeepsRow m)
    {ss : Cslib.ωSequence (MState m)} {μs : Cslib.ωSequence (Label m)} {τ ε : Ty}
    (hωtr : reduceLTS.ωTr ss μs) (hwf0 : MStateWf (ss 0) τ ε)
    (hrep : ∀ i, ReplyContract ε (ss i) (μs i)) :
    ∀ i, MStateWf (ss i) τ ε := by
  intro i
  induction i with
  | zero => exact hwf0
  | succ n ih => exact preservation_keep_fix hkeep ih (hωtr n) (hrep n)

/-- **ω-effect-safety.** Along an infinite well-typed execution (with well-typed replies),
every emitted `perform op` is a member of the declared effect row `ε`. -/
theorem ωTr_effect_safe [BEq m] (hkeep : TauKeepsRow m)
    {ss : Cslib.ωSequence (MState m)} {μs : Cslib.ωSequence (Label m)} {τ ε : Ty}
    (hωtr : reduceLTS.ωTr ss μs) (hwf0 : MStateWf (ss 0) τ ε)
    (hrep : ∀ i, ReplyContract ε (ss i) (μs i)) :
    ∀ i op lift, μs i = .perform op lift → ∃ a b, Ty.EffContains ε op a b := by
  intro i op lift hμ
  have hwfi : MStateWf (ss i) τ ε := ωTr_all_wf hkeep hωtr hwf0 hrep i
  have hstep : Reduce (ss i) (.perform op lift) (ss (i + 1)) := hμ ▸ hωtr i
  obtain ⟨cfg, envP, kP, hsi, _, hrun⟩ := reduce_perform_inv hstep
  rw [hsi] at hwfi
  obtain ⟨a, b, _, hEff, _, _⟩ := preservation_perform hwfi hrun
  exact ⟨a, b, hEff⟩

/-- **Effect safety for divergent behaviours.** A closed well-typed program's divergent
`BehaviorsR` behaviour emits only `perform`s in its declared row `ε` (given the world
supplies well-typed replies along the witnessing execution). Via `ωTr_effect_safe`. -/
theorem soundness_behaviorsR_diverges [BEq m] (hkeep : TauKeepsRow m)
    {prog : Tree.Node m} {τ ε : Ty} {μs : Cslib.ωSequence (Label m)}
    (hty : HasType [] prog τ ε)
    (hmem : Behavior.diverges μs ∈ BehaviorsR (Config.initial prog))
    (hrep : ∀ ss : Cslib.ωSequence (MState m), reduceLTS.ωTr ss μs →
        ss 0 = .run (Config.initial prog) → ∀ i, ReplyContract ε (ss i) (μs i)) :
    ∀ i op lift, μs i = .perform op lift → ∃ a b, Ty.EffContains ε op a b := by
  obtain ⟨ss, hωtr, hs0⟩ := hmem
  have hwf0 : MStateWf (ss 0) τ ε := by rw [hs0]; exact mStateWf_initial hty
  exact ωTr_effect_safe hkeep hωtr hwf0 (hrep ss hωtr hs0)

/-! ## Soundness of reply-containing terminating traces (T7)

The silent-trace `BehaviorsR` soundness (`soundness_behaviorsR_value`/`_noBadCrash`) goes
through `evalR` (which halts at the first `perform`), so it only covers `tau`-only traces.
An *open* terminating run may resume through `reply` steps; its trace then contains
`perform`/`reply` labels and the `evalR` bridge no longer applies. Such a trace is instead
folded directly over the finite `reduceLTS.MTr` with `preservation_keep_fix`, exactly like
the divergent case. The world input is the reply values: a `reply` step carries its value
in the label (`Label.reply op v`), so the contract is the **trace-level** predicate
`TraceRepliesOk` — every replied value inhabits its operation's declared reply type. -/

/-- Every `reply` value appearing in `trace` inhabits the declared reply type of its
operation (the trace-level form of `ReplyContract`). -/
def TraceRepliesOk {m : Type} [BEq m] (ε : Ty) (trace : List (Label m)) : Prop :=
  ∀ op v, Label.reply op v ∈ trace → ∀ a b, Ty.EffContains ε op a b → HasTypeV v b

/-- The terminal state of a well-typed finite execution (with well-typed replies) stays
well-typed at `(τ, ε)`. Induction over `MTr`, folding `preservation_keep_fix`; the head
`reply` step's `ReplyContract` is read off `TraceRepliesOk`. -/
theorem mTr_terminal_wf [BEq m] (hkeep : TauKeepsRow m)
    {s s' : MState m} {trace : List (Label m)} {τ ε : Ty}
    (hmtr : reduceLTS.MTr s trace s') (hwf : MStateWf s τ ε)
    (hrep : TraceRepliesOk ε trace) : MStateWf s' τ ε := by
  induction hmtr generalizing τ with
  | refl => exact hwf
  | @stepL s1 μ s2 μs s3 htr _hmtr ih =>
      have hrc : ReplyContract ε s1 μ := by
        cases htr with
        | tau _ => exact trivial
        | perform _ => exact trivial
        | @reply op envP kP v =>
            simp only [ReplyContract]
            exact hrep op v (by simp)
      have hwf2 : MStateWf s2 τ ε := preservation_keep_fix hkeep hwf htr hrc
      exact ih hwf2 (fun op v hmem => hrep op v (List.mem_cons_of_mem _ hmem))

/-- From a `terminalR?`-terminal `run` state, expose the `reduce1Run = .done o` witness. -/
theorem terminalR_run [BEq m] {cfg : Config m} {o : Outcome m}
    (h : (MState.run cfg).terminalR? = some o) : reduce1Run cfg = .done o := by
  simp only [MState.terminalR?] at h
  split at h <;> simp_all

/-- **Typed value, reply-containing trace.** A well-typed program whose (possibly
reply-containing) terminating behaviour yields a value gives a value of type `τ`. -/
theorem soundness_behaviorsR_terminates_value [BEq m] (hfix : FixPreserves m)
    (hkeep : TauKeepsRow m)
    {prog : Tree.Node m} {τ ε : Ty} {trace : List (Label m)} {v : Value m}
    (hty : HasType [] prog τ ε) (hrep : TraceRepliesOk ε trace)
    (hmem : Behavior.terminates trace (.value v) ∈ BehaviorsR (Config.initial prog)) :
    HasTypeV v τ := by
  obtain ⟨s', hmtr, hterm⟩ := hmem
  have hwf' : MStateWf s' τ ε := mTr_terminal_wf hkeep hmtr (mStateWf_initial hty) hrep
  cases s' with
  | wait _ _ _ => simp [MState.terminalR?] at hterm
  | run cfg => exact reduce1Run_done_value_typed (builtinAppPreserves hfix) hwf' (terminalR_run hterm)

/-- **No bad crash, reply-containing trace.** A well-typed program's (possibly
reply-containing) terminating crash is never bad (only the sanctioned `Unrepresentable`). -/
theorem soundness_behaviorsR_terminates_noBadCrash [BEq m] (hfix : FixPreserves m)
    (hbad : FixNoBadCrash m) (hkeep : TauKeepsRow m)
    {prog : Tree.Node m} {τ ε : Ty} {trace : List (Label m)}
    {r : Reason m} (hty : HasType [] prog τ ε) (hrep : TraceRepliesOk ε trace)
    (hmem : Behavior.terminates trace (.crash r) ∈ BehaviorsR (Config.initial prog)) :
    ¬ Reason.IsBad r := by
  obtain ⟨s', hmtr, hterm⟩ := hmem
  have hwf' : MStateWf s' τ ε := mTr_terminal_wf hkeep hmtr (mStateWf_initial hty) hrep
  cases s' with
  | wait _ _ _ => simp [MState.terminalR?] at hterm
  | run cfg =>
      have hrc := terminalR_run hterm
      rcases progress_fix hbad hwf' with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc, hnb⟩ | ⟨_, _, _, _, hc, _⟩ <;>
        rw [hrc] at hc
      · simp at hc
      · simp at hc
      · simp only [ReduceStep.done.injEq, Outcome.crash.injEq] at hc; rw [hc]; exact hnb
      · simp at hc

/-! ## Observable purity certificates (`A ! ∅`, `BehaviorsR` level)

`pure_no_perform_evalR` certifies a pure (`τ ! ∅`) program emits no effect under `evalR`.
The `BehaviorsR`-level analogues strengthen that to *all* observable shapes: a pure program
**never suspends** and a pure program's **divergent** trace contains **no `perform`** — the
empty row has no members, so effect safety leaves no room for any boundary event. -/

/-- The `ReplyContract` for the **empty** effect row is vacuous (no `EffContains .empty`). -/
theorem replyContract_empty [BEq m] (s : MState m) (μ : Label m) :
    ReplyContract .empty s μ := by
  unfold ReplyContract
  split
  · intro a b hc; cases hc
  · trivial

/-- **A pure program never suspends.** A program typed at `∅` has no suspended `BehaviorsR`
behaviour (it cannot perform an unhandled effect — the empty row is uninhabited). -/
theorem pure_no_suspend_behaviorsR [BEq m] (hkeep : TauKeepsRow m) (hbad : FixNoBadCrash m)
    {prog : Tree.Node m} {τ : Ty} {trace : List (Label m)} {op : String} {lift : Value m}
    (hty : HasType [] prog τ .empty)
    (hmem : Behavior.suspended trace op lift ∈ BehaviorsR (Config.initial prog)) : False := by
  obtain ⟨a, b, hc⟩ := soundness_behaviorsR_suspended hkeep hbad hty hmem
  cases hc

/-- **A pure program's divergent run emits no `perform`.** Every label of a pure program's
divergent `BehaviorsR` trace is non-`perform` (effect safety + empty row). -/
theorem pure_no_perform_diverges [BEq m] (hkeep : TauKeepsRow m)
    {prog : Tree.Node m} {τ : Ty} {μs : Cslib.ωSequence (Label m)}
    (hty : HasType [] prog τ .empty)
    (hmem : Behavior.diverges μs ∈ BehaviorsR (Config.initial prog)) :
    ∀ i op lift, μs i ≠ .perform op lift := by
  intro i op lift hμ
  obtain ⟨a, b, hc⟩ :=
    soundness_behaviorsR_diverges hkeep hty hmem (fun _ _ _ _ => replyContract_empty _ _) i op lift hμ
  cases hc

/-- **Headline soundness (T7).** A closed well-typed program `prog : τ ! ε` does not go
wrong. Bundling the per-shape results over the transparent observable layer `BehaviorsR`
(modulo the isolated `fix`), every behaviour the program exhibits satisfies:

1. a *silent* terminating **value** is well-typed (`HasTypeV v τ`);
2. a *silent* terminating **crash** is never *bad* — only the sanctioned
   `Unrepresentable` trap, never a type-error crash (`Vacant`/`NotAFunction`/`NoMatch`/…);
3. a boundary **suspension** performs an operation **in the declared row** (`op ∈ ε`).

Divergent behaviours are covered by `soundness_behaviorsR_diverges` (ω-effect-safety) and
open reply-containing terminating traces by `soundness_behaviorsR_terminates_value`/
`_noBadCrash` (via `TraceRepliesOk`). All `BehaviorsR` shapes are now covered modulo the
isolated `fix`. -/
theorem soundness [BEq m] (hpres : FixPreserves m) (hbad : FixNoBadCrash m)
    (hkeep : TauKeepsRow m)
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
   fun hm => soundness_behaviorsR_suspended hkeep hbad hty hm⟩

end Eyg.Types
