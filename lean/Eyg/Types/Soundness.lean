import Eyg.Types.Machine
import Eyg.Types.Generation

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
  | _ =>
      exfalso
      rcases hasType_expr_form hty with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ |
        ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h

/-- The builtin **application/saturation** preservation obligation, isolated as a
hypothesis (the **T6** deliverable — it needs the per-builtin `Builtin.run` typing,
and `int_add` may legitimately trap with the sanctioned `Unrepresentable`). When a
typed `Partial (Builtin id)` is applied to a typed argument and the machine takes a
`tau` step (i.e. the builtin did *not* crash), the successor stays well-typed. -/
def BuiltinAppPreserves (m : Type) [BEq m] : Prop :=
  ∀ {id : String} {applied : List (Value m)} {arg : Value m} {ann : m} {fenv : Env m}
    {rest : Stack m} {argTy retTy ε τ : Ty} {cfg' : Config m},
    HasTypeV (.Partial (.Builtin id) applied) (.fun argTy ε retTy) →
    HasTypeV arg argTy →
    StackWf rest retTy ε τ →
    reduceCall (.Partial (.Builtin id) applied) arg ann fenv rest = .tau cfg' →
    MStateWf (.run cfg') τ ε

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
      rcases canonical_arrow hf with ⟨x, body, cenv, rfl⟩ | ⟨id, applied, rfl⟩
      · cases hf with
        | closure henvc hbody heqc =>
            obtain ⟨hA, hE, hR⟩ := Ty.tyEquiv_fun_components heqc
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            refine ⟨_, _, EnvWf.cons (fun args => ?_) henvc,
              HasType.conv hbody hR hE, StackWf.trace hrest⟩
            simpa using hv.conv hA.symm
      · simp only [reduce1Run, reduceApply] at hr
        exact hsat hf hv hrest hr
  | callwith harg hrest =>
      rcases canonical_arrow hv with ⟨x, body, cenv, rfl⟩ | ⟨id, applied, rfl⟩
      · cases hv with
        | closure henvc hbody heqc =>
            obtain ⟨hA, hE, hR⟩ := Ty.tyEquiv_fun_components heqc
            simp only [reduce1Run, reduceApply, reduceCall] at hr; cases hr
            refine ⟨_, _, EnvWf.cons (fun args => ?_) henvc,
              HasType.conv hbody hR hE, StackWf.trace hrest⟩
            simpa using harg.conv hA.symm
      · simp only [reduce1Run, reduceApply] at hr
        exact hsat hv harg hrest hr

end Eyg.Types
