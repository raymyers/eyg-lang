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

end Eyg.Types
