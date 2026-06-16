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
      exact ⟨τin, HasTypeV.recordNil (inv_empty hty), hst⟩
  | _ =>
      exfalso
      rcases hasType_expr_form hty with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ |
        ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h | h <;> simp at h

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

/-! ## Effect safety for the pure core: no `.perform`

A well-typed pure-core state never reduces via `.perform`: that move only arises
when a `Partial (Perform l) []` value is applied, but no `HasTypeV` rule types a
`Perform` partial, so a well-typed function value (`canonical_arrow`) is never one.
`reduceCallBuiltin` likewise never performs. -/

theorem reduceCallBuiltin_ne_perform [BEq m] {key : String} {applied : List (Value m)}
    {ann : m} {env : Env m} {k : Stack m} {op : String} {lift : Value m}
    {envP : Env m} {kP : Stack m} :
    reduceCallBuiltin key applied ann env k ≠ .perform op lift envP kP := by
  intro h
  unfold reduceCallBuiltin at h
  repeat' split at h
  all_goals simp_all

/-- A well-typed function value never `reduceCall`s to a `.perform`. -/
theorem reduceCall_ne_perform [BEq m] {f arg : Value m} {ann : m} {env : Env m} {k : Stack m}
    {a e r : Ty} {op : String} {lift : Value m} {envP : Env m} {kP : Stack m}
    (hf : HasTypeV f (.fun a e r)) :
    reduceCall f arg ann env k ≠ .perform op lift envP kP := by
  intro h
  rcases canonical_arrow hf with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
  · exact absurd h (by simp [reduceCall])
  · cases hf with
    | partialBuiltin _ _ _ => exact reduceCallBuiltin_ne_perform h

/-- A well-typed state's `reduce1Run` is never `.perform` (pure-core effect safety). -/
theorem not_perform [BEq m] {cfg : Config m} {τ ε : Ty}
    {op : String} {lift : Value m} {envP : Env m} {kP : Stack m}
    (hwf : MStateWf (.run cfg) τ ε)
    (h : reduce1Run cfg = .perform op lift envP kP) : False := by
  obtain ⟨c, env, k⟩ := cfg
  cases c with
  | E e =>
      -- `reduceEval` only yields `.tau`/`.done`
      obtain ⟨expr, ann⟩ := e
      cases expr <;> simp only [reduce1Run, reduceEval] at h <;>
        first | exact absurd h (by simp) | (split at h <;> exact absurd h (by simp))
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
          | applyf hf _ =>
              simp only [reduce1Run, reduceApply] at h
              exact reduceCall_ne_perform hf h
          | callwith _ _ =>
              simp only [reduce1Run, reduceApply] at h
              exact reduceCall_ne_perform hv h

/-! ## Preservation -/

/-- **Preservation**: a well-typed state stays well-typed under `Reduce` (modulo
the T6 builtin-application obligation `hsat`). `reply` is vacuous (`wait` states
are untyped); `perform` is impossible (`not_perform`); `tau` splits into the
`.E`/`.V` cases. -/
theorem preservation [BEq m] (hsat : BuiltinAppPreserves m)
    {s s' : MState m} {μ : Label m} {τ ε : Ty}
    (hwf : MStateWf s τ ε) (hr : Reduce s μ s') : MStateWf s' τ ε := by
  cases hr with
  | tau h =>
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
  | perform h => exact (not_perform hwf h).elim
  | reply => exact hwf.elim

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
          | callwith harg hrest =>
              rcases canonical_arrow hw with ⟨x, body, cenv, rfl⟩ | ⟨sw, applied, rfl⟩
              · exact absurd h (by simp [reduce1Run, reduceApply, reduceCall])
              · cases hw with
                | partialBuiltin hs hp he =>
                    simp only [reduce1Run, reduceApply] at h
                    exact (hsat (.partialBuiltin hs hp he) harg hrest).2 _ h

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
          exact ih (preservation hsat hwf (Reduce.tau hrr)) h
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

/-- **Progress.** A well-typed state either steps (`.tau`), is a terminal value, or
terminates with a *sanctioned* (`¬ IsBad`) crash — never a bad crash, never
`.perform` (`not_perform`). For the builtin-free core this is always step-or-value;
`Unrepresentable` is the only crash a typed program can reach. -/
theorem progress [BEq m] (hbad : BuiltinAppNoBadCrash m)
    {cfg : Config m} {τ ε : Ty} (hwf : MStateWf (.run cfg) τ ε) :
    (∃ cfg', reduce1Run cfg = .tau cfg') ∨ (∃ v, reduce1Run cfg = .done (.value v)) ∨
    (∃ r, reduce1Run cfg = .done (.crash r) ∧ ¬ Reason.IsBad r) := by
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
      | _ =>
          exfalso
          rcases hasType_expr_form hty with ⟨_, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, _, hh⟩ |
            ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩ | hh | hh <;> simp at hh
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
                            exact Or.inr (Or.inr ⟨r, rfl, hbad (.partialBuiltin hs hp he) hw hres⟩)
                    | perform _ _ _ _ =>
                        exact absurd hres (reduceCall_ne_perform (.partialBuiltin hs hp he))
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
                            exact Or.inr (Or.inr
                              ⟨r, rfl, hbad (.partialBuiltin hs hp he) harg hres⟩)
                    | perform _ _ _ _ =>
                        exact absurd hres (reduceCall_ne_perform (.partialBuiltin hs hp he))

end Eyg.Types
