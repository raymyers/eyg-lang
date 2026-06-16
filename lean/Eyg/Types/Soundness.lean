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

end Eyg.Types
