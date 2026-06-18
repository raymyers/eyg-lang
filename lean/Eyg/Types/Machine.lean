import Eyg.Types.Runtime
import Eyg.Types.EffRow
import Eyg.Semantics.Reduction

/-!
# Continuation & machine-state typing (Milestone T3c-i)

The continuation half of the runtime-typing layer. Following
`references/abstract-machine-type-soundness.md` §2, a continuation stack is typed
as an **answer-type transformer**: `StackWf k τin ε τout` means "feeding a value
of type `τin` (under ambient effect row `ε`) into the stack `k` ultimately yields
an answer of type `τout`". The empty stack is the identity transformer
(`τin = τout`); each frame composes one more transformation.

`MStateWf s τout ε` then types a whole machine state by splitting it into "the
control produces some intermediate `τin`" and "the stack `k` takes `τin` to the
final `τout`". These are the signatures `preservation`/`progress` are stated over
(T3c-ii/iii); they are **fixed once** here (plan rule 1) — later slices add
*frames*/cases, never re-type them.

## Frames in the pure core

`Trace` (pass-through), `Assign` (the `let` continuation — run the body under the
bound value), `Arg` (evaluate the argument, then apply), `Apply`/`CallWith` (apply
a known function value). The effect-delimiting `Delimit` frame and the `wait`
state join in T5; `MStateWf` pins `wait` to `False` for now (pure-core programs
never suspend), to be given real content when effects un-pin the row.
-/

namespace Eyg.Types

open Eyg.Interpreter
open Eyg.Ir
open Eyg.Semantics

/-- A continuation stack as an answer-type transformer: feeding a `τin`-value
into `k` (ambient effect `ε`) yields a final `τout`. -/
inductive StackWf {m : Type} : Stack m → Ty → Ty → Ty → Prop where
  /-- The empty stack is the identity transformer. -/
  | nil {τ ε} : StackWf [] τ ε τ
  /-- `Trace` forwards its incoming value unchanged. -/
  | trace {a w rest τin ε τout} :
      StackWf rest τin ε τout →
      StackWf ((Kontinue.Trace w, a) :: rest) τin ε τout
  /-- `Assign` (the `let` continuation): the incoming value is the definition; the
  body is run in the captured env extended with it. -/
  | assign {a x body fenv Γ defnTy bodyTy ε τout rest} :
      EnvWf fenv Γ →
      HasType ((x, .mono defnTy) :: Γ) body bodyTy ε →
      StackWf rest bodyTy ε τout →
      StackWf ((Kontinue.Assign x body fenv, a) :: rest) defnTy ε τout
  /-- `Arg`: the incoming value is the *function* `argTy →⟨εf⟩ retTy`; the stored
  argument node is evaluated next, then applied. The function's latent `εf` may be
  weakened to the ambient `ε` (`EffWeaken εf ε` — a pure function applied in an
  effectful ambient; exact match for T3–T5). -/
  | arg {a arg fenv Γ argTy εf retTy ε τout rest} :
      EnvWf fenv Γ →
      HasType Γ arg argTy ε →
      Ty.EffWeaken εf ε →
      StackWf rest retTy ε τout →
      StackWf ((Kontinue.Arg arg fenv, a) :: rest) (.fun argTy εf retTy) ε τout
  /-- `Apply f`: the incoming value is the *argument* of type `argTy`; the stored
  function value `f` has type `argTy →⟨εf⟩ retTy`, latent `εf` weakenable to `ε`. -/
  | applyf {a f fenv argTy εf retTy ε τout rest} :
      HasTypeV f (.fun argTy εf retTy) →
      Ty.EffWeaken εf ε →
      StackWf rest retTy ε τout →
      StackWf ((Kontinue.Apply f fenv, a) :: rest) argTy ε τout
  /-- `CallWith arg`: the incoming value is the *function* `argTy →⟨εf⟩ retTy`; the
  stored value `arg` is its argument; latent `εf` weakenable to `ε`. -/
  | callwith {a arg fenv argTy εf retTy ε τout rest} :
      HasTypeV arg argTy →
      Ty.EffWeaken εf ε →
      StackWf rest retTy ε τout →
      StackWf ((Kontinue.CallWith arg fenv, a) :: rest) (.fun argTy εf retTy) ε τout
  /-- A deep `Delimit l handler henv` frame **discharges `l`**: the incoming value (the
  exec's normal result, type `ret`) arrives under the handled row `⟨l:(lift,reply)|tail⟩`,
  and everything below runs under the shrunk row `tail`. **No `EnvWf` premise** (the
  handler is a self-contained value; the frame env is arbitrary at `reduceDeep`). This is
  the one frame where the ambient row changes across the step. -/
  | delimit {a l handler henv lift reply tail ret ε τout rest} :
      HasTypeV handler (handlerTy lift reply tail ret) →
      Ty.EffWeaken tail ε →
      StackWf rest ret ε τout →
      StackWf ((Kontinue.Delimit l handler henv false, a) :: rest)
        ret (.effectExtend l lift reply tail) τout
  /-- **Conversion closure**: the input type and ambient row may be replaced by
  `TyEquiv`-equal ones. Needed so the reified `Resume` continuation (whose stored segment
  endpoints match the operation types only up to `TyEquiv`) plugs into the call-site
  stack. Mirrors the value-level `HasTypeV.conv` baked in at the leaves. -/
  | conv {k σ σ' ε ε' τout} :
      StackWf k σ ε τout → Ty.TyEquiv σ σ' → Ty.TyEquiv ε ε' →
      StackWf k σ' ε' τout

/-! ## Stack composition (keystone for `Resume`/`Handle`, T5d)

The reified `Resume` continuation re-pushes a captured **segment** `acc` (a `StackSegWf`,
which tracks per-endpoint rows — it may contain a row-discharging `Delimit`) onto the
call-site base stack `k` (a `StackWf`). `stackSeg_toStackWf` composes the two: the
segment's hole `(σmid, εmid)` is plugged by `k`. The old uniform-`ε` `stackWf_append`/
`stackWf_move` are gone — they assumed a single ambient row, incompatible with the
row-shrinking `Delimit`/`conv`. -/

/-- The interpreter's `move acc k` (re-push popped frames) is `acc.reverse ++ k`. -/
theorem move_eq {m : Type} (acc k : Stack m) : move acc k = acc.reverse ++ k := by
  induction acc generalizing k with
  | nil => rfl
  | cons hd rest ih => obtain ⟨s, mt⟩ := hd; simp [move, ih, List.reverse_cons]

/-- **Segment → stack composition.** A segment `seg` typed `(σin,εin) ⇒ (σmid,εmid)`
followed by a base stack `k` typed `(σmid,εmid) ⇒ τ` yields `StackWf (seg ++ k) σin εin
τ`: each segment frame becomes the matching `StackWf` frame (the `delimit` frame becomes
`StackWf.delimit`, where the ambient row shrinks). By `induction seg` + `cases hseg`. -/
theorem stackSeg_toStackWf {m : Type} {seg k : Stack m} {σin εin σmid εmid τ : Ty}
    (hseg : StackSegWf seg σin εin σmid εmid) (hk : StackWf k σmid εmid τ) :
    StackWf (seg ++ k) σin εin τ := by
  induction seg generalizing σin εin with
  | nil => cases hseg; exact hk
  | cons hd rest ih =>
      obtain ⟨kont, ann⟩ := hd
      cases hseg with
      | trace h => exact .trace (ih h)
      | assign henv hbody h => exact .assign henv hbody (ih h)
      | arg henv harg hw h => exact .arg henv harg hw (ih h)
      | applyf hf hw h => exact .applyf hf hw (ih h)
      | callwith harg hw h => exact .callwith harg hw (ih h)
      | delimit hh hweak h => exact .delimit hh hweak (ih h)

/-- **Resume composition.** Feeding a reply into `move acc k` is well-typed: `acc.reverse`
(the captured delimited prefix, in original order) is a segment `(reply,εtop) ⇒
(ret,tail)`, composed onto the base stack `k` (`(ret,tail) ⇒ τ`). -/
theorem stackWf_resume {m : Type} {acc k : Stack m} {σin εin σmid εmid τ : Ty}
    (hseg : StackSegWf acc.reverse σin εin σmid εmid) (hk : StackWf k σmid εmid τ) :
    StackWf (move acc k) σin εin τ := by
  rw [move_eq]; exact stackSeg_toStackWf hseg hk

/-! ## Per-frame inversion lemmas (fold `conv`)

`cases hst` on a `StackWf` cannot recurse through the `conv` constructor (it wraps a
smaller `StackWf` on the *same* stack at a different `(σ,ε)`). The four preservation/
progress theorems therefore branch on the **frame** (`cases kont`) and use these
inversion lemmas, which fold `conv` via `TyEquiv.trans` (mirroring the `HasType`
generation lemmas `inv_app` etc. folding `HasType.conv`). Each is proved by `induction`
on the `StackWf` with the cons-stack generalized: the matching frame is `refl`, `conv`
composes, other frames/`nil` contradict the stack head. -/

theorem stackWf_trace_inv {m : Type} {w : Value m} {a : m} {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.Trace w, a) :: rest) σ ε τ) : StackWf rest σ ε τ := by
  generalize hs : ((Kontinue.Trace w, a) :: rest) = s at h
  induction h with
  | trace h' => cases hs; exact h'
  | conv h' hσ hε ih => exact .conv (ih hs) hσ hε
  | _ => simp at hs

theorem stackWf_assign_inv {m : Type} {x : String} {body : Tree.Node m} {fenv : Env m}
    {a : m} {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.Assign x body fenv, a) :: rest) σ ε τ) :
    ∃ Γ defnTy bodyTy ε0, Ty.TyEquiv σ defnTy ∧ Ty.TyEquiv ε ε0 ∧ EnvWf fenv Γ ∧
      HasType ((x, .mono defnTy) :: Γ) body bodyTy ε0 ∧ StackWf rest bodyTy ε0 τ := by
  generalize hs : ((Kontinue.Assign x body fenv, a) :: rest) = s at h
  induction h with
  | assign henv hbody hrest => cases hs; exact ⟨_, _, _, _, .refl _, .refl _, henv, hbody, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨Γ, dT, bT, ε0, hσ', hε', henv, hbody, hrest⟩ := ih hs
      exact ⟨Γ, dT, bT, ε0, hσ.symm.trans hσ', hε.symm.trans hε', henv, hbody, hrest⟩
  | _ => simp at hs

theorem stackWf_arg_inv {m : Type} {arg : Tree.Node m} {fenv : Env m} {a : m}
    {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.Arg arg fenv, a) :: rest) σ ε τ) :
    ∃ Γ argTy εf retTy ε0, Ty.TyEquiv σ (.fun argTy εf retTy) ∧ Ty.TyEquiv ε ε0 ∧
      EnvWf fenv Γ ∧ HasType Γ arg argTy ε0 ∧ Ty.EffWeaken εf ε0 ∧
      StackWf rest retTy ε0 τ := by
  generalize hs : ((Kontinue.Arg arg fenv, a) :: rest) = s at h
  induction h with
  | arg henv harg hw hrest => cases hs; exact ⟨_, _, _, _, _, .refl _, .refl _, henv, harg, hw, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨Γ, aT, εf, rT, ε0, hσ', hε', henv, harg, hw, hrest⟩ := ih hs
      exact ⟨Γ, aT, εf, rT, ε0, hσ.symm.trans hσ', hε.symm.trans hε', henv, harg, hw, hrest⟩
  | _ => simp at hs

theorem stackWf_applyf_inv {m : Type} {f : Value m} {fenv : Env m} {a : m}
    {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.Apply f fenv, a) :: rest) σ ε τ) :
    ∃ argTy εf retTy ε0, Ty.TyEquiv σ argTy ∧ Ty.TyEquiv ε ε0 ∧
      HasTypeV f (.fun argTy εf retTy) ∧ Ty.EffWeaken εf ε0 ∧ StackWf rest retTy ε0 τ := by
  generalize hs : ((Kontinue.Apply f fenv, a) :: rest) = s at h
  induction h with
  | applyf hf hw hrest => cases hs; exact ⟨_, _, _, _, .refl _, .refl _, hf, hw, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨aT, εf, rT, ε0, hσ', hε', hf, hw, hrest⟩ := ih hs
      exact ⟨aT, εf, rT, ε0, hσ.symm.trans hσ', hε.symm.trans hε', hf, hw, hrest⟩
  | _ => simp at hs

theorem stackWf_callwith_inv {m : Type} {arg : Value m} {fenv : Env m} {a : m}
    {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.CallWith arg fenv, a) :: rest) σ ε τ) :
    ∃ argTy εf retTy ε0, Ty.TyEquiv σ (.fun argTy εf retTy) ∧ Ty.TyEquiv ε ε0 ∧
      HasTypeV arg argTy ∧ Ty.EffWeaken εf ε0 ∧ StackWf rest retTy ε0 τ := by
  generalize hs : ((Kontinue.CallWith arg fenv, a) :: rest) = s at h
  induction h with
  | callwith harg hw hrest => cases hs; exact ⟨_, _, _, _, .refl _, .refl _, harg, hw, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨aT, εf, rT, ε0, hσ', hε', harg, hw, hrest⟩ := ih hs
      exact ⟨aT, εf, rT, ε0, hσ.symm.trans hσ', hε.symm.trans hε', harg, hw, hrest⟩
  | _ => simp at hs

/-- `Delimit` inversion. Only the deep (`shallow = false`) frame is typeable; the input
type is the handler's return `ret` and the input row is the handled `⟨l:(lift,reply)|tail⟩`,
while `rest` runs at some ambient `εInner` with `tail ⊑ εInner` (the handle's discharged row
is weakenable to the continuation's ambient — `εInner = tail` in the exact case). -/
theorem stackWf_delimit_inv {m : Type} {l : String} {handler : Value m} {henv : Env m}
    {shallow : Bool} {a : m} {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.Delimit l handler henv shallow, a) :: rest) σ ε τ) :
    ∃ lift reply tail ret εInner, shallow = false ∧ Ty.TyEquiv σ ret ∧
      Ty.TyEquiv ε (.effectExtend l lift reply tail) ∧ Ty.EffWeaken tail εInner ∧
      HasTypeV handler (handlerTy lift reply tail ret) ∧ StackWf rest ret εInner τ := by
  generalize hs : ((Kontinue.Delimit l handler henv shallow, a) :: rest) = s at h
  induction h with
  | delimit hh hw hrest => cases hs; exact ⟨_, _, _, _, _, rfl, .refl _, .refl _, hw, hh, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨li, r, t, re, ei, hsh, hσ', hε', hweff, hh, hrest⟩ := ih hs
      exact ⟨li, r, t, re, ei, hsh, hσ.symm.trans hσ', hε.symm.trans hε', hweff, hh, hrest⟩
  | _ => simp at hs

/-- The empty-stack (identity) inversion, folding `conv`: `StackWf [] σ ε τ` forces the
input type to equal the answer (up to `TyEquiv`). -/
theorem stackWf_nil_inv {m : Type} {σ ε τ : Ty} (h : StackWf ([] : Stack m) σ ε τ) :
    Ty.TyEquiv σ τ := by
  generalize hs : ([] : Stack m) = s at h
  induction h with
  | nil => exact .refl _
  | conv _ hσ hε ih => exact hσ.symm.trans (ih hs)
  | _ => simp at hs

/-- A machine state is well-typed at answer type `τ` and effect row `ε`: the
control yields an intermediate `τin` that the stack carries to `τ`. A `wait op env
k` state (suspended performing `op`, awaiting a reply) is typed by **effect safety**
(T5): `op` is a member of the ambient row `ε` (carrying lift `a`, reply `b`), and
the stack `k` carries a reply of type `b` (up to `TyEquiv`, since the stack's
expected input need only be equivalent to the declared reply type) to the answer
`τ`. The reply value itself is supplied by the world — typed by the reply contract,
discharged in `preservation`'s `reply` case. -/
def MStateWf {m : Type} : MState m → Ty → Ty → Prop
  | .run (.E e, env, k), τ, ε => ∃ Γ τin, EnvWf env Γ ∧ HasType Γ e τin ε ∧ StackWf k τin ε τ
  | .run (.V v, _, k), τ, ε => ∃ τin, HasTypeV v τin ∧ StackWf k τin ε τ
  | .wait op _ k, τ, ε =>
      ∃ a b replyTy, Ty.EffContains ε op a b ∧ Ty.TyEquiv b replyTy ∧ StackWf k replyTy ε τ

/-! ## A well-typed program yields a well-typed initial state

`MStateWf (run (Config.initial prog)) τ ε` reduces to `HasType [] prog τ ε`: the
empty env realizes the empty context and the empty stack is the identity
transformer. This is the entry point the soundness theorem (T3c-iii) starts from. -/

theorem mStateWf_initial {m : Type} {prog : Tree.Node m} {τ ε : Ty}
    (h : HasType [] prog τ ε) : MStateWf (.run (Config.initial prog)) τ ε :=
  ⟨[], τ, EnvWf.nil, h, StackWf.nil⟩

/-! ## Sanity checks -/

section
open Eyg.Ir.Tree

-- The initial state for `(\x. x) 1` is well-typed at `integer ! empty`.
example : MStateWf (.run (Config.initial
    (apply (lambda "x" (variable_ "x")) (integer 1)))) .integer .empty := by
  apply mStateWf_initial
  refine HasType.app (argTy := .integer) ?_ (Ty.effWeaken_refl _) ?_
  · exact HasType.lam (HasType.var (s := .mono .integer) (args := []) rfl)
  · exact HasType.int

-- A non-empty stack: applying the argument frame to a function value flows
-- `integer → integer` to a final `integer`.
example : StackWf [(Kontinue.Apply (.Closure "x" (variable_ "x") []) ([] : Env Unit), ())]
    .integer .empty .integer :=
  StackWf.applyf
    (HasTypeV.closure EnvWf.nil (HasType.var (s := .mono .integer) (args := []) rfl)
      (Ty.TyEquiv.refl _))
    (Ty.effWeaken_refl _)
    StackWf.nil

end

end Eyg.Types
