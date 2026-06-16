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
  /-- `Arg`: the incoming value is the *function* `argTy →⟨ε⟩ retTy`; the stored
  argument node is evaluated next, then applied. -/
  | arg {a arg fenv Γ argTy retTy ε τout rest} :
      EnvWf fenv Γ →
      HasType Γ arg argTy ε →
      StackWf rest retTy ε τout →
      StackWf ((Kontinue.Arg arg fenv, a) :: rest) (.fun argTy ε retTy) ε τout
  /-- `Apply f`: the incoming value is the *argument* of type `argTy`; the stored
  function value `f` has type `argTy →⟨ε⟩ retTy`. -/
  | applyf {a f fenv argTy retTy ε τout rest} :
      HasTypeV f (.fun argTy ε retTy) →
      StackWf rest retTy ε τout →
      StackWf ((Kontinue.Apply f fenv, a) :: rest) argTy ε τout
  /-- `CallWith arg`: the incoming value is the *function* `argTy →⟨ε⟩ retTy`; the
  stored value `arg` is its argument. -/
  | callwith {a arg fenv argTy retTy ε τout rest} :
      HasTypeV arg argTy →
      StackWf rest retTy ε τout →
      StackWf ((Kontinue.CallWith arg fenv, a) :: rest) (.fun argTy ε retTy) ε τout

/-! ## Stack composition (keystone for `Resume`/`Handle`, T5d)

`StackWf` is *already* a stack-**segment** typing: `StackWf.nil : StackWf [] σ ε σ` is
the identity transformer, so `StackWf seg σin ε σmid` types `seg` as a transformer
`σin ⇒ σmid` (its `nil`-base is the hole that the continuation plugs into). Hence the
delimited continuation that `Resume` reifies (a captured stack prefix `acc`, re-pushed
via `move`) needs no new typing judgment — just these two facts:

* `stackWf_append` — composing two segment typings end-to-end (the hole of the first
  is filled by the second);
* `move_eq` — the interpreter's `move acc k` is `acc.reverse ++ k`.

Together: `StackWf acc.reverse σin ε σmid → StackWf k σmid ε τ → StackWf (move acc k)
σin ε τ`. This is what types `Resume`'s `move frames k` successor in the T5 `Handle`
slice. Proved here, isolated, ahead of the cascade. -/

/-- **Stack composition.** A segment `seg` typed `σin ⇒ σmid` (a `StackWf` whose
`nil`-base is the plug point) followed by a stack `k` typed `σmid ⇒ τ` yields a stack
`seg ++ k` typed `σin ⇒ τ`: the segment's identity base is replaced by `k`. -/
theorem stackWf_append {m : Type} {seg k : Stack m} {σin σmid ε τ : Ty}
    (hseg : StackWf seg σin ε σmid) (hk : StackWf k σmid ε τ) :
    StackWf (seg ++ k) σin ε τ := by
  induction hseg with
  | nil => exact hk
  | trace _ ih => exact .trace (ih hk)
  | assign henv hbody _ ih => exact .assign henv hbody (ih hk)
  | arg henv harg _ ih => exact .arg henv harg (ih hk)
  | applyf hf _ ih => exact .applyf hf (ih hk)
  | callwith harg _ ih => exact .callwith harg (ih hk)

/-- The interpreter's `move acc k` (re-push popped frames) is `acc.reverse ++ k`. -/
theorem move_eq {m : Type} (acc k : Stack m) : move acc k = acc.reverse ++ k := by
  induction acc generalizing k with
  | nil => rfl
  | cons hd rest ih => obtain ⟨s, mt⟩ := hd; simp [move, ih, List.reverse_cons]

/-- **Resume composition.** Feeding a reply into the reified continuation `move acc k`
is well-typed: `acc.reverse` (the delimited prefix in original order) is a segment
`σin ⇒ σmid`, composed onto the base stack `k` (`σmid ⇒ τ`). -/
theorem stackWf_move {m : Type} {acc k : Stack m} {σin σmid ε τ : Ty}
    (hseg : StackWf acc.reverse σin ε σmid) (hk : StackWf k σmid ε τ) :
    StackWf (move acc k) σin ε τ := by
  rw [move_eq]; exact stackWf_append hseg hk

/-- **Resume composition across effect discharge** (the corrected keystone). The
`StackSegWf` analogue of `stackWf_move`: feeding a reply into `move acc k` is well-typed
even when the captured `acc` contains the re-pushed `Delimit` (deep handler), because
`StackSegWf` tracks the per-endpoint rows. This is what types `Resume`'s `move frames k`
successor in the full `Handle` slice. -/
theorem stackSeg_move {m : Type} {acc k : Stack m} {σin εin σmid εmid σout εout : Ty}
    (hseg : StackSegWf acc.reverse σin εin σmid εmid)
    (hk : StackSegWf k σmid εmid σout εout) :
    StackSegWf (move acc k) σin εin σout εout := by
  rw [move_eq]; exact stackSeg_append hseg hk

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
  apply HasType.app (argTy := .integer)
  · exact HasType.lam (HasType.var (s := .mono .integer) (args := []) rfl)
  · exact HasType.int

-- A non-empty stack: applying the argument frame to a function value flows
-- `integer → integer` to a final `integer`.
example : StackWf [(Kontinue.Apply (.Closure "x" (variable_ "x") []) ([] : Env Unit), ())]
    .integer .empty .integer :=
  StackWf.applyf
    (HasTypeV.closure EnvWf.nil (HasType.var (s := .mono .integer) (args := []) rfl)
      (Ty.TyEquiv.refl _))
    StackWf.nil

end

end Eyg.Types
