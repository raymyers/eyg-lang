import Eyg.Types.Runtime
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

/-- A machine state is well-typed at answer type `τ` and effect row `ε`: the
control yields an intermediate `τin` that the stack carries to `τ`. A `wait`
state is not typeable in the pure core (T5 un-pins this). -/
def MStateWf {m : Type} : MState m → Ty → Ty → Prop
  | .run (.E e, env, k), τ, ε => ∃ Γ τin, EnvWf env Γ ∧ HasType Γ e τin ε ∧ StackWf k τin ε τ
  | .run (.V v, _, k), τ, ε => ∃ τin, HasTypeV v τin ∧ StackWf k τin ε τ
  | .wait _ _ _, _, _ => False

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
