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

end Eyg.Types
