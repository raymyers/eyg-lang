import Eyg.Semantics.Behavior
import Cslib.Foundations.Semantics.LTS.TraceEq

/-!
# Metatheory & packaging (Milestone S6, stretch)

S6 is the on-ramp to verified compilation; the plan deliberately defers most of
it. This module lands the pieces that are *free* given the earlier milestones —
the cslib equivalence packaging, which our `instDeterministic` unlocks — and
records the status of the genuinely-deferred items.

## Delivered here

* **Trace-equivalence / bisimulation packaging.** cslib's `TraceEq` instantiates
  at `eygLTS`; because the LTS is deterministic, trace equivalence is a
  simulation (`mstate_traceEq_sim`), and determinism also makes the LTS
  image-finite for free.

## Tracked, deferred (see `plan/eyg-semantics.md` §S6)

* **Value relation** `V : Value → Value → Prop` (structural on data, *behavioural*
  on closures). Deliberately deferred: it is the genuinely new proof machinery
  and only pays off once a compiler/target enters the picture (difference-doc).
  The behavioural-closure case needs a step-indexed / coinductive definition.
* **Denotational packaging** via `Foundations/Control/Monad/Free` — optional.
* **Shared builtin specification** — *already satisfied by construction*: the FBS
  `eval`/`run` drive the interpreter's own `step`, which dispatches builtins
  through `callBuiltin`/`Builtin.run`. There is exactly one builtin
  implementation, shared by interpreter and FBS; a future compiler target would
  reuse the same `Builtin` module. (The `lake exe spec` `FBS≡interpreter: 104/104`
  cross-check exercises this on every builtin fixture.)
-/

namespace Eyg.Semantics

open Eyg.Interpreter
open Cslib

/-- Trace equivalence of EYG machine states, packaged from cslib at `eygLTS`. -/
abbrev MStateTraceEq {m : Type} [BEq m] (s1 s2 : MState m) : Prop :=
  TraceEq eygLTS s1 s2

/-- Trace equivalence on EYG states is an equivalence relation (cslib). -/
theorem mstateTraceEq_equiv {m : Type} [BEq m] :
    Equivalence (TraceEq (eygLTS (m := m))) :=
  TraceEq.eqv eygLTS

/-- Because `eygLTS` is deterministic, trace equivalence is a simulation: a step
on one side is matched by an equally-labelled step into a trace-equivalent
state. This is the bisimulation-packaging on-ramp (`LTS/TraceEq`). -/
theorem mstate_traceEq_sim {m : Type} [BEq m] (s1 s2 : MState m)
    (h : MStateTraceEq s1 s2) :
    ∀ μ s1', eygLTS.Tr s1 μ s1' → ∃ s2', eygLTS.Tr s2 μ s2' ∧ MStateTraceEq s1' s2' :=
  TraceEq.deterministic_sim eygLTS s1 s2 h

/-- Determinism makes the EYG LTS image-finite for free (cslib
`deterministic_imageFinite`). -/
example : (eygLTS (m := Unit)).ImageFinite := inferInstance

end Eyg.Semantics
