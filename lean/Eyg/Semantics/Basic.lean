import Eyg.Interpreter.State

/-!
# EYG operational semantics — frame & vocabulary (Milestone S0)

This module fixes the *model* for the EYG formal semantics: the LTS state, the
transition labels, and the terminal outcomes. Every later milestone
(`FunctionalBigStep`, `Lts`, `Behavior`) is phrased in terms of the definitions
here, so they stay recognizably close to the CEK interpreter in
`Eyg.Interpreter.State`.

See `Eyg/Semantics/README.md` for the prose rationale and the mapping onto
`Cslib.Foundations.Semantics`.

## State = the CEK configuration

The state of the transition system is *exactly* the interpreter's machine
configuration — a `Control` (expression to evaluate or value to feed back), an
environment `Env`, and a continuation `Stack`. Reusing the interpreter's own
config means the semantics and the implementation share one step function; there
is no second copy of the reduction rules to keep in sync, and environments
eliminate substitution entirely (no capture-avoidance lemmas).

## Labels (decision recorded in S0)

We use **separate** `perform`/`reply` labels rather than a single fused
`effect op lift reply`. Rationale:

* It matches the interpreter harness's two-phase protocol (`State.execute`
  breaks at an unhandled `perform`; `State.resume` feeds a reply back), so the
  trace is literally the interleaving the harness already produces.
* Divergence (S4) must be able to observe `perform`s that never receive a
  `reply` — a server that loops performing effects forever. A fused label cannot
  express an unanswered request.
* Pure machine moves carry `tau`; the *observable* trace is the
  `perform`/`reply` subsequence (the `tau`s are erased by `Label.observable`).
-/

namespace Eyg.Semantics

open Eyg.Interpreter
open Eyg.Ir

/-- The LTS state: the interpreter's CEK configuration
`Control × Env × Stack`. Reused verbatim from `Eyg.Interpreter`, so the
semantics steps the same machine the implementation does. -/
abbrev Config (m : Type) := Control m × Env m × Stack m

/-- An initial configuration for a closed source term: evaluate `exp` in
`scope` with an empty stack (mirrors `State.execute exp scope`). -/
def Config.initial (exp : Tree.Node m) (scope : Scope m := []) : Config m :=
  (.E exp, scope, [])

/-- Transition labels. Pure reduction is `tau`; reaching the effect boundary
emits `perform op lift`; feeding a value back to the resumption emits
`reply op v`. The observable trace is the non-`tau` subsequence. -/
inductive Label (m : Type) where
  /-- An internal reduction step, with no observation. -/
  | tau
  /-- An effect raised to the boundary: operation `op` with payload `lift`. -/
  | perform (op : String) (lift : Value m)
  /-- A value `reply` fed back to the resumption of operation `op`. -/
  | reply (op : String) (reply : Value m)
  deriving Repr, BEq, Inhabited

/-- `true` for the observable (non-`tau`) labels. -/
def Label.isObservable : Label m → Bool
  | .tau => false
  | _ => true

/-- Erase the `tau`s from a trace, leaving the observable `perform`/`reply`
subsequence. -/
def Label.observable (trace : List (Label m)) : List (Label m) :=
  trace.filter Label.isObservable

/-- Terminal outcomes of a run. `value v` is normal termination; `crash reason`
is a first-class observable failure (`Vacant`, `NotAFunction`, `UnhandledEffect`
at top level, …). Non-termination is *not* an `Outcome` — it is the absence of
any terminal config (modeled in `FunctionalBigStep`/`Behavior`). -/
inductive Outcome (m : Type) where
  | value (v : Value m)
  | crash (reason : Reason m)
  deriving Repr, BEq, Inhabited

end Eyg.Semantics
