import Eyg.Semantics.FunctionalBigStep
import Cslib.Foundations.Semantics.LTS.Basic

/-!
# The EYG labelled transition system (Milestone S2)

Reflects the CEK machine as a `Cslib.LTS`, so a program's observable behaviour
is a *trace of effect events* (`LTS.MTr` for finite runs, `LTS.ωTr` for infinite
ones in S4). The transition relation `Step` is defined *directly over the
interpreter's `step` function* — there is no second copy of the reduction rules,
so the LTS and the implementation cannot drift apart.

## State: `MState`, a faithful extension of `Config`

Separate `perform`/`reply` labels (the S0 decision) need an intermediate state
between raising an effect and receiving its reply — the machine is *suspended*
with a captured resumption. A bare `Config = Control × Env × Stack` cannot name
that suspended state (there is no value to put in `Control` yet), so the LTS
state is

```
MState := run Config | wait op env k
```

`wait op env k` is the suspended machine: it has performed `op` and holds the
`(env, k)` to resume into once a reply value arrives (exactly the context
`State.resume` feeds back). This is still "the machine configuration" — a CEK
machine genuinely *is* suspended at an unhandled effect — so the model stays
recognizably close to the interpreter.

## Transitions

* `tau` — a pure machine move: `step c e k = Loop c' e' k'`.
* `perform op lift` — `step` hits an unhandled effect at the boundary
  (`Break (UnhandledEffect op lift)`), suspending into `wait op env k`.
* `reply op v` — feed value `v` back, resuming to `run (V v, env, k)`.

Terminal `run` states (where `step` breaks with a value or a non-effect crash)
have no outgoing transition; `wait` states always can `reply`. `progress` makes
this precise: every state is `Terminated` or has a transition (no state is
`Stuck`).
-/

namespace Eyg.Semantics

open Eyg.Interpreter
open Eyg.Ir
open Cslib

/-- The LTS state: a running CEK configuration, or a machine suspended at an
unhandled effect `op` with the resumption context `(env, k)`. -/
inductive MState (m : Type) where
  | run (cfg : Config m)
  | wait (op : String) (env : Env m) (k : Stack m)

/-- The EYG transition relation, defined over the interpreter's `step`. -/
inductive Step {m : Type} [BEq m] : MState m → Label m → MState m → Prop where
  /-- A pure machine move carries no observation. -/
  | tau {c e k c' e' k'} :
      step c e k = .Loop c' e' k' →
      Step (.run (c, e, k)) .tau (.run (c', e', k'))
  /-- An unhandled effect at the boundary suspends the machine. -/
  | perform {c e k op lift ann envP kP} :
      step c e k = .Break (.error (.UnhandledEffect op lift, ann, envP, kP)) →
      Step (.run (c, e, k)) (.perform op lift) (.wait op envP kP)
  /-- A reply value resumes the suspended machine. -/
  | reply {op envP kP v} :
      Step (.wait op envP kP) (.reply op v) (.run (.V v, envP, kP))

/-- The EYG LTS over machine states and effect labels. -/
def eygLTS {m : Type} [BEq m] : LTS (MState m) (Label m) := ⟨Step⟩

@[simp] theorem eygLTS_Tr {m : Type} [BEq m] {s μ s'} :
    (eygLTS (m := m)).Tr s μ s' ↔ Step s μ s' := Iff.rfl

/-- `tau` is the internal label, so the EYG LTS supports cslib's weak-transition
and divergence machinery. -/
instance {m : Type} : HasTau (Label m) where
  τ := .tau

/-! ## Terminal states and outcomes -/

/-- The terminal `Outcome` of a state, if it is terminal: a `run` config whose
`step` breaks with a value (`value`) or a non-effect crash (`crash`). A `wait`
state, a `Loop`, and an unhandled-effect `Break` are *not* terminal. -/
def MState.outcome? {m : Type} [BEq m] : MState m → Option (Outcome m)
  | .run (c, e, k) =>
      match step c e k with
      | .Break (.ok v) => some (.value v)
      | .Break (.error (.UnhandledEffect _ _, _, _, _)) => none
      | .Break (.error (reason, _, _, _)) => some (.crash reason)
      | .Loop _ _ _ => none
  | .wait _ _ _ => none

/-- A state is terminated iff it has a terminal outcome. -/
def Terminated {m : Type} [BEq m] (s : MState m) : Prop := s.outcome?.isSome

/-- Terminating at a value. -/
def MState.IsValue {m : Type} [BEq m] (s : MState m) : Prop :=
  ∃ v, s.outcome? = some (.value v)

/-- Terminating at a crash. -/
def MState.IsCrash {m : Type} [BEq m] (s : MState m) : Prop :=
  ∃ r, s.outcome? = some (.crash r)

/-! ## Progress: no state is stuck

Totality of the machine (ill-formed terms crash rather than getting stuck)
means every state either is terminated or can take a step. Hence the cslib
`Stuck` predicate is empty for `eygLTS`. -/

/-- Every state is terminated or has an outgoing transition. -/
theorem progress {m : Type} [BEq m] (s : MState m) :
    Terminated s ∨ ∃ μ s', Step s μ s' := by
  match s with
  | .wait op env k => exact Or.inr ⟨.reply op unit, _, Step.reply⟩
  | .run (c, e, k) =>
      cases h : step c e k with
      | Loop c' e' k' => exact Or.inr ⟨.tau, _, Step.tau h⟩
      | Break res =>
          cases res with
          | ok v => exact Or.inl (by simp [Terminated, MState.outcome?, h])
          | error d =>
              obtain ⟨reason, ann, envP, kP⟩ := d
              cases reason with
              | UnhandledEffect op lift => exact Or.inr ⟨.perform op lift, _, Step.perform h⟩
              | _ => exact Or.inl (by simp [Terminated, MState.outcome?, h])

/-- No state of `eygLTS` is `Stuck` (with `Terminated` as the termination
predicate): progress always offers an outcome or a move. -/
theorem not_stuck {m : Type} [BEq m] (s : MState m) :
    ¬ (eygLTS (m := m)).Stuck (Terminated := Terminated) s := by
  rintro ⟨hnt, hno⟩
  rcases progress s with hterm | ⟨μ, s', hstep⟩
  · exact hnt hterm
  · exact hno ⟨μ, s', hstep⟩

/-! ## Sanity checks: concrete transitions and a multistep run -/

-- NOTE on concrete examples: the machine's `step` dispatches into `partial def`
-- (`eval`/`apply`/`call`), which is irreducible, so `tau`/`perform` transitions
-- on a *concrete* config cannot be discharged by `rfl`. They are instead
-- exercised abstractly (`progress` cases on `step c e k`) and executably (the
-- FBS `eval`/`run` over `step`, cross-checked on every spec fixture). The
-- `reply` rule references no `step`, so concrete `reply` transitions *are*
-- provable directly.

section
-- A suspended machine can be replied to.
example : Step (.wait "Get" [] [] : MState Unit) (.reply "Get" (.Integer 5))
    (.run (.V (.Integer 5), [], [])) :=
  Step.reply

-- A single transition is a one-step `MTr`: replying to a suspended machine.
example : (eygLTS (m := Unit)).MTr (.wait "Get" [] [])
    [.reply "Get" (.Integer 5)] (.run (.V (.Integer 5), [], [])) :=
  LTS.MTr.single (eygLTS (m := Unit)) Step.reply

end

end Eyg.Semantics
