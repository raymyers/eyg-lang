---
date: 2026-06-16
milestone: S5
status: blocker documented; achievable parts delivered
---

# S5 `interpreter_eq_fbs` is not a kernel theorem (opaque `partial def loop`)

## What S5 asked for

A proof that the executable interpreter (`Eyg.Interpreter.State.execute` /
`resume`) agrees with the total FBS semantics (`eval`/`run`) — "same value, same
crash, same effect sequence", stated over the trace.

## Why the kernel proof is blocked

`execute exp scope = loop (step (.E exp) scope [])`, and `loop` is a
`partial def`. In Lean 4, `partial def` compiles to a **logically opaque**
constant (inhabited witness + `@[implemented_by]` for `#eval`/compilation); it
has **no equational lemmas**. Confirmed: `unfold loop` fails, `simp [loop]` /
`rw [loop]` have nothing to use. So a hypothesis like `execute exp scope = .ok v`
is opaque — it cannot be decomposed to relate to `eval`. The former stub
`eval_agrees_execute_value` was therefore unprovable as stated; it has been
removed (no `sorry` remains in the project).

This is the proof-side companion of
`2026-06-16-partial-def-irreducibility.md` (which covered `step` being
unevaluable on concrete configs).

## What was delivered instead

1. **Executable bridge (the real guarantee).** `Spec.Harness.fbsAgreesInterp`
   drives `run` (FBS) and `execute`/`resume` (interpreter) through the *same*
   effect oracle and checks equality of value / crash / unhandled-effect
   boundary, on **all 104 spec fixtures**. `lake exe spec` prints
   `FBS≡interpreter: 104/104` and fails the build on any mismatch. This is the
   analogue, at the testing level, of the interpreter's own `executeLemma`.

2. **Proof-level knot among the total artifacts.** `eval` ⟷ `eygLTS`
   (`Correspondence.lean`, S3) ⟷ `Behaviors` (`Behavior.lean`, S4), all
   kernel-proved. `Behavior.lean` adds `eval_done_mem_behaviors`,
   `eval_effect_mem_behaviors`, `timeout_mem_behaviors`: every `eval` outcome
   (value/crash, effect, divergence) is realized as a member of `Behaviors`.

Net: interpreter →(executable, 104/104)→ `run`/`eval` →(kernel proof)→ `eygLTS`
→(kernel proof)→ `Behaviors`.

## If a kernel `interpreter_eq_fbs` is ever required

Refound the machine driver as a **total** function so it has equational lemmas:
either (a) make `eval`/`run` (already total, fuel-indexed) the *definitional*
interpreter and derive `execute` as `run` at "sufficient fuel" / a
`partial_fixpoint`, or (b) prove `loop` terminating via a measure where it does.
Both are sizeable and not currently justified — the executable cross-check
already pins the behaviour on the whole conformance suite.
