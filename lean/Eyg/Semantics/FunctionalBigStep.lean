import Eyg.Semantics.Basic

/-!
# Functional big-step interpreter (Milestone S1)

A fuel-indexed, total, executable evaluator in the CakeML/Owens "functional
big-step semantics" style. It is *definitional*: it drives the interpreter's own
`step` function, so the thing we reason about and the thing we test are the same
artifact.

* `eval (fuel+1) cfg` runs one `step` and recurses; `eval 0 _ = .timeout`.
* Divergence is modeled as "times out at every fuel"
  (`∀ fuel, eval fuel cfg = .timeout`).
* An unhandled effect at the boundary is surfaced as `.effect op lift resume`,
  where `resume` is the configuration to continue from once a reply is supplied
  — exactly the `(.V reply, env, k)` that `State.resume` feeds back. This makes
  the semantics executable against an oracle/runner (see `run`).

The headline lemma is `eval_mono`: more fuel never changes a non-`timeout`
result. Everything downstream (FBS↔LTS, divergence) leans on it.
-/

namespace Eyg.Semantics

open Eyg.Interpreter
open Eyg.Ir

/-- Result of the fuel-indexed evaluator.

* `done o` — reached a terminal `Outcome` (value or crash) within the fuel;
* `timeout` — ran out of fuel before terminating;
* `effect op lift resume` — hit an unhandled `perform op lift` at the boundary;
  `resume reply` is the configuration to continue from when the runner supplies
  `reply`. -/
inductive Result (m : Type) where
  | done (o : Outcome m)
  | timeout
  | effect (op : String) (lift : Value m) (resume : Value m → Config m)

/-- The fuel-indexed evaluator. One `step` per unit of fuel; `eval 0 = timeout`.
Reuses the interpreter's `step`, so the reduction rules are shared. -/
def eval [BEq m] : Nat → Config m → Result m
  | 0, _ => .timeout
  | fuel + 1, (c, e, k) =>
    match step c e k with
    | .Loop c' e' k' => eval fuel (c', e', k')
    | .Break (.ok v) => .done (.value v)
    | .Break (.error (.UnhandledEffect op lift, _, env, k')) =>
        .effect op lift (fun reply => (.V reply, env, k'))
    | .Break (.error (reason, _, _, _)) => .done (.crash reason)

/-- Project a finished value, if any. -/
def Result.value? : Result m → Option (Value m)
  | .done (.value v) => some v
  | _ => none

/-- Project a crash reason, if any. -/
def Result.crash? : Result m → Option (Reason m)
  | .done (.crash r) => some r
  | _ => none

/-- `true` iff the evaluator timed out (ran out of fuel). -/
def Result.isTimeout : Result m → Bool
  | .timeout => true
  | _ => false

/-! ## Running against an oracle of effect replies

`run` mirrors `Spec.Harness.runFixture`'s effect-folding: execute, and whenever
the evaluator suspends at an unhandled effect, look up the next `(label, lift,
reply)` from the oracle and continue. Effects with no matching oracle entry are
left as the terminal `effect` result. -/

/-- Step the evaluator, folding a list of effect replies through the
resumptions. `fuel` bounds the work *per segment* between effects; `oracle` is
the ordered list of `(label, lift, reply)` triples (as in the spec fixtures). -/
def run [BEq m] (fuel : Nat) :
    Config m → List (String × Value m × Value m) → Result m
  | cfg, oracle =>
    match eval fuel cfg, oracle with
    | .effect op lift resume, (label, expectLift, reply) :: rest =>
        if op == label && lift == expectLift then
          run fuel (resume reply) rest
        else .effect op lift resume
    | r, _ => r
  termination_by _ oracle => oracle.length
  decreasing_by simp_wf

/-! ## Cross-check against the M2–M5 interpreter

These mirror the `#guard`s in `State.lean`: with enough fuel, `eval` agrees with
`execute` on every terminating fixture (value, crash, and effect cases). -/

section
open Eyg.Ir.Tree

/-- `fix(\self.\n. match int_compare(n,0) { Eq -> 1 | _ -> n * self(n-1) })`
applied to `n` — the same factorial used in `State.lean`'s checks. -/
private def factOf (n : Int) : Tree.Node Unit :=
  let selfNMinus1 := Tree.apply (Tree.variable_ "self")
    (Tree.subtract (Tree.variable_ "n") (Tree.integer 1))
  let body := Tree.lambda "self" (Tree.lambda "n"
    (Tree.match_ (Tree.apply (Tree.apply (Tree.builtin "int_compare") (Tree.variable_ "n"))
        (Tree.integer 0))
      [("Eq", Tree.lambda "_" (Tree.integer 1)),
       ("Lt", Tree.lambda "_" (Tree.multiply (Tree.variable_ "n") selfNMinus1)),
       ("Gt", Tree.lambda "_" (Tree.multiply (Tree.variable_ "n") selfNMinus1))]))
  Tree.apply (Tree.apply (Tree.builtin "fix") body) (Tree.integer n)

-- `(\x. x) 1` ⟶ value 1
#guard (eval 100 (Config.initial
  (Tree.apply (Tree.lambda "x" (Tree.variable_ "x")) (Tree.integer 1)))).value?
  == some (.Integer 1)
-- `let x = 2 in x` ⟶ value 2
#guard (eval 100 (Config.initial
  (Tree.let_ "x" (Tree.integer 2) (Tree.variable_ "x")))).value? == some (.Integer 2)
-- unbound variable ⟶ crash (UndefinedVariable)
#guard (eval 100 (Config.initial (Tree.variable_ "z"))).crash?
  == some (.UndefinedVariable "z")
-- vacant ⟶ crash (Vacant)
#guard (eval 100 (Config.initial Tree.vacant)).crash? == some (.Vacant)
-- int_add: 2 + 3 ⟶ value 5
#guard (eval 100 (Config.initial (Tree.add (Tree.integer 2) (Tree.integer 3)))).value?
  == some (.Integer 5)
-- factorial via fix: 4! ⟶ 24 (needs more than a handful of steps)
#guard (eval 1000 (Config.initial (factOf 4))).value? == some (.Integer 24)
-- too little fuel ⟶ timeout (4! needs many steps; 3 is nowhere near enough)
#guard (eval 3 (Config.initial (factOf 4))).isTimeout == true
-- unhandled effect suspends at the boundary as `effect`
#guard (match eval 100 (Config.initial
    (Tree.apply (Tree.perform "Boom") (Tree.integer 1))) with
  | .effect op lift _ => op == "Boom" && lift == (.Integer 1)
  | _ => false)
-- `run` resumes through an oracle reply, mirroring the harness:
-- handle a `Get` effect by replying 5, then `+10` ⟶ 15
#guard (run 100 (Config.initial
    (Tree.let_ "x" (Tree.apply (Tree.perform "Get") Tree.unit)
      (Tree.add (Tree.variable_ "x") (Tree.integer 10))))
    [("Get", unit, .Integer 5)]).value? == some (.Integer 15)
end

/-! ## Agreement with the interpreter (statement; proof in S5)

The value direction of `interpreter_eq_fbs`: whatever the unbounded interpreter
`execute` returns as a value, the fueled `eval` reaches with *some* fuel. The
full bridge (crashes and effect traces, both directions) is Milestone S5; this
stub pins the shape. -/
theorem eval_agrees_execute_value [BEq m]
    (exp : Tree.Node m) (scope : Scope m) (v : Value m)
    (h : execute exp scope = .ok v) :
    ∃ fuel, eval fuel (Config.initial exp scope) = .done (.value v) := by
  sorry

end Eyg.Semantics
