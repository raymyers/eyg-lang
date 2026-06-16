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

/-! ## Monotonicity in fuel

The workhorse lemma: more fuel never changes a result that already finished
(was not a `timeout`). The proof is purely about the fuel recursion — it never
inspects `step`, only whether it returned `Loop` (recurse) or `Break` (stop) —
so it is independent of the builtin/effect details. -/

/-- One controlled unfold of `eval` at successor fuel (definitional). -/
theorem eval_succ [BEq m] (n : Nat) (c : Control m) (e : Env m) (k_ : Stack m) :
    eval (n + 1) (c, e, k_) =
      match step c e k_ with
      | .Loop c' e' k' => eval n (c', e', k')
      | .Break (.ok v) => .done (.value v)
      | .Break (.error (.UnhandledEffect op lift, _, env, k')) =>
          .effect op lift (fun reply => (.V reply, env, k'))
      | .Break (.error (reason, _, _, _)) => .done (.crash reason) := rfl

/-- One extra unit of fuel preserves any non-`timeout` result. -/
theorem eval_succ_mono [BEq m] :
    ∀ (n : Nat) (cfg : Config m) (r : Result m),
      eval n cfg = r → r ≠ .timeout → eval (n + 1) cfg = r := by
  intro n
  induction n with
  | zero =>
      intro cfg r h hne
      simp only [eval] at h
      exact absurd h.symm hne
  | succ k ih =>
      rintro ⟨c, e, k_⟩ r h hne
      rw [eval_succ] at h ⊢
      cases hs : step c e k_ with
      | Loop c' e' k' =>
          simp only [hs] at h ⊢
          exact ih (c', e', k') r h hne
      | Break res =>
          simp only [hs] at h ⊢
          -- `res` must become concrete for the dead `Loop` arm to iota-reduce away.
          cases res with
          | ok v => exact h
          | error dbg =>
              obtain ⟨reason, _ann, _env, _kk⟩ := dbg
              cases reason <;> exact h

/-- Monotonicity: a non-`timeout` result is stable under any increase in fuel. -/
theorem eval_mono [BEq m] {n n' : Nat} (hle : n ≤ n') {cfg : Config m} {r : Result m}
    (h : eval n cfg = r) (hne : r ≠ .timeout) : eval n' cfg = r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact eval_succ_mono _ cfg r ih hne

/-- `timeout` is downward-closed in fuel: if a larger budget still times out, so
does every smaller one. The contrapositive of `eval_mono`; used by divergence
(S4), where "diverges" means "times out at every fuel". -/
theorem eval_timeout_antitone [BEq m] {n n' : Nat} (hle : n ≤ n') {cfg : Config m}
    (h : eval n' cfg = .timeout) : eval n cfg = .timeout := by
  cases hr : eval n cfg with
  | timeout => rfl
  | done o =>
      have hstable := eval_mono hle hr (by simp)
      rw [h] at hstable; simp at hstable
  | effect op lift resume =>
      have hstable := eval_mono hle hr (by simp)
      rw [h] at hstable; simp at hstable

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

/-! ### Crash agreement with the interpreter (Milestone S7)

The `FBS≡interpreter: 104/104` cross-check (spec harness) only exercises the
*value* path — every spec fixture expects a `value`. These `#guard`s close that
gap directly: on a term that crashes, `eval`'s `.crash reason` agrees with
`execute`'s `.error reason` (same term, same reason), and on a top-level
unhandled effect, `eval`'s `.effect` reconciles with `execute`'s `.error
UnhandledEffect` (the open-boundary ↔ closed-`execute` projection, S7). The
matches are self-checking: a non-crash `eval` falls through to `false`. -/

/-- `eval`'s crash and `execute`'s error agree on the same term. -/
private def crashAgrees (t : Tree.Node Unit) : Bool :=
  match eval 1000 (Config.initial t), execute t [] with
  | .done (.crash gr), .error (ir, _, _, _) => gr == ir
  | _, _ => false

-- unbound variable ⟶ both crash with `UndefinedVariable "z"`
#guard crashAgrees (Tree.variable_ "z")
-- vacant ⟶ both crash with `Vacant`
#guard crashAgrees Tree.vacant
-- applying a non-function ⟶ both crash with `NotAFunction`
#guard crashAgrees (Tree.apply (Tree.integer 1) (Tree.integer 2))
-- undefined builtin ⟶ both crash with `UndefinedBuiltin`
#guard crashAgrees (Tree.builtin "no_such_builtin")

-- top-level unhandled effect: `eval` suspends (`.effect`); `execute` (closed,
-- no oracle) projects to `.error UnhandledEffect`. The two reconcile on op+lift
-- — exactly `fbsAgreesInterp`'s effect case, here exercised by a `#guard`.
#guard (match eval 1000 (Config.initial (Tree.apply (Tree.perform "Boom") (Tree.integer 1))),
    execute (Tree.apply (Tree.perform "Boom") (Tree.integer 1)) [] with
  | .effect op lift _, .error (.UnhandledEffect l v, _, _, _) => op == l && lift == v
  | _, _ => false)
end

/-! ## Agreement with the interpreter (Milestone S5)

We would like `interpreter_eq_fbs`: whatever the unbounded `execute` returns,
the fueled `eval` reaches with some fuel. This **cannot be a kernel theorem**:
`execute` is `loop (step …)`, and `loop` is a `partial def`, which Lean compiles
to a logically *opaque* constant with no equational lemmas (even `unfold loop`
fails). So a hypothesis `execute exp scope = .ok v` carries no decomposable
information, and the bridge is unprovable *as stated over `loop`*.

The interpreter↔FBS agreement is therefore established **executably**: the spec
harness's `fbsAgreesInterp` runs `run` (this FBS) and `execute`/`resume` (the
interpreter) through the same effect oracle and checks they agree — on all 104
spec fixtures (`lake exe spec` ⇒ `FBS≡interpreter: 104/104`). The *proof-level*
knot is tied among the total artifacts instead: `eval` ⟷ `eygLTS`
(`Correspondence.lean`, S3) ⟷ `Behaviors` (`Behavior.lean`, S4). See
`plan/progress/2026-06-16-interpreter-bridge-partial-def.md`. -/

end Eyg.Semantics
