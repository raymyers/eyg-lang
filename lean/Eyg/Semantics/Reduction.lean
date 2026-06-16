import Eyg.Semantics.Lts

/-!
# Transparent reduction substrate `Reduce` (Milestone T0)

The type-soundness proof needs **preservation**, which — unlike every metatheory
result proved so far — requires knowing *what* each reduction rule computes
("applying a closure extends the env with the argument", "`Select l` on a record
returns field `l`", "a handler frame discharges effect `l`"). The shipped machine
`step` dispatches into `partial def eval`/`apply`/`call`, which Lean compiles to a
kernel-**opaque** constant: `cases h : step c e k` learns nothing about the
successor (see `plan/progress/2026-06-16-partial-def-irreducibility.md`). So
preservation cannot be proved about `step` directly.

This module furnishes the fix the plan (`eyg-type-soundness.md` §T0) calls for: a
**transparent, reducible** small-step relation `Reduce` that the soundness proof
`cases` on. It is environment-based (no substitution), exactly like the machine.

## Key design decision — one transparent *function* `reduce1Run`, not 25 axioms

The machine's `call`/`callBuiltin`/`deep`/`doPerform` are `partial` because a
single `step` can do unbounded work: `Match` re-dispatches via `call branch
inner`; `fix`/`list_fold` re-`call`; `doPerform` walks the stack. Transcribing
that recursion into an inductive relation would reintroduce the very opacity we
are escaping.

The escape hatch is the identity

```
  call f x ann env k  ≡  step (.V x, env, (Kontinue.Apply f env, ann) :: k)
```

(`apply` on an `Apply f` frame *is* `call f x`). So every internal `call f x` is
re-expressed as an explicit intermediate machine state `(.V x, env, Apply f ::
k)`. With that, the only remaining recursions are the stack walk and `move`, both
**structural on the stack list** — total `def`s (`doPerformR` is the transparent
total twin of the interpreter's `partial def doPerform`; `move` was already total).
Hence the entire one-step relation is a single non-recursive, total, *transparent*
function `reduce1Run : Config → ReduceStep`, and `Reduce` is defined from it. Two
payoffs:

* **Determinism is `rfl`** (a function has one output) — no 25-case proof.
* **Inversion is `cases h : reduce1Run cfg`** — it *computes*, exposing the
  successor's structure, which is exactly what preservation needs.

The cost: `Reduce` is *finer-grained* than `step` (a `Match`/`fix`/`deep` move
becomes two `Reduce` steps via the intermediate `Apply` state). The relation is
therefore cross-checked against the machine at the **observable-outcome** level
(`evalR` vs. FBS `eval`) on the fixture battery, not one-step-to-one-step. Each
intermediate state is itself a genuine machine configuration, so no behaviour is
invented — only the granularity differs. (Deviation from the plan's literal
"one `Reduce` step matches one `step` move"; the multi-step outcome agreement is
what soundness actually consumes — see the progress note.)
-/

namespace Eyg.Semantics

open Eyg.Interpreter
open Eyg.Ir

/-! ## One-step result -/

/-- The result of one transparent reduction step from a running `Config`.
Mirrors the three shapes of `Step` over a `run` state: an internal move
(`tau`), reaching the effect boundary (`perform`, suspending into a `wait`), or a
terminal `Outcome` (no outgoing transition). -/
inductive ReduceStep (m : Type) where
  /-- A pure machine move to a new running configuration. -/
  | tau (cfg : Config m)
  /-- The machine performed `op lift` at the boundary; it suspends with the
  resumption context `(envP, kP)`. -/
  | perform (op : String) (lift : Value m) (envP : Env m) (kP : Stack m)
  /-- A terminal outcome (value or crash). -/
  | done (o : Outcome m)
  deriving Inhabited

/-! ## The transparent one-step function

`reduceEval`/`reduceApply`/`reduceCall`/`reduceCallBuiltin`/`reduceDeep`/
`reducePerform` transcribe `eval`/`apply`/`call`/`callBuiltin`/`deep`/`perform`
from `State.lean`, with each internal `call f x` replaced by an `Apply`-frame
intermediate state. None of them is recursive (only the structural
`doPerformR`/`move`/`recordGet`/`Builtin.run` helpers are called), so they are
ordinary total `def`s — no `mutual`, no `partial`. -/

/-- Install a deep handler (`state.deep`): re-expressed as the intermediate state
that next runs `call exec unit` under a fresh `Delimit` frame. -/
def reduceDeep (label : String) (handler exec : Value m) (ann : m)
    (env : Env m) (k : Stack m) : ReduceStep m :=
  .tau (.V unit, env,
    (Kontinue.Apply exec env, ann) :: (Kontinue.Delimit label handler env false, ann) :: k)

/-- Transparent, **total** twin of the interpreter's `partial def doPerform`
(`State.lean`): walk the stack to the nearest matching `Delimit`, capturing the
traversed prefix as the resumption. **Structural recursion on the stack `k`** (it
is decreasing in every recursive call and `partial` was unnecessary), so the
entire `Reduce` path is kernel-transparent — the opaque `partial def doPerform`
no longer appears in `reduce1Run`, which is what lets T5 reason about the
`.perform` effect boundary at the kernel level (the effect analog of the T0
substrate fix). Cross-checked executably against the interpreter on the fixtures
(the `evalR`/`runR` `#guard` battery exercises the perform/handle paths). -/
def doPerformR (label : String) (arg : Value m) (iEnv : Env m) :
    Stack m → List (Kontinue m × m) → Return m
  | (.Delimit l h e shallow, mt) :: rest, acc =>
      if l == label then
        let acc := if shallow then acc else (Kontinue.Delimit label h e false, mt) :: acc
        let resume : Value m := .Partial (.Resume acc iEnv) []
        let k := (Kontinue.CallWith arg e, mt) :: (Kontinue.CallWith resume e, mt) :: rest
        .ok (.V h, e, k)
      else
        doPerformR label arg iEnv rest ((Kontinue.Delimit l h e shallow, mt) :: acc)
  | (kont, mt) :: rest, acc => doPerformR label arg iEnv rest ((kont, mt) :: acc)
  | [], _ => .error (.UnhandledEffect label arg)

/-- Perform an effect (`state.perform` = `doPerform … []`). A handled effect
finds its `Delimit` and resumes (a `tau` loop); an unhandled one reaches the
boundary and suspends (`perform`). `doPerformR` only ever errors with
`UnhandledEffect`, so the last arm is dead. -/
def reducePerform (label : String) (arg : Value m) (env : Env m) (k : Stack m) : ReduceStep m :=
  match doPerformR label arg env k [] with
  | .ok (c, e, k') => .tau (c, e, k')
  | .error (.UnhandledEffect op lift) => .perform op lift env k
  | .error e => .done (.crash e)

/-- Dispatch a fully-applied builtin (`state.callBuiltin`). The 4 stack-coupled
builtins re-express their internal `call` as an `Apply`-frame intermediate
state; the 26 pure builtins run directly via `Builtin.run`. -/
def reduceCallBuiltin [BEq m] (key : String) (applied : List (Value m)) (ann : m)
    (env : Env m) (k : Stack m) : ReduceStep m :=
  match key, applied with
  | "fix", [builder] =>
      .tau (.V (.Partial (.Builtin "fixed") [builder]), env,
        (Kontinue.Apply builder env, ann) :: k)
  | "fixed", [builder, arg] =>
      .tau (.V (.Partial (.Builtin "fixed") [builder]), env,
        (Kontinue.Apply builder env, ann) :: (Kontinue.CallWith arg env, ann) :: k)
  | "list_fold", [lst, st, func] =>
      match Cast.asList lst with
      | .error e => .done (.crash e)
      | .ok [] => .tau (.V st, env, k)
      | .ok (element :: rest) =>
          .tau (.V element, env,
            (Kontinue.Apply func env, ann) ::
            (Kontinue.CallWith st env, ann) ::
            (Kontinue.Apply (.Partial (.Builtin "list_fold") [.LinkedList rest]) env, ann) ::
            (Kontinue.CallWith func env, ann) :: k)
  | "binary_fold", [bin, st, func] =>
      match Cast.asBinary bin with
      | .error e => .done (.crash e)
      | .ok bytes =>
          if bytes.size == 0 then .tau (.V st, env, k)
          else
            let byte := bytes.get! 0
            let rest := bytes.extract 1 bytes.size
            .tau (.V (.Integer (Int.ofNat byte.toNat)), env,
              (Kontinue.Apply func env, ann) ::
              (Kontinue.CallWith st env, ann) ::
              (Kontinue.Apply (.Partial (.Builtin "binary_fold") [.Binary rest]) env, ann) ::
              (Kontinue.CallWith func env, ann) :: k)
  | _, _ =>
      match Builtin.builtinArity key with
      | none => .done (.crash (.UndefinedBuiltin key))
      | some n =>
          if applied.length == n then
            match Builtin.run key applied with
            | .error e => .done (.crash e)
            | .ok value => .tau (.V value, env, k)
          else .tau (.V (.Partial (.Builtin key) applied), env, k)

/-- Apply function value `f` to `arg` (`state.call`), transparently. Every
internal `call g y` (the `Match` re-dispatch, the `Builtin`/`Perform`/`Handle`
delegations) becomes an `Apply`-frame intermediate state, so this is
non-recursive. -/
def reduceCall [BEq m] (f : Value m) (arg : Value m) (ann : m) (env : Env m) (k : Stack m) :
    ReduceStep m :=
  match f with
  | .Closure param body captured =>
      .tau (.E body, (param, arg) :: captured, (Kontinue.Trace arg, ann) :: k)
  | .Partial switch applied =>
      match switch, applied with
      | .Cons, [item] =>
          match Cast.asList arg with
          | .error e => .done (.crash e)
          | .ok elements => .tau (.V (.LinkedList (item :: elements)), env, k)
      | .Extend label, [value] =>
          match Cast.asRecord arg with
          | .error e => .done (.crash e)
          | .ok fields => .tau (.V (.Record (recordInsert fields label value)), env, k)
      | .Overwrite label, [value] =>
          match Cast.asRecord arg with
          | .error e => .done (.crash e)
          | .ok fields =>
              match recordGet fields label with
              | none => .done (.crash (.MissingField label))
              | some _ => .tau (.V (.Record (recordInsert fields label value)), env, k)
      | .Select label, [] =>
          match Cast.asRecord arg with
          | .error e => .done (.crash e)
          | .ok fields =>
              match recordGet fields label with
              | none => .done (.crash (.MissingField label))
              | some value => .tau (.V value, env, k)
      | .Tag label, [] => .tau (.V (.Tagged label arg), env, k)
      | .Match label, [branch, otherwise] =>
          match Cast.asTagged arg with
          | .error e => .done (.crash e)
          | .ok (l, inner) =>
              if l == label then .tau (.V inner, env, (Kontinue.Apply branch env, ann) :: k)
              else .tau (.V arg, env, (Kontinue.Apply otherwise env, ann) :: k)
      | .NoCases, [] => .done (.crash (.NoMatch arg))
      | .Builtin key, applied => reduceCallBuiltin key (applied ++ [arg]) ann env k
      | .Perform label, [] => reducePerform label arg env k
      | .Handle label, [handler] => reduceDeep label handler arg ann env k
      | .Resume frames capturedEnv, [] => .tau (.V arg, capturedEnv, move frames k)
      | switch, applied => .tau (.V (.Partial switch (applied ++ [arg])), env, k)
  | term => .done (.crash (.NotAFunction term))

/-- A value meets the top continuation frame (`state.apply`), transparently. -/
def reduceApply [BEq m] (val : Value m) (env : Env m) (kont : Kontinue m) (ann : m)
    (rest : Stack m) : ReduceStep m :=
  match kont with
  | .Assign label then_ fenv => .tau (.E then_, (label, val) :: fenv, rest)
  | .Arg arg fenv => .tau (.E arg, fenv, (Kontinue.Apply val fenv, ann) :: rest)
  | .Apply f fenv => reduceCall f val ann fenv rest
  | .CallWith arg fenv => reduceCall val arg ann fenv rest
  | .Delimit _ _ _ _ => .tau (.V val, env, rest)
  | .Trace _ => .tau (.V val, env, rest)

/-- One expression → next configuration (`state.eval`), transparently. A crash
reason that `eval` would wrap in `Debug` is surfaced directly as `done (crash
reason)` — the `(ann, env, k)` context is not part of the observable `Outcome`. -/
def reduceEval [BEq m] (exp : Tree.Node m) (env : Env m) (k : Stack m) : ReduceStep m :=
  let ann := exp.annotation
  match exp.expr with
  | .Lambda param body => .tau (.V (.Closure param body env), env, k)
  | .Apply f arg => .tau (.E f, env, (Kontinue.Arg arg env, ann) :: k)
  | .Variable x =>
      match env.lookup x with
      | some term => .tau (.V term, env, k)
      | none => .done (.crash (.UndefinedVariable x))
  | .Let var defn body => .tau (.E defn, env, (Kontinue.Assign var body env, ann) :: k)
  | .Binary data => .tau (.V (.Binary data), env, k)
  | .Integer data => .tau (.V (.Integer data), env, k)
  | .String data => .tau (.V (.String data), env, k)
  | .Tail => .tau (.V (.LinkedList []), env, k)
  | .Cons => .tau (.V (.Partial .Cons []), env, k)
  | .Vacant => .done (.crash .Vacant)
  | .Select label => .tau (.V (.Partial (.Select label) []), env, k)
  | .Tag label => .tau (.V (.Partial (.Tag label) []), env, k)
  | .Perform label => .tau (.V (.Partial (.Perform label) []), env, k)
  | .Empty => .tau (.V unit, env, k)
  | .Extend label => .tau (.V (.Partial (.Extend label) []), env, k)
  | .Overwrite label => .tau (.V (.Partial (.Overwrite label) []), env, k)
  | .Case label => .tau (.V (.Partial (.Match label) []), env, k)
  | .NoCases => .tau (.V (.Partial .NoCases []), env, k)
  | .Handle label => .tau (.V (.Partial (.Handle label) []), env, k)
  | .Builtin id =>
      if isBuiltin id then .tau (.V (.Partial (.Builtin id) []), env, k)
      else .done (.crash (.UndefinedBuiltin id))
  | .ContentReference ref => .done (.crash (.UndefinedReference ref))
  | .ReleaseReference package release cid => .done (.crash (.UndefinedRelease package release cid))
  | .RelativeReference location => .done (.crash (.UndefinedRelative location))

/-- One transparent machine step over a running configuration (`state.step`). -/
def reduce1Run [BEq m] (cfg : Config m) : ReduceStep m :=
  match cfg with
  | (.E exp, env, k) => reduceEval exp env k
  | (.V value, _, []) => .done (.value value)
  | (.V value, env, (kont, ann) :: rest) => reduceApply value env kont ann rest

/-! ## The reduction relation

`Reduce` carries exactly the three transitions of `Step` (Lts.lean), but its
`tau`/`perform` premises reference the **transparent** `reduce1Run`, so a `cases`
on a `Reduce` step exposes the successor configuration — the property
preservation needs and `Step` (opaque `step`) lacks. -/

/-- The transparent EYG reduction relation. -/
inductive Reduce {m : Type} [BEq m] : MState m → Label m → MState m → Prop where
  /-- A pure machine move. -/
  | tau {cfg cfg'} :
      reduce1Run cfg = .tau cfg' →
      Reduce (.run cfg) .tau (.run cfg')
  /-- An effect at the boundary suspends the machine. -/
  | perform {cfg op lift envP kP} :
      reduce1Run cfg = .perform op lift envP kP →
      Reduce (.run cfg) (.perform op lift) (.wait op envP kP)
  /-- A reply resumes the suspended machine. -/
  | reply {op envP kP v} :
      Reduce (.wait op envP kP) (.reply op v) (.run (.V v, envP, kP))

/-! ## Determinism

A `run` state's `(label, successor)` is determined: `reduce1Run` is a function,
so its `tau`/`perform` images are unique. (`reply` from a `wait` state is
intentionally relational in the reply value — the environment supplies it.) -/

/-- From a running configuration the reduction is deterministic. -/
theorem reduce_run_det {m : Type} [BEq m] {cfg : Config m} {μ₁ μ₂ : Label m} {s₁ s₂ : MState m}
    (h₁ : Reduce (.run cfg) μ₁ s₁) (h₂ : Reduce (.run cfg) μ₂ s₂) :
    μ₁ = μ₂ ∧ s₁ = s₂ := by
  cases h₁ with
  | tau e₁ =>
      cases h₂ with
      | tau e₂ => rw [e₁] at e₂; cases e₂; exact ⟨rfl, rfl⟩
      | perform e₂ => rw [e₁] at e₂; cases e₂
  | perform e₁ =>
      cases h₂ with
      | tau e₂ => rw [e₁] at e₂; cases e₂
      | perform e₂ => rw [e₁] at e₂; cases e₂; exact ⟨rfl, rfl⟩

/-! ## Progress (untyped): no state is stuck

Totality of the machine — every running config either is a terminal outcome or
reduces — re-derived for `Reduce` (cf. `Lts.progress`). -/

/-- The terminal outcome of a state, if it has one (a `run` config whose
`reduce1Run` is `done`). -/
def MState.terminalR? {m : Type} [BEq m] : MState m → Option (Outcome m)
  | .run cfg => match reduce1Run cfg with | .done o => some o | _ => none
  | .wait _ _ _ => none

/-- Every state has a terminal outcome or an outgoing `Reduce` transition. -/
theorem progressR {m : Type} [BEq m] (s : MState m) :
    s.terminalR?.isSome ∨ ∃ μ s', Reduce s μ s' := by
  match s with
  | .wait op env k => exact Or.inr ⟨.reply op unit, _, Reduce.reply⟩
  | .run cfg =>
      cases h : reduce1Run cfg with
      | tau cfg' => exact Or.inr ⟨.tau, _, Reduce.tau h⟩
      | perform op lift envP kP => exact Or.inr ⟨.perform op lift, _, Reduce.perform h⟩
      | done o => exact Or.inl (by simp [MState.terminalR?, h])

/-! ## Observable layer: the fueled evaluator `evalR`

`evalR` iterates `reduce1Run` on fuel, mirroring the FBS `eval` (and reusing its
`Result` type). This — not the opaque `eval` — is the transparent object the
soundness theorem (T7) will conclude about. -/

/-- The fuel-indexed evaluator over `reduce1Run`. -/
def evalR [BEq m] : Nat → Config m → Result m
  | 0, _ => .timeout
  | fuel + 1, cfg =>
    match reduce1Run cfg with
    | .tau cfg' => evalR fuel cfg'
    | .done o => .done o
    | .perform op lift envP kP => .effect op lift (fun reply => (.V reply, envP, kP))

/-- One controlled unfold of `evalR` at successor fuel (definitional). -/
theorem evalR_succ [BEq m] (n : Nat) (cfg : Config m) :
    evalR (n + 1) cfg =
      match reduce1Run cfg with
      | .tau cfg' => evalR n cfg'
      | .done o => .done o
      | .perform op lift envP kP => .effect op lift (fun reply => (.V reply, envP, kP)) := rfl

/-- Run `evalR`, folding a list of effect replies through the resumptions (the
analogue of FBS `run`; mirrors the spec harness's effect-folding). -/
def runR [BEq m] (fuel : Nat) :
    Config m → List (String × Value m × Value m) → Result m
  | cfg, oracle =>
    match evalR fuel cfg, oracle with
    | .effect op lift resume, (label, expectLift, reply) :: rest =>
        if op == label && lift == expectLift then
          runR fuel (resume reply) rest
        else .effect op lift resume
    | r, _ => r
  termination_by _ oracle => oracle.length
  decreasing_by simp_wf

/-! ## Executable agreement `Reduce ≈ step`

The only link to the shipped interpreter is *executable* (the opaque
`partial def` precludes a kernel equation — see `FunctionalBigStep.lean` §S5).
These `#guard`s check that `evalR` reaches the **same observable outcome** as the
FBS `eval` (which drives the real `step`) on the fixture battery: values,
crashes, the top-level unhandled effect, and an oracle-resumed effect. A failure
fails `lake build`, so the relation we reason about and the machine we run cannot
silently drift. `evalR` is finer-grained, so it is given more fuel. -/

section
open Eyg.Ir.Tree

/-- `fix(\self.\n. match int_compare(n,0) { Eq -> 1 | _ -> n * self(n-1) })` n. -/
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

-- `(\x. x) 1` ⟶ value 1 (agrees with FBS `eval`)
#guard (evalR 100 (Config.initial
  (Tree.apply (Tree.lambda "x" (Tree.variable_ "x")) (Tree.integer 1)))).value?
  == (eval 100 (Config.initial
  (Tree.apply (Tree.lambda "x" (Tree.variable_ "x")) (Tree.integer 1)))).value?
-- `let x = 2 in x` ⟶ value 2
#guard (evalR 100 (Config.initial (Tree.let_ "x" (Tree.integer 2) (Tree.variable_ "x")))).value?
  == some (.Integer 2)
-- currying `((\x.\y.x) 1) 2` ⟶ 1
#guard (evalR 100 (Config.initial (Tree.apply
    (Tree.apply (Tree.lambda "x" (Tree.lambda "y" (Tree.variable_ "x"))) (Tree.integer 1))
    (Tree.integer 2)))).value? == some (.Integer 1)
-- unbound variable ⟶ crash (UndefinedVariable), agreeing with FBS
#guard (evalR 100 (Config.initial (Tree.variable_ "z"))).crash?
  == (eval 100 (Config.initial (Tree.variable_ "z"))).crash?
#guard (evalR 100 (Config.initial (Tree.variable_ "z"))).crash? == some (.UndefinedVariable "z")
-- vacant ⟶ crash (Vacant)
#guard (evalR 100 (Config.initial Tree.vacant)).crash? == some (.Vacant)
-- non-function application ⟶ crash (NotAFunction)
#guard (match (evalR 100 (Config.initial (Tree.apply (Tree.integer 1) (Tree.integer 2)))).crash? with
  | some (.NotAFunction _) => true | _ => false)
-- record select ⟶ 2 (no MissingField)
#guard (evalR 100 (Config.initial
  (Tree.get (Tree.record [("a", Tree.integer 1), ("b", Tree.integer 2)]) "b"))).value?
  == some (.Integer 2)
-- select missing field ⟶ crash
#guard (match (evalR 100 (Config.initial
  (Tree.get (Tree.record [("a", Tree.integer 1)]) "z"))).crash? with
  | some (.MissingField "z") => true | _ => false)
-- overwrite existing field ⟶ {a:9}
#guard (evalR 100 (Config.initial (Tree.apply (Tree.apply (Tree.overwrite "a") (Tree.integer 9))
  (Tree.record [("a", Tree.integer 1)])))).value? == some (mkRecord [("a", .Integer 9)])
-- list literal ⟶ LinkedList [1,2]
#guard (evalR 100 (Config.initial (Tree.list [Tree.integer 1, Tree.integer 2]))).value?
  == some (.LinkedList [.Integer 1, .Integer 2])
-- variant + match ⟶ 1
#guard (evalR 100 (Config.initial
  (Tree.match_ (Tree.tagged "Some" (Tree.integer 1))
    [("Some", Tree.lambda "x" (Tree.variable_ "x"))]))).value? == some (.Integer 1)
-- int_add ⟶ 5
#guard (evalR 100 (Config.initial (Tree.add (Tree.integer 2) (Tree.integer 3)))).value?
  == some (.Integer 5)
-- partial builtin stays Partial
#guard (evalR 100 (Config.initial (Tree.apply (Tree.builtin "int_add") (Tree.integer 2)))).value?
  == some (.Partial (.Builtin "int_add") [.Integer 2])
-- int_divide by zero ⟶ Error(unit)
#guard (evalR 100 (Config.initial (Tree.apply (Tree.apply (Tree.builtin "int_divide")
  (Tree.integer 7)) (Tree.integer 0)))).value? == some (error unit)
-- list_fold sums [1,2,3] ⟶ 6
#guard (evalR 200 (Config.initial (Tree.call (Tree.builtin "list_fold")
  [Tree.list [Tree.integer 1, Tree.integer 2, Tree.integer 3], Tree.integer 0,
   Tree.builtin "int_add"]))).value? == some (.Integer 6)
-- factorial via fix: 4! ⟶ 24 (agrees with FBS `eval`)
#guard (evalR 3000 (Config.initial (factOf 4))).value?
  == (eval 3000 (Config.initial (factOf 4))).value?
#guard (evalR 3000 (Config.initial (factOf 4))).value? == some (.Integer 24)
-- too little fuel ⟶ timeout
#guard (evalR 3 (Config.initial (factOf 4))).isTimeout == true
-- deep handler that ignores resume ⟶ 1
#guard (evalR 200 (Config.initial
    (let handler := Tree.lambda "p" (Tree.lambda "r" (Tree.variable_ "p"))
     let exec := Tree.lambda "_" (Tree.apply (Tree.perform "Eff") (Tree.integer 1))
     Tree.apply (Tree.apply (Tree.handle "Eff") handler) exec))).value? == some (.Integer 1)
-- deep handler that resumes ⟶ 15
#guard (evalR 200 (Config.initial
    (let handler := Tree.lambda "p" (Tree.lambda "resume"
       (Tree.apply (Tree.variable_ "resume") (Tree.integer 5)))
     let exec := Tree.lambda "_"
       (Tree.let_ "x" (Tree.apply (Tree.perform "Get") Tree.unit)
         (Tree.add (Tree.variable_ "x") (Tree.integer 10)))
     Tree.apply (Tree.apply (Tree.handle "Get") handler) exec))).value? == some (.Integer 15)
-- top-level unhandled effect suspends at the boundary (op/lift agree)
#guard (match evalR 100 (Config.initial (Tree.apply (Tree.perform "Boom") (Tree.integer 1))) with
  | .effect op lift _ => op == "Boom" && lift == (.Integer 1)
  | _ => false)
-- `runR` resumes a top-level effect through an oracle reply ⟶ 15 (matches FBS `run`)
#guard (runR 100 (Config.initial
    (Tree.let_ "x" (Tree.apply (Tree.perform "Get") Tree.unit)
      (Tree.add (Tree.variable_ "x") (Tree.integer 10))))
    [("Get", unit, .Integer 5)]).value? == some (.Integer 15)

end

end Eyg.Semantics
