import Eyg.Interpreter.Break
import Eyg.Interpreter.Cast
import Eyg.Interpreter.Builtin

/-!
# EYG CEK machine

Mirrors `packages/gleam_interpreter/src/eyg/interpreter/state.gleam`.

The machine is a CEK-style state machine threaded through a step loop, exactly
as in the Gleam source. `eval` takes one expression to the next configuration,
`apply` feeds a value to the top continuation frame, `call` applies a function
value to an argument, and `step`/`loop` drive them.

## Error-type discipline (matching the Gleam `result.map_error` boundaries)

- `call` / `callBuiltin` / `perform` / `deep` return `Return m` — an
  `Except (Reason m) …` (error is a bare `Reason`).
- `eval` / `apply` wrap that into `Except (Debug m) …` via `mapError`, attaching
  the `(ann, env, stack)` context. `Debug := Reason × m × Env × Stack`.
- `step`/`loop` consume the `Debug`-flavoured results and `Break` on error.

## Builtins (decision #1)

Builtins are not stored in the environment. `eval` validates an `ir.Builtin id`
node against the known-name set `isBuiltin` (matches Gleam's
`dict.get(env.builtins, id)` check), and a fully-applied `Switch.Builtin` is
dispatched by name in `callBuiltin` (M4).

## Milestone status

This file currently implements **Milestone 2** (core lambda-calculus machine):
`eval` for every node, `apply` for every frame, and `call` for `Closure`, the
generic `Partial` accumulation, and `NotAFunction`. The switch-specific `call`
arms (records/variants/lists/match — M3; builtins — M4; perform/handle/resume —
M5) are added in later milestones.
-/

namespace Eyg.Interpreter

open Eyg.Ir

/-! ## Builtin name set (decision #1) -/

/-- An `ir.Builtin id` node is valid iff `id` is a registered builtin. The
single source of truth is `Builtin.builtinArity` (which mirrors Gleam's
`builtin.all`): an identifier is a builtin exactly when it has an arity. -/
def isBuiltin (id : String) : Bool := (Builtin.builtinArity id).isSome

/-! ## Machine configuration types (state.gleam:18-47) -/

/-- The control component: an expression to evaluate, or a value to feed back. -/
inductive Control (m : Type) where
  | E (node : Tree.Node m)
  | V (value : Value m)
  deriving Repr, Inhabited

/-- Debug info attached to a break: the reason plus the configuration. -/
abbrev Debug (m : Type) := Reason m × m × Env m × Stack m

/-- Outcome of one machine step. -/
inductive Next (m : Type) where
  | Loop (c : Control m) (env : Env m) (stack : Stack m)
  | Break (result : Except (Debug m) (Value m))

/-- Result of `eval`/`apply` — error carries full `Debug` context. -/
abbrev EvalReturn (m : Type) := Except (Debug m) (Control m × Env m × Stack m)

/-- Result of `call`/`callBuiltin`/`perform`/`deep` — error is a bare `Reason`. -/
abbrev Return (m : Type) := Except (Reason m) (Control m × Env m × Stack m)

/-! ## Effect helper (state.gleam:232) -/

/-- Re-push a list of popped frames onto the stack (`state.move`). Folds each
`(kontinue, meta)` back on top of `acc`, reversing `delimited` onto it. -/
def move : List (Kontinue m × m) → Stack m → Stack m
  | [], acc => acc
  | (step, mt) :: rest, acc => move rest ((step, mt) :: acc)

/-! ## The machine (state.gleam:91-211) -/

mutual

/-- One expression → next configuration (`state.gleam:91`). -/
partial def eval [BEq m] (exp : Tree.Node m) (env : Env m) (k : Stack m) : EvalReturn m :=
  let ann := exp.annotation
  let value : Value m → Return m := fun val => .ok (.V val, env, k)
  let res : Return m :=
    match exp.expr with
    | .Lambda param body => .ok (.V (.Closure param body env), env, k)
    | .Apply f arg => .ok (.E f, env, (Kontinue.Arg arg env, ann) :: k)
    | .Variable x =>
        match env.lookup x with
        | some term => .ok (.V term, env, k)
        | none => .error (.UndefinedVariable x)
    | .Let var defn body => .ok (.E defn, env, (Kontinue.Assign var body env, ann) :: k)
    | .Binary data => value (.Binary data)
    | .Integer data => value (.Integer data)
    | .String data => value (.String data)
    | .Tail => value (.LinkedList [])
    | .Cons => value (.Partial .Cons [])
    | .Vacant => .error .Vacant
    | .Select label => value (.Partial (.Select label) [])
    | .Tag label => value (.Partial (.Tag label) [])
    | .Perform label => value (.Partial (.Perform label) [])
    | .Empty => value unit
    | .Extend label => value (.Partial (.Extend label) [])
    | .Overwrite label => value (.Partial (.Overwrite label) [])
    | .Case label => value (.Partial (.Match label) [])
    | .NoCases => value (.Partial .NoCases [])
    | .Handle label => value (.Partial (.Handle label) [])
    | .Builtin id =>
        if isBuiltin id then value (.Partial (.Builtin id) [])
        else .error (.UndefinedBuiltin id)
    | .ContentReference ref => .error (.UndefinedReference ref)
    | .ReleaseReference package release cid => .error (.UndefinedRelease package release cid)
    | .RelativeReference location => .error (.UndefinedRelative location)
  res.mapError (fun reason => (reason, ann, env, k))

/-- A value meets the top continuation frame (`state.gleam:137`). -/
partial def apply [BEq m] (val : Value m) (env : Env m) (k : Kontinue m) (ann : m) (rest : Stack m) :
    EvalReturn m :=
  let res : Return m :=
    match k with
    | .Assign label then_ fenv => .ok (.E then_, (label, val) :: fenv, rest)
    | .Arg arg fenv => .ok (.E arg, fenv, (Kontinue.Apply val fenv, ann) :: rest)
    | .Apply f fenv => call f val ann fenv rest
    | .CallWith arg fenv => call val arg ann fenv rest
    | .Delimit _ _ _ _ => .ok (.V val, env, rest)
    | .Trace _ => .ok (.V val, env, rest)
  res.mapError (fun reason => (reason, ann, env, rest))

/-- Apply a function value `f` to argument `arg` (`state.gleam:152`).

`Closure` binds the param and enters the body; the `Partial`-switch arms run
the structured-value operators (M3). Builtins (`Switch.Builtin`, M4) and effects
(`Perform`/`Handle`/`Resume`, M5) are not yet wired and currently fall through
the generic accumulation catch-all. -/
partial def call [BEq m] (f : Value m) (arg : Value m) (ann : m) (env : Env m) (k : Stack m) : Return m :=
  match f with
  | .Closure param body captured =>
      .ok (.E body, (param, arg) :: captured, (Kontinue.Trace arg, ann) :: k)
  | .Partial switch applied =>
      match switch, applied with
      | .Cons, [item] =>
          match Cast.asList arg with
          | .error e => .error e
          | .ok elements => .ok (.V (.LinkedList (item :: elements)), env, k)
      | .Extend label, [value] =>
          match Cast.asRecord arg with
          | .error e => .error e
          | .ok fields => .ok (.V (.Record (recordInsert fields label value)), env, k)
      | .Overwrite label, [value] =>
          match Cast.asRecord arg with
          | .error e => .error e
          | .ok fields =>
              match recordGet fields label with
              | none => .error (.MissingField label)
              | some _ => .ok (.V (.Record (recordInsert fields label value)), env, k)
      | .Select label, [] =>
          match Cast.asRecord arg with
          | .error e => .error e
          | .ok fields =>
              match recordGet fields label with
              | none => .error (.MissingField label)
              | some value => .ok (.V value, env, k)
      | .Tag label, [] => .ok (.V (.Tagged label arg), env, k)
      | .Match label, [branch, otherwise] =>
          match Cast.asTagged arg with
          | .error e => .error e
          | .ok (l, inner) =>
              if l == label then call branch inner ann env k
              else call otherwise arg ann env k
      | .NoCases, [] => .error (.NoMatch arg)
      | .Builtin key, applied => callBuiltin key (applied ++ [arg]) ann env k
      | .Perform label, [] => perform label arg env k
      | .Handle label, [handler] => deep label handler arg ann env k
      | .Resume frames capturedEnv, [] => .ok (.V arg, capturedEnv, move frames k)
      | switch, applied => .ok (.V (.Partial switch (applied ++ [arg])), env, k)
  | term => .error (.NotAFunction term)

/-- Dispatch a (fully-applied) builtin by name (`state.gleam:214`, decision #1).

The 4 stack-coupled builtins push continuation frames and re-enter `call` here;
the 26 pure builtins delegate to `Builtin.run`. Under/over-application (arg count
≠ arity) accumulates as `Partial (Builtin key) applied`, matching the Gleam
`_, _args -> Partial` fall-through. -/
partial def callBuiltin [BEq m] (key : String) (applied : List (Value m)) (ann : m)
    (env : Env m) (k : Stack m) : Return m :=
  match key, applied with
  | "fix", [builder] =>
      call builder (.Partial (.Builtin "fixed") [builder]) ann env k
  | "fixed", [builder, arg] =>
      call builder (.Partial (.Builtin "fixed") [builder]) ann env
        ((Kontinue.CallWith arg env, ann) :: k)
  | "list_fold", [lst, st, func] =>
      match Cast.asList lst with
      | .error e => .error e
      | .ok [] => .ok (.V st, env, k)
      | .ok (element :: rest) =>
          call func element ann env
            ((Kontinue.CallWith st env, ann) ::
             (Kontinue.Apply (.Partial (.Builtin "list_fold") [.LinkedList rest]) env, ann) ::
             (Kontinue.CallWith func env, ann) :: k)
  | "binary_fold", [bin, st, func] =>
      match Cast.asBinary bin with
      | .error e => .error e
      | .ok bytes =>
          if bytes.size == 0 then .ok (.V st, env, k)
          else
            let byte := bytes.get! 0
            let rest := bytes.extract 1 bytes.size
            call func (.Integer (Int.ofNat byte.toNat)) ann env
              ((Kontinue.CallWith st env, ann) ::
               (Kontinue.Apply (.Partial (.Builtin "binary_fold") [.Binary rest]) env, ann) ::
               (Kontinue.CallWith func env, ann) :: k)
  | _, _ =>
      match Builtin.builtinArity key with
      | none => .error (.UndefinedBuiltin key)
      | some n =>
          if applied.length == n then
            match Builtin.run key applied with
            | .error e => .error e
            | .ok value => .ok (.V value, env, k)
          else .ok (.V (.Partial (.Builtin key) applied), env, k)

/-- Walk the stack to the nearest matching `Delimit`, capturing the traversed
prefix as the resumption (`state.do_perform`). On reaching the handler, install
`CallWith arg :: CallWith resume :: rest` and run the handler `h`. -/
partial def doPerform (label : String) (arg : Value m) (iEnv : Env m) (k : Stack m)
    (acc : List (Kontinue m × m)) : Return m :=
  match k with
  | (.Delimit l h e shallow, mt) :: rest =>
      if l == label then
        -- shallow is always false for the suite; keep the field for shape parity
        let acc := if shallow then acc else (Kontinue.Delimit label h e false, mt) :: acc
        let resume : Value m := .Partial (.Resume acc iEnv) []
        let k := (Kontinue.CallWith arg e, mt) :: (Kontinue.CallWith resume e, mt) :: rest
        .ok (.V h, e, k)
      else
        doPerform label arg iEnv rest ((Kontinue.Delimit l h e shallow, mt) :: acc)
  | (kont, mt) :: rest => doPerform label arg iEnv rest ((kont, mt) :: acc)
  | [] => .error (.UnhandledEffect label arg)

/-- Perform an effect (`state.perform`). -/
partial def perform (label : String) (arg : Value m) (iEnv : Env m) (k : Stack m) : Return m :=
  doPerform label arg iEnv k []

/-- Install a deep handler and run the guarded computation (`state.deep`):
push `Delimit(label, handler, env, false)`, then `call exec unit`. -/
partial def deep [BEq m] (label : String) (handler : Value m) (exec : Value m) (ann : m)
    (env : Env m) (k : Stack m) : Return m :=
  call exec unit ann env ((Kontinue.Delimit label handler env false, ann) :: k)

end

/-! ## Step loop & drivers (state.gleam:76, expression.gleam) -/

/-- Lift an `eval`/`apply` result into the next machine outcome (`state.try`). -/
def ofEvalReturn : EvalReturn m → Next m
  | .ok (c, e, k) => .Loop c e k
  | .error info => .Break (.error info)

/-- One machine step (`state.gleam:76`). -/
def step [BEq m] (c : Control m) (env : Env m) (k : Stack m) : Next m :=
  match c, k with
  | .E exp, k => ofEvalReturn (eval exp env k)
  | .V value, [] => .Break (.ok value)
  | .V value, (kont, ann) :: rest => ofEvalReturn (apply value env kont ann rest)

/-- Drive the machine to a break (`expression.gleam:18`). -/
partial def loop [BEq m] : Next m → Except (Debug m) (Value m)
  | .Loop c e k => loop (step c e k)
  | .Break result => result

/-- Execute an expression within a scope (`expression.gleam:26`). The builtin
dict is gone (decision #1), so `builtin.default(scope)` is just `scope`. -/
def execute [BEq m] (exp : Tree.Node m) (scope : Scope m) : Except (Debug m) (Value m) :=
  loop (step (.E exp) scope [])

/-- Resume the loop with a value from a previous break (`expression.gleam:10`). -/
def resume [BEq m] (value : Value m) (env : Env m) (k : Stack m) : Except (Debug m) (Value m) :=
  loop (step (.V value) env k)

/-! ## Sanity checks (Milestone 2) -/

open Eyg.Ir.Tree in
section
-- `(\x. x) 1` ⟶ 1
#guard (execute (Tree.apply (Tree.lambda "x" (Tree.variable_ "x")) (Tree.integer 1)) []).toOption
  == some (.Integer 1)
-- `let x = 2 in x` ⟶ 2
#guard (execute (Tree.let_ "x" (Tree.integer 2) (Tree.variable_ "x")) []).toOption
  == some (.Integer 2)
-- currying: `((\x.\y. x) 1) 2` ⟶ 1
#guard (execute (Tree.apply
    (Tree.apply (Tree.lambda "x" (Tree.lambda "y" (Tree.variable_ "x"))) (Tree.integer 1))
    (Tree.integer 2)) []).toOption == some (.Integer 1)
-- unbound variable ⟶ break (UndefinedVariable)
#guard (execute (Tree.variable_ "z") []).toOption == none

/-! ### Structured values (Milestone 3) -/

-- record select: `{a:1, b:2}.b` ⟶ 2
#guard (execute (Tree.get (Tree.record [("a", Tree.integer 1), ("b", Tree.integer 2)]) "b")
  []).toOption == some (.Integer 2)
-- select missing field ⟶ break
#guard (execute (Tree.get (Tree.record [("a", Tree.integer 1)]) "z") []).toOption == none
-- overwrite existing field: `{a:1}` with `a:9` ⟶ {a:9}
#guard (execute (Tree.apply (Tree.apply (Tree.overwrite "a") (Tree.integer 9))
  (Tree.record [("a", Tree.integer 1)])) []).toOption == some (mkRecord [("a", .Integer 9)])
-- overwrite missing field ⟶ break (MissingField)
#guard (execute (Tree.apply (Tree.apply (Tree.overwrite "z") (Tree.integer 9))
  (Tree.record [("a", Tree.integer 1)])) []).toOption == none
-- list cons: `[1, 2]` ⟶ LinkedList [1, 2]
#guard (execute (Tree.list [Tree.integer 1, Tree.integer 2]) []).toOption
  == some (.LinkedList [.Integer 1, .Integer 2])
-- variant + match: `match Some(1) { Some -> x | _ -> 0 }` style ⟶ 1
#guard (execute
  (Tree.match_ (Tree.tagged "Some" (Tree.integer 1))
    [("Some", Tree.lambda "x" (Tree.variable_ "x"))]) []).toOption == some (.Integer 1)
-- match falls through to the otherwise branch
#guard (execute
  (Tree.match_ (Tree.tagged "None" (Tree.integer 7))
    [("Some", Tree.lambda "x" (Tree.variable_ "x"))]) []).toOption == none

/-! ### Builtins (Milestone 4) -/

-- int_add: 2 + 3 ⟶ 5
#guard (execute (Tree.add (Tree.integer 2) (Tree.integer 3)) []).toOption == some (.Integer 5)
-- partial builtin: `int_add(2)` stays Partial (under-applied)
#guard (execute (Tree.apply (Tree.builtin "int_add") (Tree.integer 2)) []).toOption
  == some (.Partial (.Builtin "int_add") [.Integer 2])
-- overflow: 2^53 + 1 ⟶ Unrepresentable break
#guard (execute (Tree.add (Tree.integer 9007199254740991) (Tree.integer 1)) []).toOption == none
-- int_divide by zero ⟶ Error(unit)
#guard (execute (Tree.apply (Tree.apply (Tree.builtin "int_divide") (Tree.integer 7))
  (Tree.integer 0)) []).toOption == some (error unit)
-- int_to_string
#guard (execute (Tree.apply (Tree.builtin "int_to_string") (Tree.integer (-42))) []).toOption
  == some (.String "-42")
-- string_append
#guard (execute (Tree.apply (Tree.apply (Tree.builtin "string_append") (Tree.string "ab"))
  (Tree.string "cd")) []).toOption == some (.String "abcd")
-- equal
#guard (execute (Tree.apply (Tree.apply (Tree.builtin "equal") (Tree.integer 1))
  (Tree.integer 1)) []).toOption == some true'
-- list_fold sums [1,2,3] with int_add, seed 0 ⟶ 6
#guard (execute (Tree.call (Tree.builtin "list_fold")
  [Tree.list [Tree.integer 1, Tree.integer 2, Tree.integer 3], Tree.integer 0,
   Tree.builtin "int_add"]) []).toOption == some (.Integer 6)
-- fix-based recursion: factorial 4 ⟶ 24
-- fix(\self. \n. match int_compare(n, 0) { Eq -> 1 | _ -> n * self(n-1) })
private def fact : Tree.Node Unit :=
  let selfNMinus1 := Tree.apply (Tree.variable_ "self")
    (Tree.subtract (Tree.variable_ "n") (Tree.integer 1))
  let body := Tree.lambda "self" (Tree.lambda "n"
    (Tree.match_ (Tree.apply (Tree.apply (Tree.builtin "int_compare") (Tree.variable_ "n"))
        (Tree.integer 0))
      [("Eq", Tree.lambda "_" (Tree.integer 1)),
       ("Lt", Tree.lambda "_" (Tree.multiply (Tree.variable_ "n") selfNMinus1)),
       ("Gt", Tree.lambda "_" (Tree.multiply (Tree.variable_ "n") selfNMinus1))]))
  Tree.apply (Tree.apply (Tree.builtin "fix") body) (Tree.integer 4)
#guard (execute fact []).toOption == some (.Integer 24)

/-! ### Algebraic effects (Milestone 5) -/

-- deep handler that ignores `resume` and returns the effect payload:
-- handle "Eff" (\p.\r. p) (\_. perform "Eff" 1)  ⟶ 1
private def abortHandler : Tree.Node Unit :=
  let handler := Tree.lambda "p" (Tree.lambda "r" (Tree.variable_ "p"))
  let exec := Tree.lambda "_" (Tree.apply (Tree.perform "Eff") (Tree.integer 1))
  Tree.apply (Tree.apply (Tree.handle "Eff") handler) exec
#guard (execute abortHandler []).toOption == some (.Integer 1)

-- deep handler that resumes the computation:
-- handle "Get" (\p.\resume. resume 5) (\_. let x = perform "Get" unit in x + 10)  ⟶ 15
private def resumeHandler : Tree.Node Unit :=
  let handler := Tree.lambda "p" (Tree.lambda "resume"
    (Tree.apply (Tree.variable_ "resume") (Tree.integer 5)))
  let exec := Tree.lambda "_"
    (Tree.let_ "x" (Tree.apply (Tree.perform "Get") Tree.unit)
      (Tree.add (Tree.variable_ "x") (Tree.integer 10)))
  Tree.apply (Tree.apply (Tree.handle "Get") handler) exec
#guard (execute resumeHandler []).toOption == some (.Integer 15)

-- unhandled effect ⟶ break (UnhandledEffect)
#guard (execute (Tree.apply (Tree.perform "Boom") (Tree.integer 1)) []).toOption == none
end

end Eyg.Interpreter
