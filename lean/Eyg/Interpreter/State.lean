import Eyg.Interpreter.Break

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

/-- The identifiers registered in Gleam's `builtin.default` env (`builtin.all`).
An `ir.Builtin id` node is valid iff `id` is in this set. -/
def builtinNames : List String :=
  ["equal", "fix", "fixed", "never",
   "int_compare", "int_add", "int_subtract", "int_multiply", "int_divide",
   "int_absolute", "int_parse", "int_to_string",
   "string_append", "string_split", "string_split_once", "string_replace",
   "string_uppercase", "string_lowercase", "string_starts_with",
   "string_ends_with", "string_length", "string_to_binary", "string_from_binary",
   "binary_from_integers", "binary_size", "binary_concat", "binary_compare",
   "binary_fold", "list_pop", "list_fold"]

def isBuiltin (id : String) : Bool := builtinNames.contains id

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

/-! ## The machine (state.gleam:91-211) -/

mutual

/-- One expression → next configuration (`state.gleam:91`). -/
partial def eval (exp : Tree.Node m) (env : Env m) (k : Stack m) : EvalReturn m :=
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
partial def apply (val : Value m) (env : Env m) (k : Kontinue m) (ann : m) (rest : Stack m) :
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

Milestone 2: `Closure`, generic `Partial` accumulation, and `NotAFunction`.
The specific `Partial`-switch arms are filled in by later milestones. -/
partial def call (f : Value m) (arg : Value m) (ann : m) (env : Env m) (k : Stack m) : Return m :=
  match f with
  | .Closure param body captured =>
      .ok (.E body, (param, arg) :: captured, (Kontinue.Trace arg, ann) :: k)
  | .Partial switch applied =>
      -- TODO(M3-M5): specific arms (Cons/Extend/Select/Match/Builtin/Perform/…)
      -- go here, before this generic accumulation catch-all.
      .ok (.V (.Partial switch (applied ++ [arg])), env, k)
  | term => .error (.NotAFunction term)

end

/-! ## Step loop & drivers (state.gleam:76, expression.gleam) -/

/-- Lift an `eval`/`apply` result into the next machine outcome (`state.try`). -/
def ofEvalReturn : EvalReturn m → Next m
  | .ok (c, e, k) => .Loop c e k
  | .error info => .Break (.error info)

/-- One machine step (`state.gleam:76`). -/
def step (c : Control m) (env : Env m) (k : Stack m) : Next m :=
  match c, k with
  | .E exp, k => ofEvalReturn (eval exp env k)
  | .V value, [] => .Break (.ok value)
  | .V value, (kont, ann) :: rest => ofEvalReturn (apply value env kont ann rest)

/-- Drive the machine to a break (`expression.gleam:18`). -/
partial def loop : Next m → Except (Debug m) (Value m)
  | .Loop c e k => loop (step c e k)
  | .Break result => result

/-- Execute an expression within a scope (`expression.gleam:26`). The builtin
dict is gone (decision #1), so `builtin.default(scope)` is just `scope`. -/
def execute (exp : Tree.Node m) (scope : Scope m) : Except (Debug m) (Value m) :=
  loop (step (.E exp) scope [])

/-- Resume the loop with a value from a previous break (`expression.gleam:10`). -/
def resume (value : Value m) (env : Env m) (k : Stack m) : Except (Debug m) (Value m) :=
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
end

end Eyg.Interpreter
