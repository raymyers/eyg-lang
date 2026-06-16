import Eyg.Interpreter.Value

/-!
# EYG failure reasons

Mirrors `packages/gleam_interpreter/src/eyg/interpreter/break.gleam`.

`Reason(m, c)` becomes `Reason m` (the context type parameter `c` is pinned to
the machine's `Context m` and not surfaced separately here). `Unrepresentable`
"halts the run with a resumable state" — it carries the builtin and its args.
-/

namespace Eyg.Interpreter

open Eyg.Ir

/-- Failure reasons produced by the machine, mirroring `break.Reason`. -/
inductive Reason (m : Type) where
  | NotAFunction (term : Value m)
  | UndefinedVariable (label : String)
  | UndefinedBuiltin (identifier : String)
  | UndefinedReference (cid : Tree.Cid)
  | UndefinedRelease (package : String) (release : Int) (module_ : Tree.Cid)
  | UndefinedRelative (location : String)
  | Vacant
  | NoMatch (term : Value m)
  | UnhandledEffect (label : String) (lift : Value m)
  | IncorrectTerm (expected : String) (got : Value m)
  | MissingField (label : String)
  /-- Unrepresentable on the runtime (e.g. integer outside the JS safe range);
  halts with a resumable state, carrying the builtin id and its arguments. -/
  | Unrepresentable (builtin : String) (args : List (Value m))
  deriving Repr, BEq, Inhabited

end Eyg.Interpreter
