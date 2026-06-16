import Eyg.Interpreter.Break

/-!
# Value coercions

Mirrors `packages/gleam_interpreter/src/eyg/interpreter/cast.gleam`.

Each `asX` projects a `Value` into the underlying datum, failing with
`IncorrectTerm(expected, got)` (or `MissingField`) on a mismatch — the same
errors the Gleam casts raise. These are pure (no machine state) and are used by
`call` (records/variants/lists) and the builtins.
-/

namespace Eyg.Interpreter.Cast

open Eyg.Interpreter

/-- Project an `Integer` value (`cast.as_integer`). -/
def asInteger : Value m → Except (Reason m) Int
  | .Integer v => .ok v
  | other => .error (.IncorrectTerm "Integer" other)

/-- Project a `String` value (`cast.as_string`). -/
def asString : Value m → Except (Reason m) String
  | .String v => .ok v
  | other => .error (.IncorrectTerm "String" other)

/-- Project a `Binary` value (`cast.as_binary`). -/
def asBinary : Value m → Except (Reason m) ByteArray
  | .Binary v => .ok v
  | other => .error (.IncorrectTerm "Binary" other)

/-- Project a `LinkedList` value (`cast.as_list`). -/
def asList : Value m → Except (Reason m) (List (Value m))
  | .LinkedList es => .ok es
  | other => .error (.IncorrectTerm "List" other)

/-- Project a `Record` value's fields (`cast.as_record`). -/
def asRecord : Value m → Except (Reason m) (List (String × Value m))
  | .Record fs => .ok fs
  | other => .error (.IncorrectTerm "Record" other)

/-- Project a `Tagged` value (`cast.as_tagged`). -/
def asTagged : Value m → Except (Reason m) (String × Value m)
  | .Tagged label inner => .ok (label, inner)
  | other => .error (.IncorrectTerm "Tagged" other)

end Eyg.Interpreter.Cast
