import Eyg.Interpreter.Cast
import Eyg.Ir.Tree

/-!
# EYG builtins (pure subset)

Mirrors the value-returning builtins of
`packages/gleam_interpreter/src/eyg/interpreter/builtin.gleam`.

`run id args` computes the result `Value` (or a `Reason` failure) for the 26
builtins that do **not** touch the machine stack. The 4 stack-coupled builtins
— `fix`, `fixed`, `list_fold`, `binary_fold` — push continuation frames and call
back into `call`, so they live in `State.callBuiltin` (mutual with `call`)
instead. `builtinArity` gives every builtin's arity for the under/over-applied
`Partial` accumulation in `callBuiltin`.

## Cross-target quirks deliberately reproduced (per the Gleam comments)

- `string_split_once` with an empty pattern yields `#("", s)` (JS behaviour),
  not `Error` (`builtin.gleam:167`).
- `string_replace` with an empty `from` wraps `to` around every character and at
  both ends (JS behaviour), `builtin.gleam:191`. (We split on Unicode scalar
  values, not grapheme clusters — see the plan's watch-list.)
- `int_parse` / `int_add` / … flag `Unrepresentable` when a well-formed result
  leaves the JS safe-integer range (`Integer.isSafe`).
-/

namespace Eyg.Interpreter.Builtin

open Eyg.Interpreter
open Eyg.Ir

/-- Arity of each builtin (`Arity1`/`Arity2`/`Arity3` in `builtin.gleam`).
`none` means the identifier is not a builtin. -/
def builtinArity : String → Option Nat
  | "equal" => some 2 | "fix" => some 1 | "fixed" => some 2 | "never" => some 1
  | "int_compare" => some 2 | "int_add" => some 2 | "int_subtract" => some 2
  | "int_multiply" => some 2 | "int_divide" => some 2 | "int_absolute" => some 1
  | "int_parse" => some 1 | "int_to_string" => some 1
  | "string_append" => some 2 | "string_split" => some 2
  | "string_split_once" => some 2 | "string_replace" => some 3
  | "string_uppercase" => some 1 | "string_lowercase" => some 1
  | "string_starts_with" => some 2 | "string_ends_with" => some 2
  | "string_length" => some 1 | "string_to_binary" => some 1
  | "string_from_binary" => some 1
  | "binary_from_integers" => some 1 | "binary_size" => some 1
  | "binary_concat" => some 2 | "binary_compare" => some 2 | "binary_fold" => some 3
  | "list_pop" => some 1 | "list_fold" => some 3
  | _ => none

/-- Tag an `Ordering` as the EYG `Lt`/`Eq`/`Gt` variant (matches `order.Lt`…). -/
def ordTag : Ordering → Value m
  | .lt => .Tagged "Lt" unit
  | .eq => .Tagged "Eq" unit
  | .gt => .Tagged "Gt" unit

/-- Lexicographic byte comparison, shorter-is-prefix-is-less (`bit_array.compare`). -/
def cmpBytes : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | a :: as, b :: bs => match compare a b with
      | .eq => cmpBytes as bs
      | o => o

/-- Is `c` a combining mark / grapheme-extender (a non-spacing scalar that
attaches to the preceding base character)? Covers the ranges the spec fixtures
exercise — enough to count grapheme clusters like Gleam's `string.length`. -/
private def isCombining (c : Char) : Bool :=
  let n := c.toNat
  (0x0300 ≤ n ∧ n ≤ 0x036F) || (0x1AB0 ≤ n ∧ n ≤ 0x1AFF) ||
  (0x1DC0 ≤ n ∧ n ≤ 0x1DFF) || (0x20D0 ≤ n ∧ n ≤ 0x20FF) ||
  (0xFE20 ≤ n ∧ n ≤ 0xFE2F) || n == 0x200D

/-- Split a string into grapheme clusters (base char + trailing combining marks),
approximating Gleam `string.to_graphemes`. Used by `string_split` on an empty
pattern and by `string_length`. -/
def graphemes (s : String) : List String := Id.run do
  let mut acc : List String := []  -- built in reverse
  for c in s.toList do
    if isCombining c then
      match acc with
      | g :: rest => acc := (g ++ c.toString) :: rest
      | [] => acc := [c.toString]
    else
      acc := c.toString :: acc
  return acc.reverse

/-- `s` starts with `p` (by Unicode scalar prefix). -/
private def strStartsWith (s p : String) : Bool := s.take p.length == p
/-- `s` ends with `p`. -/
private def strEndsWith (s p : String) : Bool :=
  p.length ≤ s.length && s.drop (s.length - p.length) == p

/-- Run a non-stack builtin by name. Precondition (from `callBuiltin`): `args`
has exactly `builtinArity id` elements, so the arg-shape matches. -/
def run [BEq m] (id : String) (args : List (Value m)) : Except (Reason m) (Value m) :=
  match id, args with
  | "equal", [a, b] => .ok (bool (a == b))
  | "never", [a] => .error (.IncorrectTerm "Never" a)
  -- integers
  | "int_compare", [a, b] => do
      let x ← Cast.asInteger a; let y ← Cast.asInteger b
      .ok (ordTag (compare x y))
  | "int_add", [a, b] => do
      let x ← Cast.asInteger a; let y ← Cast.asInteger b
      let r := x + y
      if Integer.isSafe r then .ok (.Integer r) else .error (.Unrepresentable "int_add" [a, b])
  | "int_subtract", [a, b] => do
      let x ← Cast.asInteger a; let y ← Cast.asInteger b
      let r := x - y
      if Integer.isSafe r then .ok (.Integer r) else .error (.Unrepresentable "int_subtract" [a, b])
  | "int_multiply", [a, b] => do
      let x ← Cast.asInteger a; let y ← Cast.asInteger b
      let r := x * y
      if Integer.isSafe r then .ok (.Integer r) else .error (.Unrepresentable "int_multiply" [a, b])
  | "int_divide", [a, b] => do
      let x ← Cast.asInteger a; let y ← Cast.asInteger b
      .ok (if y == 0 then error unit else ok (.Integer (x / y)))
  | "int_absolute", [a] => do
      let x ← Cast.asInteger a
      .ok (.Integer (Int.ofNat x.natAbs))
  | "int_parse", [a] => do
      let s ← Cast.asString a
      match s.toInt? with
      | none => .ok (error unit)
      | some i =>
          if Integer.isSafe i then .ok (ok (.Integer i))
          else .error (.Unrepresentable "int_parse" [a])
  | "int_to_string", [a] => do
      let x ← Cast.asInteger a
      .ok (.String (toString x))
  -- strings
  | "string_append", [a, b] => do
      let x ← Cast.asString a; let y ← Cast.asString b
      .ok (.String (x ++ y))
  | "string_split", [a, b] => do
      let s ← Cast.asString a; let pat ← Cast.asString b
      -- Gleam `string.split(s, "")` yields the grapheme clusters of `s`.
      let parts := if pat == "" then graphemes s else s.splitOn pat
      match parts with
      | [] => .ok (mkRecord [("head", .String ""), ("tail", .LinkedList [])])
      | first :: rest =>
          .ok (mkRecord [("head", .String first), ("tail", .LinkedList (rest.map (.String ·)))])
  | "string_split_once", [a, b] => do
      let s ← Cast.asString a; let pat ← Cast.asString b
      if pat == "" then
        .ok (ok (mkRecord [("pre", .String ""), ("post", .String s)]))
      else match s.splitOn pat with
        | first :: rest@(_ :: _) =>
            .ok (ok (mkRecord [("pre", .String first),
                               ("post", .String (String.intercalate pat rest))]))
        | _ => .ok (error unit)
  | "string_replace", [a, b, c] => do
      let inp ← Cast.asString a; let frm ← Cast.asString b; let to ← Cast.asString c
      let replaced :=
        if frm == "" then
          if inp == "" then to
          else to ++ String.intercalate to (inp.toList.map (·.toString)) ++ to
        else inp.replace frm to
      .ok (.String replaced)
  | "string_uppercase", [a] => do
      let s ← Cast.asString a; .ok (.String (s.map Char.toUpper))
  | "string_lowercase", [a] => do
      let s ← Cast.asString a; .ok (.String (s.map Char.toLower))
  | "string_starts_with", [a, b] => do
      let s ← Cast.asString a; let p ← Cast.asString b; .ok (bool (strStartsWith s p))
  | "string_ends_with", [a, b] => do
      let s ← Cast.asString a; let p ← Cast.asString b; .ok (bool (strEndsWith s p))
  | "string_length", [a] => do
      let s ← Cast.asString a; .ok (.Integer (Int.ofNat (graphemes s).length))
  | "string_to_binary", [a] => do
      let s ← Cast.asString a; .ok (.Binary s.toUTF8)
  | "string_from_binary", [a] => do
      let b ← Cast.asBinary a
      match String.fromUTF8? b with
      | some str => .ok (ok (.String str))
      | none => .ok (error unit)
  -- binaries
  | "binary_from_integers", [a] => do
      let elements ← Cast.asList a
      let ints ← elements.mapM Cast.asInteger
      -- Gleam builds `<<i, …:bits>>`, i.e. the low 8 bits of each `i`
      -- (two's-complement for negatives: `-1 → 255`). `Int % 256` is already
      -- non-negative in Lean, so this matches without an `Int.toNat` clamp.
      .ok (.Binary (ByteArray.mk (ints.map (fun i => UInt8.ofNat (i % 256).toNat)).toArray))
  | "binary_size", [a] => do
      let b ← Cast.asBinary a; .ok (.Integer (Int.ofNat b.size))
  | "binary_concat", [a, b] => do
      let x ← Cast.asBinary a; let y ← Cast.asBinary b; .ok (.Binary (x ++ y))
  | "binary_compare", [a, b] => do
      let x ← Cast.asBinary a; let y ← Cast.asBinary b
      .ok (ordTag (cmpBytes x.toList y.toList))
  -- lists
  | "list_pop", [a] => do
      let elements ← Cast.asList a
      match elements with
      | [] => .ok (error unit)
      | head :: tail => .ok (ok (mkRecord [("head", head), ("tail", .LinkedList tail)]))
  | _, _ => .error (.UndefinedBuiltin id)

/-! ## Smoke checks -/

-- `binary_from_integers` takes the low 8 bits of each element (Gleam `<<i>>`):
-- `-1 → 255`, `256 → 0`, `300 → 44`.
#guard (run (m := Unit) "binary_from_integers"
    [.LinkedList [.Integer (-1), .Integer 256, .Integer 300]]).toOption
  == some (.Binary (ByteArray.mk #[255, 0, 44]))

end Eyg.Interpreter.Builtin
