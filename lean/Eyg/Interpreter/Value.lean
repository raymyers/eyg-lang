import Eyg.Ir.Tree

/-!
# EYG runtime values & CEK machine types

Mirrors `packages/gleam_interpreter/src/eyg/interpreter/value.gleam` (the
`Value` / `Switch` types) and the machine-state types from
`.../state.gleam` (`Kontinue`, `Stack`, `Scope`, `Env`, `Context`).

## Deviations from the Gleam shape (see the plan's "Key design decisions")

1. **Builtins dispatched by name (decision #1).** Gleam's `Env(scope, builtins)`
   stows a `Dict(String, Builtin)` of *functions* in the environment. A function
   whose codomain mentions `Value` cannot live inside the `Value` inductive in
   Lean (non-strict-positivity), so the builtin dict is dropped entirely and
   `Env` collapses to `Scope = List (String × Value m)`. Builtins are resolved by
   their identifier string in `State.lean` (`ir.Builtin id` is valid iff `id` is
   a known builtin). `Switch.Builtin id` still carries the identifier.

2. **`Value` is first-order ⇒ `BEq` derives.** With builtins out of the env,
   `Value`/`Switch`/`Kontinue` form one `mutual inductive` block with no function
   fields. The harness compares result values structurally, which needs only a
   `Bool` equality — `deriving BEq` suffices and *does* derive through the `List`
   occurrences here. (`DecidableEq` deriving cannot see through `List`/`Prod`
   nesting, so the Prop-level instance is deferred; it is not needed to run the
   suites. Tracked as a follow-up for the semantics proofs.)

3. **Records are kept canonical (decision #3).** Gleam `Record` is a `Dict`, so
   `{a:1,b:2} == {b:2,a:1}`. Here `Record` holds `List (String × Value m)`
   maintained **sorted by key with unique keys** (`recordInsert`/`mkRecord`), so
   the derived structural `BEq` is order-insensitive, matching `should.equal` on
   Gleam dicts. Every record-building site must go through these helpers.

4. **`Stack` is `List (Kontinue m × m)`.** Gleam's `Stack(k, meta, rest) | Empty`
   is exactly a cons-list of frame+metadata pairs (`Empty = []`). The effect
   machinery's `do_perform` accumulator and `move` already treat it as a list,
   and `Context`/`Resume` carry that same list — so a `List` alias matches the
   source and keeps `Stack` out of the mutual block.
-/

namespace Eyg.Interpreter

open Eyg.Ir

/-- `ByteArray` lacks a core `Repr`; provide one (via its byte list). Scoped. -/
local instance : Repr ByteArray where
  reprPrec b _ := repr b.toList

mutual

/-- Runtime values, mirroring `Value(m, context)` in `value.gleam`.

`Record.fields` is kept sorted-by-key/unique (decision #3). `Closure.env` and
the env fields on `Kontinue`/`Switch.Resume` are `Scope`s (decision #1). -/
inductive Value (m : Type) where
  | Binary (value : ByteArray)
  | Integer (value : Int)
  | String (value : String)
  | LinkedList (elements : List (Value m))
  | Record (fields : List (String × Value m))
  | Tagged (label : String) (value : Value m)
  | Closure (param : String) (body : Tree.Node m) (env : List (String × Value m))
  | Partial (switch : Switch m) (applied : List (Value m))
  deriving Repr, BEq, Inhabited

/-- Partially-applied primitive operators, mirroring `Switch(context)`.

`Resume` carries the captured resumption context `#(List(#(Kontinue, m)), Env)`
(state.gleam `Context(m)`): the popped stack frames plus the interpreter scope
in effect when the effect was performed. -/
inductive Switch (m : Type) where
  | Cons
  | Extend (label : String)
  | Overwrite (label : String)
  | Select (label : String)
  | Tag (label : String)
  | Match (label : String)
  | NoCases
  | Perform (label : String)
  | Handle (label : String)
  | Resume (frames : List (Kontinue m × m)) (env : List (String × Value m))
  | Builtin (identifier : String)
  deriving Repr, BEq, Inhabited

/-- Continuation frames, mirroring `Kontinue(m)` in `state.gleam:63`. -/
inductive Kontinue (m : Type) where
  | Arg (arg : Tree.Node m) (env : List (String × Value m))
  | Apply (func : Value m) (env : List (String × Value m))
  | Assign (label : String) (then_ : Tree.Node m) (env : List (String × Value m))
  | CallWith (arg : Value m) (env : List (String × Value m))
  | Delimit (label : String) (handler : Value m) (env : List (String × Value m)) (shallow : Bool)
  /-- Pass-through marker pushed on every closure call; debug-only. -/
  | Trace (arg : Value m)
  deriving Repr, BEq, Inhabited

end

/-! ## Machine-state aliases (state.gleam:9-33) -/

/-- Environment scope: builtins live elsewhere (decision #1), so `Env = Scope`. -/
abbrev Scope (m : Type) := List (String × Value m)

/-- `Env` is just the scope here (no builtin dict). -/
abbrev Env (m : Type) := Scope m

/-- The control stack: `Empty | Stack(k, meta, rest)` as a cons-list. -/
abbrev Stack (m : Type) := List (Kontinue m × m)

/-- Captured resumption context inside `Resume`: popped frames + scope. -/
abbrev Context (m : Type) := Stack m × Scope m

/-! ## Value constructors / helpers (value.gleam:34-71)

`tag`, `true`, `false`, `bool`, `ok`, `error`, `some`, `none` follow Lean
reserved-token renames (`true'`/`false'`). -/

/-- Insert into a canonical (sorted-by-key, unique) record field list, replacing
any existing entry for `key`. Preserves sortedness when the input is sorted. -/
def recordInsert : List (String × Value m) → String → Value m → List (String × Value m)
  | [], key, value => [(key, value)]
  | (k, v) :: rest, key, value =>
    if key == k then (key, value) :: rest
    else if key < k then (key, value) :: (k, v) :: rest
    else (k, v) :: recordInsert rest key value

/-- Look up a field in a record field list. -/
def recordGet : List (String × Value m) → String → Option (Value m)
  | [], _ => none
  | (k, v) :: rest, key => if key == k then some v else recordGet rest key

/-- Build a canonical `Record` from arbitrary fields (later keys win). -/
def mkRecord (fields : List (String × Value m)) : Value m :=
  .Record (fields.foldl (fun acc (kv : String × Value m) => recordInsert acc kv.1 kv.2) [])

/-- Empty record (`value.unit`). -/
def unit : Value m := .Record []

def tag (label : String) : Value m := .Partial (.Tag label) []
def true' : Value m := .Tagged "True" unit
def false' : Value m := .Tagged "False" unit
def bool : Bool → Value m | true => true' | false => false'
def ok (value : Value m) : Value m := .Tagged "Ok" value
def error (reason : Value m) : Value m := .Tagged "Error" reason
def some' (value : Value m) : Value m := .Tagged "Some" value
def none' : Value m := .Tagged "None" unit

/-! ## Smoke checks (Milestone 1) -/

-- Records compare order-insensitively (decision #3): `{a:1,b:2} == {b:2,a:1}`.
example :
    (mkRecord [("a", .Integer 1), ("b", .Integer 2)] : Value Unit)
      == mkRecord [("b", .Integer 2), ("a", .Integer 1)] := by native_decide

-- Later keys win when building a record.
example :
    (mkRecord [("a", .Integer 1), ("a", .Integer 9)] : Value Unit)
      == mkRecord [("a", .Integer 9)] := by native_decide

-- Distinct values are distinguished.
example : ((.Integer 1 : Value Unit) == .Integer 2) = false := by native_decide

end Eyg.Interpreter
