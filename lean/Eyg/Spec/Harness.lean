import Eyg.Interpreter.State
import Lean.Data.Json

/-!
# Spec evaluation harness

A Lean port of `packages/gleam_interpreter/test/eyg/interpreter_test.gleam`.

Reads the three `spec/evaluation/*.json` suites, decodes each fixture
(dag-json `source` → `Tree.Node Unit`, expected `value`/`break`, and any
`effects`), runs `execute`, folds the effect replies through `resume`, and
compares the final result to the expectation. `main` exits non-zero unless every
fixture passes (the project's real contract).

The dag-json node encoding (key `"0"`) mirrors `eyg/ir/dag_json.gleam`; bytes use
the IPLD form `{"/": {"bytes": "<base64>"}}` and CID links `{"/": "<cid>"}`.
-/

namespace Eyg.Spec

open Lean (Json)
open Eyg.Interpreter
open Eyg.Ir

/-! ## base64 (dag-json bytes) -/

/-- Map a base64 / base64url character to its 6-bit value; `none` for padding. -/
def b64val (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c == '+' ∨ c == '-' then some 62
  else if c == '/' ∨ c == '_' then some 63
  else none

/-- Decode a (possibly unpadded) base64 string to bytes; non-alphabet chars
(e.g. `=`) are skipped. -/
def decodeB64 (s : String) : ByteArray := Id.run do
  let mut acc : Nat := 0
  let mut nbits : Nat := 0
  let mut out := ByteArray.empty
  for c in s.toList do
    if let some v := b64val c then
      acc := (acc <<< 6) ||| v
      nbits := nbits + 6
      if nbits ≥ 8 then
        nbits := nbits - 8
        out := out.push (((acc >>> nbits) &&& 0xFF).toUInt8)
  return out

/-! ## JSON helpers -/

private def field (j : Json) (k : String) : Except String Json := j.getObjVal? k
private def strField (j : Json) (k : String) : Except String String := do
  (← j.getObjVal? k).getStr?

/-- Decode a dag-json bytes node `{"/": {"bytes": "<base64>"}}`. -/
def decodeBytes (j : Json) : Except String ByteArray := do
  let inner ← field j "/"
  let b64 ← strField inner "bytes"
  .ok (decodeB64 b64)

/-- Decode a dag-json CID link `{"/": "<cid>"}` to its string form. -/
def decodeCid (j : Json) : Except String Tree.Cid := do
  (← field j "/").getStr?

/-! ## IR decoder (dag_json.gleam) -/

/-- Decode a dag-json source node into `Tree.Node Unit`. -/
partial def decodeNode (j : Json) : Except String (Tree.Node Unit) := do
  let key ← strField j "0"
  let lbl : Except String String := strField j "l"
  let n (e : Tree.Expr Unit) : Except String (Tree.Node Unit) := .ok ⟨e, ()⟩
  match key with
  | "v" => n (.Variable (← lbl))
  | "f" => n (.Lambda (← lbl) (← decodeNode (← field j "b")))
  | "a" => n (.Apply (← decodeNode (← field j "f")) (← decodeNode (← field j "a")))
  | "l" => n (.Let (← lbl) (← decodeNode (← field j "v")) (← decodeNode (← field j "t")))
  | "x" => n (.Binary (← decodeBytes (← field j "v")))
  | "i" =>
      let v ← (← field j "v").getInt?
      if Integer.isSafe v then n (.Integer v) else .error "integer not exactly representable"
  | "s" => n (.String (← (← field j "v").getStr?))
  | "ta" => n .Tail
  | "c" => n .Cons
  | "z" => n .Vacant
  | "u" => n .Empty
  | "e" => n (.Extend (← lbl))
  | "g" => n (.Select (← lbl))
  | "o" => n (.Overwrite (← lbl))
  | "t" => n (.Tag (← lbl))
  | "m" => n (.Case (← lbl))
  | "n" => n .NoCases
  | "p" => n (.Perform (← lbl))
  | "h" => n (.Handle (← lbl))
  | "b" => n (.Builtin (← lbl))
  | "#" => n (.ContentReference (← decodeCid (← field j "l")))
  | "@" =>
      n (.ReleaseReference (← strField j "p") (← (← field j "r").getInt?)
          (← decodeCid (← field j "l")))
  | "." => n (.RelativeReference (← strField j "i"))
  | other => .error s!"unknown node key {other}"

/-! ## Value decoder (interpreter_test.gleam:31) -/

/-- Decode an expected runtime value. -/
partial def decodeValue (j : Json) : Except String (Value Unit) := do
  if let .ok b := j.getObjVal? "binary" then
    .ok (.Binary (← decodeBytes b))
  else if let .ok i := j.getObjVal? "integer" then
    .ok (.Integer (← i.getInt?))
  else if let .ok s := j.getObjVal? "string" then
    .ok (.String (← s.getStr?))
  else if let .ok l := j.getObjVal? "list" then
    let arr ← l.getArr?
    .ok (.LinkedList (← arr.toList.mapM decodeValue))
  else if let .ok r := j.getObjVal? "record" then
    match r with
    | .obj m =>
        let mut fields : List (String × Value Unit) := []
        for (k, vj) in m.toList do
          fields := fields ++ [(k, ← decodeValue vj)]
        .ok (mkRecord fields)
    | _ => .error "record is not an object"
  else if let .ok t := j.getObjVal? "tagged" then
    .ok (.Tagged (← strField t "label") (← decodeValue (← field t "value")))
  else
    .error "unknown value shape"

/-! ## Fixture, effect & expectation decoders -/

/-- A spec fixture (`interpreter_test.gleam` `Fixture`). -/
structure Fixture where
  name : String
  source : Tree.Node Unit
  effects : List (String × Value Unit × Value Unit)  -- (label, lift, reply)
  expected : Except (Reason Unit) (Value Unit)

def decodeEffect (j : Json) : Except String (String × Value Unit × Value Unit) := do
  .ok (← strField j "label", ← decodeValue (← field j "lift"), ← decodeValue (← field j "reply"))

/-- Decode the top-level `value`/`break` expectation. -/
def decodeExpectation (j : Json) : Except String (Except (Reason Unit) (Value Unit)) := do
  if let .ok v := j.getObjVal? "value" then
    .ok (.ok (← decodeValue v))
  else if let .ok b := j.getObjVal? "break" then
    if let .ok x := b.getObjVal? "UndefinedVariable" then .ok (.error (.UndefinedVariable (← x.getStr?)))
    else if let .ok x := b.getObjVal? "UndefinedBuiltin" then .ok (.error (.UndefinedBuiltin (← x.getStr?)))
    else if let .ok _ := b.getObjVal? "NotImplemented" then .ok (.error .Vacant)
    else .error "unknown break reason"
  else
    .error "fixture has neither value nor break"

def decodeFixture (j : Json) : Except String Fixture := do
  let name ← strField j "name"
  let source ← decodeNode (← field j "source")
  let effects ← match j.getObjVal? "effects" with
    | .ok e => do let arr ← e.getArr?; arr.toList.mapM decodeEffect
    | .error _ => pure []
  let expected ← decodeExpectation j
  .ok ⟨name, source, effects, expected⟩

/-! ## Runner -/

/-- Run a fixture: execute, fold effect replies through `resume`, compare. -/
def runFixture (fx : Fixture) : Bool :=
  let final := fx.effects.foldl (init := execute fx.source []) fun ret (label, lift, reply) =>
    match ret with
    | .error (.UnhandledEffect l v, _, env, k) =>
        if l == label && v == lift then resume reply env k else ret
    | _ => ret
  match final, fx.expected with
  | .ok got, .ok exp => got == exp
  | .error (reason, _, _, _), .error exp => reason == exp
  | _, _ => false

/-- Decode + run one suite file, returning `(passed, total, failureNames)`. -/
def runSuiteJson (file : String) (j : Json) : Nat × Nat × List String := Id.run do
  let mut passed := 0
  let mut total := 0
  let mut fails : List String := []
  match j.getArr? with
  | .error e => return (0, 1, [s!"{file}: not a JSON array: {e}"])
  | .ok arr =>
    for fxJson in arr do
      total := total + 1
      match decodeFixture fxJson with
      | .error e =>
          let nm := (strField fxJson "name").toOption.getD "?"
          fails := fails ++ [s!"{file}: {nm}: decode error: {e}"]
      | .ok fx =>
          if runFixture fx then passed := passed + 1
          else fails := fails ++ [s!"{file}: {fx.name}"]
  return (passed, total, fails)

def suiteFiles : List String := ["core_suite.json", "builtins_suite.json", "effects_suite.json"]

def run : IO UInt32 := do
  let dir := "../spec/evaluation/"
  let mut passed := 0
  let mut total := 0
  let mut fails : List String := []
  for file in suiteFiles do
    let contents ← IO.FS.readFile (dir ++ file)
    match Json.parse contents with
    | .error e => fails := fails ++ [s!"{file}: JSON parse error: {e}"]; total := total + 1
    | .ok j =>
        let (p, t, fs) := runSuiteJson file j
        passed := passed + p; total := total + t; fails := fails ++ fs
  IO.println s!"spec evaluation: {passed}/{total} fixtures passed"
  for f in fails do IO.println s!"  FAIL {f}"
  if passed == total ∧ total > 0 then pure 0 else pure 1

end Eyg.Spec

/-- Executable entry point (`lake exe spec`). -/
def main : IO UInt32 := Eyg.Spec.run
