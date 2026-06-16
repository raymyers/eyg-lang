import Eyg.Interpreter.State
import Eyg.Ir.Cid
import Eyg.Semantics.FunctionalBigStep
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

/-! ## IR encoder & round-trip (dag_json.to_data_model) -/

/-- Encode bytes as base64 (standard alphabet, no padding); inverse of
`decodeB64`. Used for IR round-trip; canonical CID block bytes come from
`toBlock`/`Json.compress`, not from this encoder. -/
def encodeB64 (bytes : ByteArray) : String := Id.run do
  let tbl := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray
  let mut out := ""
  let mut acc : Nat := 0
  let mut nbits : Nat := 0
  for b in bytes.toList do
    acc := (acc <<< 8) ||| b.toNat
    nbits := nbits + 8
    while nbits ≥ 6 do
      nbits := nbits - 6
      out := out.push tbl[((acc >>> nbits) &&& 0x3F)]!
  if nbits > 0 then
    out := out.push tbl[((acc <<< (6 - nbits)) &&& 0x3F)]!
  return out

/-- Encode an IR node back to the dag-json data model (`dag_json.to_data_model`).
Key order is not canonicalised — `decodeNode` reads fields by name. -/
partial def encodeNode (nd : Tree.Node Unit) : Json :=
  let lbl (x : String) : String × Json := ("l", Json.str x)
  let o := Json.mkObj
  let cidLink (c : Tree.Cid) : Json := Json.mkObj [("/", Json.str c)]
  match nd.expr with
  | .Variable x => o [("0", Json.str "v"), lbl x]
  | .Lambda x b => o [("0", Json.str "f"), lbl x, ("b", encodeNode b)]
  | .Apply f a => o [("0", Json.str "a"), ("f", encodeNode f), ("a", encodeNode a)]
  | .Let x v t => o [("0", Json.str "l"), lbl x, ("v", encodeNode v), ("t", encodeNode t)]
  | .Binary b => o [("0", Json.str "x"),
      ("v", Json.mkObj [("/", Json.mkObj [("bytes", Json.str (encodeB64 b))])])]
  | .Integer i => o [("0", Json.str "i"), ("v", Json.num (.fromInt i))]
  | .String s => o [("0", Json.str "s"), ("v", Json.str s)]
  | .Tail => o [("0", Json.str "ta")]
  | .Cons => o [("0", Json.str "c")]
  | .Vacant => o [("0", Json.str "z")]
  | .Empty => o [("0", Json.str "u")]
  | .Extend x => o [("0", Json.str "e"), lbl x]
  | .Select x => o [("0", Json.str "g"), lbl x]
  | .Overwrite x => o [("0", Json.str "o"), lbl x]
  | .Tag x => o [("0", Json.str "t"), lbl x]
  | .Case x => o [("0", Json.str "m"), lbl x]
  | .NoCases => o [("0", Json.str "n")]
  | .Perform x => o [("0", Json.str "p"), lbl x]
  | .Handle x => o [("0", Json.str "h"), lbl x]
  | .Builtin x => o [("0", Json.str "b"), lbl x]
  | .ContentReference c => o [("0", Json.str "#"), ("l", cidLink c)]
  | .ReleaseReference p r c =>
      o [("0", Json.str "@"), ("p", Json.str p), ("r", Json.num (.fromInt r)), ("l", cidLink c)]
  | .RelativeReference loc => o [("0", Json.str "."), ("i", Json.str loc)]

/-- An `ir_suite.json` fixture: a source node and its expected CIDv1 string. -/
structure IrFixture where
  name : String
  source : Tree.Node Unit
  cid : String

def decodeIrFixture (j : Json) : Except String IrFixture := do
  .ok ⟨← strField j "name", ← decodeNode (← field j "source"), ← strField j "cid"⟩

/-- Canonical dag-json block bytes for a node: compact JSON with sorted keys
(`Json.compress` over the sorted-key object). Mirrors `dag_json.to_block`. -/
def toBlock (nd : Tree.Node Unit) : ByteArray := (encodeNode nd).compress.toUTF8

/-- Check a fixture: structural round-trip and CIDv1-string equality. -/
def runIrFixture (fx : IrFixture) : Bool × Bool :=
  let roundTrip := (decodeNode (encodeNode fx.source)).toOption == some fx.source
  let cidOk := Eyg.Ir.Cid.cidOfBlock (toBlock fx.source) == fx.cid
  (roundTrip, cidOk)

/-- Returns `(roundTripPassed, cidPassed, total, failures)`. -/
def runIrSuiteJson (file : String) (j : Json) : Nat × Nat × Nat × List String := Id.run do
  let mut passed := 0
  let mut cidPassed := 0
  let mut total := 0
  let mut fails : List String := []
  match j.getArr? with
  | .error e => return (0, 0, 1, [s!"{file}: not a JSON array: {e}"])
  | .ok arr =>
    for fxJson in arr do
      total := total + 1
      match decodeIrFixture fxJson with
      | .error e =>
          let nm := (strField fxJson "name").toOption.getD "?"
          fails := fails ++ [s!"{file}: {nm}: decode error: {e}"]
      | .ok fx =>
          let (rt, cid) := runIrFixture fx
          if rt then passed := passed + 1
          else fails := fails ++ [s!"{file}: {fx.name}: round-trip mismatch"]
          if cid then cidPassed := cidPassed + 1
          else fails := fails ++ [s!"{file}: {fx.name}: CID mismatch"]
  return (passed, cidPassed, total, fails)

/-! ## Runner -/

/-- The interpreter's final outcome for a fixture: execute, then fold the effect
replies through `resume` (the M6 harness protocol). -/
def interpFinal (fx : Fixture) : Except (Debug Unit) (Value Unit) :=
  fx.effects.foldl (init := execute fx.source []) fun ret (label, lift, reply) =>
    match ret with
    | .error (.UnhandledEffect l v, _, env, k) =>
        if l == label && v == lift then resume reply env k else ret
    | _ => ret

/-- Run a fixture: execute, fold effect replies through `resume`, compare. -/
def runFixture (fx : Fixture) : Bool :=
  match interpFinal fx, fx.expected with
  | .ok got, .ok exp => got == exp
  | .error (reason, _, _, _), .error exp => reason == exp
  | _, _ => false

/-- Fuel large enough to finish every spec fixture's longest segment. -/
def fbsFuel : Nat := 1000000

/-- Cross-check (Milestone S1): the functional big-step `Semantics.run`, driven
through the *same* effect oracle, reaches the same outcome as the M6 interpreter
harness — same value, same crash reason, or same unhandled effect at the
boundary. A concrete instance of the S5 bridge theorem, checked on every
fixture. -/
def fbsAgreesInterp (fx : Fixture) : Bool :=
  match Semantics.run fbsFuel (Semantics.Config.initial fx.source) fx.effects, interpFinal fx with
  | .done (.value gv), .ok iv => gv == iv
  | .done (.crash gr), .error (ir, _, _, _) => gr == ir
  | .effect op lift _, .error (.UnhandledEffect l v, _, _, _) => op == l && lift == v
  | _, _ => false

/-- Decode + run one suite file, returning `(passed, fbsAgreed, total,
failureNames)`. `fbsAgreed` counts fixtures where the functional big-step
semantics matches the interpreter (Milestone S1 cross-check). -/
def runSuiteJson (file : String) (j : Json) : Nat × Nat × Nat × List String := Id.run do
  let mut passed := 0
  let mut fbsAgreed := 0
  let mut total := 0
  let mut fails : List String := []
  match j.getArr? with
  | .error e => return (0, 0, 1, [s!"{file}: not a JSON array: {e}"])
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
          if fbsAgreesInterp fx then fbsAgreed := fbsAgreed + 1
          else fails := fails ++ [s!"{file}: {fx.name}: FBS≠interpreter"]
  return (passed, fbsAgreed, total, fails)

def suiteFiles : List String := ["core_suite.json", "builtins_suite.json", "effects_suite.json"]

def run : IO UInt32 := do
  let dir := "../spec/evaluation/"
  let mut passed := 0
  let mut fbsAgreed := 0
  let mut total := 0
  let mut fails : List String := []
  for file in suiteFiles do
    let contents ← IO.FS.readFile (dir ++ file)
    match Json.parse contents with
    | .error e => fails := fails ++ [s!"{file}: JSON parse error: {e}"]; total := total + 1
    | .ok j =>
        let (p, fbs, t, fs) := runSuiteJson file j
        passed := passed + p; fbsAgreed := fbsAgreed + fbs; total := total + t
        fails := fails ++ fs
  IO.println s!"spec evaluation: {passed}/{total} fixtures passed"
  IO.println s!"FBS≡interpreter: {fbsAgreed}/{total} fixtures agree"
  for f in fails do IO.println s!"  FAIL {f}"
  -- IR suite: structural round-trip and CIDv1-string equality
  let irContents ← IO.FS.readFile "../spec/ir_suite.json"
  let mut irPassed := 0
  let mut irCid := 0
  let mut irTotal := 0
  let mut irFails : List String := []
  match Json.parse irContents with
  | .error e => irFails := [s!"ir_suite.json: JSON parse error: {e}"]; irTotal := 1
  | .ok j =>
      let (p, c, t, fs) := runIrSuiteJson "ir_suite.json" j
      irPassed := p; irCid := c; irTotal := t; irFails := fs
  IO.println s!"ir round-trip: {irPassed}/{irTotal} | CID match: {irCid}/{irTotal}"
  for f in irFails do IO.println s!"  FAIL {f}"
  if passed == total ∧ fbsAgreed == total ∧ total > 0
      ∧ irPassed == irTotal ∧ irCid == irTotal ∧ irTotal > 0
    then pure 0 else pure 1

end Eyg.Spec

/-- Executable entry point (`lake exe spec`). -/
def main : IO UInt32 := Eyg.Spec.run
