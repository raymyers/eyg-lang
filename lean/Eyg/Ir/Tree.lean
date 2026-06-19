/-!
# EYG IR expression tree

Mirrors `packages/gleam_ir/src/eyg/ir/tree.gleam` one-for-one.

A `Node m` is an expression paired with metadata of type `m`
(Gleam: `pub type Node(m) = #(Expression(m), m)`). The runner instantiates
`m := Unit` (every spec fixture uses `Nil` metadata, decision #4 in the plan),
but the type stays metadata-generic so the shape matches the Gleam source.

**Deviation from the Gleam shape (and the plan's `Node := Expr m × m`):** `Node`
is a single-field `structure` in a `mutual` block with `Expr`, rather than a
`Prod` alias. The recursion `Expr → Node → Expr` is then *direct*, which lets
Lean derive `DecidableEq` (the `DecidableEq` deriving handler cannot see through
the `Prod` in `Expr m × m` — that is a nested inductive). `DecidableEq` on `Node`
is required transitively by `Value` in Milestone 1, so we pay for it here. The
named projections `Node.expr`/`Node.annotation` replace `.1`/`.2`.

Builtin / reference identifiers: Gleam stores a `v1.Cid` for content and release
references. We model the CID as its canonical string form (`Cid := String`);
that is all the interpreter needs, since every reference node evaluates to an
`Undefined*` failure for the spec.
-/

namespace Eyg.Ir.Tree

/-- `ByteArray` has no `Repr` in core; provide one (via its byte list) so the
expression tree can derive `Repr` for `#eval`/debugging. Scoped to this file. -/
local instance : Repr ByteArray where
  reprPrec b _ := repr b.toList

/-- Canonical string form of a CIDv1, used by content/release references. -/
abbrev Cid := String

mutual

/-- EYG IR expressions, mirroring `Expression(m)` in `tree.gleam`. -/
inductive Expr (m : Type) where
  | Variable (label : String)
  | Lambda (label : String) (body : Node m)
  | Apply (func : Node m) (argument : Node m)
  | Let (label : String) (definition : Node m) (body : Node m)
  | Binary (value : ByteArray)
  | Integer (value : Int)
  | String (value : String)
  | Tail
  | Cons
  | Vacant
  | Empty
  | Extend (label : String)
  | Select (label : String)
  | Overwrite (label : String)
  | Tag (label : String)
  | Case (label : String)
  | NoCases
  | Perform (label : String)
  | Handle (label : String)
  | Builtin (identifier : String)
  | ContentReference (identifier : Cid)
  | ReleaseReference (package : String) (version : Int) (identifier : Cid)
  | RelativeReference (location : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An expression paired with its metadata (Gleam `Node(m) = #(Expression(m), m)`). -/
structure Node (m : Type) where
  expr : Expr m
  annotation : m
  deriving Repr, BEq, DecidableEq, Inhabited

end

/-! ## Smart constructors

Mirror the Gleam smart constructors, which build a node with `Nil` metadata.
In Lean that is `()` at metadata type `Unit`. -/

@[inline] def node (e : Expr Unit) : Node Unit := ⟨e, ()⟩

def variable_ (label : String) : Node Unit := node (.Variable label)
def lambda (label : String) (body : Node Unit) : Node Unit := node (.Lambda label body)
def apply (func argument : Node Unit) : Node Unit := node (.Apply func argument)
def let_ (label : String) (value then_ : Node Unit) : Node Unit := node (.Let label value then_)
def binary (value : ByteArray) : Node Unit := node (.Binary value)
def integer (value : Int) : Node Unit := node (.Integer value)
def string (value : String) : Node Unit := node (.String value)
def tail : Node Unit := node .Tail
def cons : Node Unit := node .Cons
def vacant : Node Unit := node .Vacant
def empty : Node Unit := node .Empty
def extend (label : String) : Node Unit := node (.Extend label)
def select (label : String) : Node Unit := node (.Select label)
def overwrite (label : String) : Node Unit := node (.Overwrite label)
def tag (label : String) : Node Unit := node (.Tag label)
def case_ (label : String) : Node Unit := node (.Case label)
def nocases : Node Unit := node .NoCases
def perform (label : String) : Node Unit := node (.Perform label)
def handle (label : String) : Node Unit := node (.Handle label)
def builtin (identifier : String) : Node Unit := node (.Builtin identifier)
def reference (identifier : Cid) : Node Unit := node (.ContentReference identifier)
def release (package : String) (rel : Int) (identifier : Cid) : Node Unit :=
  node (.ReleaseReference package rel identifier)

/-- **`e` contains no `Let` node** (structurally). Used as the value-restriction guard on a
polymorphic `let`'s generalized lambda body (T6 `let_poly`): a let-free body lets the readiness
keystone re-type it under the instantiation substitution with the *original* (arbitrary-σ)
`hasType_subst` whose `Let`/`let_poly` arms are then vacuous — sidestepping the instantiation-vs-LevelMap
gap that genuinely-nested let-generalization hits (see the cascade progress notes). Covers all
combinator polymorphism (`\x.x`, `\x.\y.x`, `\f.\x. f (f x)`, …). -/
def Node.noLet {m : Type} : Node m → Prop
  | ⟨.Lambda _ b, _⟩ => b.noLet
  | ⟨.Apply f a, _⟩ => f.noLet ∧ a.noLet
  | ⟨.Let _ _ _, _⟩ => False
  | _ => True

/-- `func(params, body)` — fold params right into nested lambdas. -/
def func (params : List String) (body : Node Unit) : Node Unit :=
  params.foldr (fun param acc => lambda param acc) body

/-- `call(f, args)` — fold args left into nested applications. -/
def call (f : Node Unit) (args : List (Node Unit)) : Node Unit :=
  args.foldl (fun acc arg => apply acc arg) f

/-- `block(assignments, then)` — fold right into nested lets. -/
def block (assignments : List (String × Node Unit)) (then_ : Node Unit) : Node Unit :=
  assignments.foldr (fun a acc => let_ a.1 a.2 acc) then_

/-- `list(items)` — desugar to nested `cons`/`tail`. -/
def list (items : List (Node Unit)) : Node Unit :=
  items.foldr (fun item acc => apply (apply cons item) acc) tail

/-- `record(fields)` — desugar to nested `extend`/`empty`. -/
def record (fields : List (String × Node Unit)) : Node Unit :=
  fields.foldr (fun f acc => apply (apply (extend f.1) f.2) acc) empty

def unit : Node Unit := empty
def get (value : Node Unit) (label : String) : Node Unit := apply (select label) value
def tagged (label : String) (inner : Node Unit) : Node Unit := apply (tag label) inner
def true' : Node Unit := tagged "True" unit
def false' : Node Unit := tagged "False" unit

/-- `match(value, matches)` — fold right into nested `case`/`nocases`, applied to value. -/
def match_ (value : Node Unit) (branches : List (String × Node Unit)) : Node Unit :=
  let m := branches.foldr (fun mt acc => call (case_ mt.1) [mt.2, acc]) nocases
  apply m value

def add (a b : Node Unit) : Node Unit := apply (apply (builtin "int_add") a) b
def subtract (a b : Node Unit) : Node Unit := apply (apply (builtin "int_subtract") a) b
def multiply (a b : Node Unit) : Node Unit := apply (apply (builtin "int_multiply") a) b

/-! ## Smoke check (Milestone 0) -/

-- `(\x. x) 1`
private def idApp : Node Unit := apply (lambda "x" (variable_ "x")) (integer 1)

example : idApp == idApp := by native_decide
example : (integer 1) ≠ (integer 2) := by decide

end Eyg.Ir.Tree

namespace Eyg.Ir.Integer

/-- True when the integer is exactly representable on the JS target: magnitude
≤ 2^53 − 1 (`Number.isSafeInteger`). Mirrors `integer.is_safe`; on Erlang every
integer is exact, but the spec fixtures encode the JS-safe-range behavior so
out-of-range input fails with `Unrepresentable` instead of rounding. -/
def isSafe (value : Int) : Bool := value.natAbs ≤ 9007199254740991

example : isSafe 1 = true := by decide
example : isSafe (2 ^ 53) = false := by decide

end Eyg.Ir.Integer
