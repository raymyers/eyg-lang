import Eyg.Semantics.FunctionalBigStep
import Eyg.Semantics.Reduction

/-!
# Counterexample: effectful-builder `fix` is unsound (Caveat 4 / G2)

The reference type analyzer (`gleam_analysis`, `contextual.gleam:530`) types `fix`
with a **free** builder/recursion effect row `q1`:

```
fix : ((q0 →⟨q2⟩ q3) →⟨q1⟩ (q0 →⟨q2⟩ q3)) →⟨q1⟩ (q0 →⟨q2⟩ q3)
```

so it accepts a builder that performs effects *while constructing* the recursive
function. This is **unsound** under call-by-value, because the runtime re-runs the
builder on every recursive self-application (`do_fixed`, `State.lean:194`): the
builder's *construction* effects fire again at each recursive step, under whatever
ambient the recursive call happens in — which a handler installed at `fix`-creation
time no longer covers.

## The witness program (closed)

```
let f =
  handle Log ((value) -> (k) -> k({}))          -- discharges Log at CREATION
            ((_) ->
               fix ((self) ->
                 let inner = (n) -> int_add(self(n), 1)   -- recurses: calls self
                 let _ = perform Log("building")          -- CONSTRUCTION effect
                 inner))
f(5)
```

The analyzer types this whole program as `#(Ok(Nil), "Integer", "")` — **well-typed,
type `Integer`, effect `""` (pure)**. (Confirmed by running `j.infer`; the builder's
`Log` is absorbed into `fix`'s latent `q1` at creation, where the `handle Log`
discharges it, so the program's residual effect row is empty.)

Operationally, though:
* `fix builder` eagerly runs `builder (fixed builder)` once — *inside* the handler —
  performing `Log("building")` (handled, resumes); it returns `inner`.
* `f(5)` runs `inner 5 = int_add (self 5) 1`; evaluating `self 5` applies the internal
  `fixed builder` partial, which **re-runs** `builder (fixed builder)` — performing
  `Log("building")` **again**, now *outside* the handler → an **unhandled / out-of-row**
  effect.

So a program the reference analyzer certifies as pure `Integer` performs an effect not
in its declared (empty) row: a genuine type-soundness violation. This is the effect
analog of the base-type-`fix` unsoundness (Open Question 4 /
`progress/2026-06-17-fix-base-type-unsoundness.md`), and it is exactly why the Lean
`Builtins.scheme "fix"` / `HasTypeV.partialFixed` keep the **pure-builder** pin
(`q1 = ∅`): the pin is *load-bearing*, not a proof-engineering artifact.
-/

namespace Eyg.Types.CexEffectfulFix

open Eyg.Semantics
open Eyg.Interpreter
open Eyg.Ir
open Eyg.Ir.Tree

/-- The effectful builder: `(self) -> { let inner = (n) -> int_add(self n, 1); _ = perform Log("building"); inner }`. -/
def builder : Tree.Node Unit :=
  let inner := Tree.lambda "n" (Tree.add (Tree.apply (Tree.variable_ "self") (Tree.variable_ "n")) (Tree.integer 1))
  Tree.lambda "self"
    (Tree.let_ "inner" inner
      (Tree.let_ "_" (Tree.apply (Tree.perform "Log") (Tree.string "building"))
        (Tree.variable_ "inner")))

/-- `(value) -> (k) -> k({})` — resume the captured continuation with unit. -/
def handler : Tree.Node Unit :=
  Tree.lambda "value" (Tree.lambda "k" (Tree.apply (Tree.variable_ "k") Tree.empty))

/-- `(_) -> fix builder` — produces the recursive function value (builder runs once, here). -/
def exec : Tree.Node Unit :=
  Tree.lambda "_" (Tree.apply (Tree.builtin "fix") builder)

/-- The whole closed program: `let f = handle Log handler exec in f(5)`. -/
def prog : Tree.Node Unit :=
  Tree.let_ "f"
    (Tree.apply (Tree.apply (Tree.handle "Log") handler) exec)
    (Tree.apply (Tree.variable_ "f") (Tree.integer 5))

-- **Machine-check (executable big-step `eval`):** the program — typed pure `Integer`
-- by the reference analyzer — performs an **unhandled `Log` effect** at the boundary. The
-- lift value `"building"` is the builder's construction-time `perform Log` argument, re-fired
-- outside the handler during the recursive `self 5`.
#guard (match eval 1000 (Config.initial prog) with
    | .effect op lift _ => op == "Log" && lift == (Value.String "building")
    | _ => false)

-- **Machine-check (transparent soundness relation `evalR`):** the same out-of-row `Log`
-- boundary — the relation the headline `soundness`/`soundness_evalR` is proved over.
-- A `HasType []`-style derivation under the *un-pinned* (reference) `fix` scheme would
-- classify this program as effect `∅`, so this boundary is an out-of-row effect: the
-- soundness conclusion would be **false** without the pure-builder restriction.
#guard (match evalR 1000 (Config.initial prog) with
    | .effect op lift _ => op == "Log" && lift == (Value.String "building")
    | _ => false)

end Eyg.Types.CexEffectfulFix
