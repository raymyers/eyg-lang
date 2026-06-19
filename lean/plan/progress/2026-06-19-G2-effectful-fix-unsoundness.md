---
date: 2026-06-19
milestone: G2 (Caveat 4) — effectful-builder `fix` is UNSOUND (machine-checked counterexample)
status: DONE — counterexample found, confirmed on both reference tools + machine-checked in Lean
kind: soundness-counterexample
component: gleam_analysis (type checker) + gleam_interpreter (evaluator) + Lean port
---

# G2 / Caveat 4 — effectful-builder `fix` is unsound (the fork **refutes**)

The plan's G2 fork (prove effectful-builder `fix` sound, **or** find a counterexample) is
**resolved by counterexample**. The reference analyzer accepts a closed program as a pure
`Integer`; the reference interpreter runs it to an **unhandled (out-of-row) `Log` effect**.
This is the effect analog of the base-type-`fix` unsoundness (Open Question 4,
`2026-06-17-fix-base-type-unsoundness.md`) and **justifies the Lean pure-builder pin**
(`Builtins.scheme "fix"` / `HasTypeV.partialFixed` keep the builder latent at `∅`): the
restriction is *load-bearing*, not a proof-engineering artifact.

## TL;DR

The reference `fix` scheme (`contextual.gleam:530`) has a **free** builder/recursion effect
row `q1`:

```
fix : ((q0 →⟨q2⟩ q3) →⟨q1⟩ (q0 →⟨q2⟩ q3)) →⟨q1⟩ (q0 →⟨q2⟩ q3)
```

so it accepts a builder that performs effects *while constructing* the recursive function
(`q1 ≠ ∅`). Under call-by-value this is unsound: the runtime **re-runs the builder on every
recursive self-application** (`do_fixed`, `state.gleam` / `Interpreter/State.lean:194`). The
builder's *construction* effects therefore fire again at each recursive step, under whatever
ambient the recursive call happens in — and a handler installed at `fix`-creation time no
longer covers that ambient.

## The mechanism (why a handler at creation doesn't help)

Both the reference and the Lean executable interpreter implement `fix` **eagerly**:
`do_fix builder = call builder (fixed builder)` — the builder runs once, immediately, at
`fix`-creation. So a `handle Log` wrapping the `fix` expression *does* catch that first
construction `Log`. But the recursive function returned by the builder calls `self`; applying
the internal `fixed builder` partial (`do_fixed`) **re-evaluates `builder (fixed builder)`**,
re-performing the construction `Log` — now at the recursive call site, outside the original
handler. The analyzer charges `q1` to `fix`'s latent at *creation* (where the handler
discharges it); the runtime pays it again at *every call*.

## The witness program (closed)

```
let f =
  handle Log ((value) -> { (k) -> { k({}) } })          // discharges Log at CREATION
            ((_) -> {
               !fix((self) -> {
                 let inner = (n) -> { !int_add(self(n), 1) }   // recurses: calls self
                 let _ = perform Log("building")               // CONSTRUCTION effect
                 inner
               })
            })
f(5)
```

(Writing wrinkle: bind `inner` *before* `perform Log(...)`; a `let _ = perform Log(..)` placed
immediately before a parenthesized lambda parses as applying the perform-result to the lambda.)

## Reproduction — both reference tools (Gleam, nix toolchain)

```sh
nix shell nixpkgs#gleam nixpkgs#nodejs_22 --command gleam test
```

### (1) Type checker — `packages/gleam_analysis`

Add a test mirroring the `calc` helper (`do_resolve` + `debug.mono`/`debug.effect`, head triple
= whole program) in `test/eyg/analysis/inference/levels_j/`:

```gleam
pub fn cex_effectful_builder_fix_test() {
  let src =
    "
    let f = handle Log((value) -> { (k) -> { k({}) } })((_) -> {
      !fix((self) -> {
        let inner = (n) -> { !int_add(self(n), 1) }
        let _ = perform Log(\"building\")
        inner
      })
    })
    f(5)
    "
  echo calc(src, t.Empty)
}
```

**Observed whole-program (first) triple:**

```
#(Ok(Nil), "Integer", "")
```

`Ok(Nil)` = no type error; type = `Integer`; effect = `""` (pure). The builder's `Log` is
absorbed into `fix`'s latent `q1` at creation, where `handle Log` discharges it, so the
program's residual effect row is empty.

### (2) Evaluator — `packages/gleam_interpreter`

```gleam
pub fn cex_effectful_builder_fix_test() {
  let inner =
    ir.lambda("n", ir.apply(ir.apply(ir.builtin("int_add"),
      ir.apply(ir.variable("self"), ir.variable("n"))), ir.integer(1)))
  let builder =
    ir.lambda("self", ir.let_("inner", inner,
      ir.let_("_", ir.apply(ir.perform("Log"), ir.string("building")), ir.variable("inner"))))
  let exec = ir.lambda("_", ir.apply(ir.builtin("fix"), builder))
  let handler = ir.lambda("value", ir.lambda("k", ir.apply(ir.variable("k"), ir.empty())))
  let f = ir.apply(ir.apply(ir.handle("Log"), handler), exec)
  let prog = ir.let_("f", f, ir.apply(ir.variable("f"), ir.integer(5)))
  echo r.execute(prog, [])
}
```

**Observed result:**

```
Error(#(UnhandledEffect("Log", String(value: "building")), …control, env, stack…))
```

A well-typed (pure `Integer`) program performs an effect not in its declared (empty) row —
exactly a type-soundness violation (the report's "never an out-of-row effect").

## Machine-checked in Lean

`lean/Eyg/Types/CexEffectfulFix.lean` builds the same closed program (`prog`) in the `Tree`
IR and `#guard`s that **both** semantics reduce it to the out-of-row boundary:

```
eval  1000 (Config.initial prog)  ⟶  .effect "Log" (.String "building") _
evalR 1000 (Config.initial prog)  ⟶  .effect "Log" (.String "building") _
```

`evalR` is the transparent relation the headline `soundness`/`soundness_evalR` is proved over;
a `HasType []` derivation under the *un-pinned* (reference) `fix` scheme would type `prog` at
effect `∅`, so this `Log` boundary is an out-of-row effect — the soundness conclusion would be
**false** without the pure-builder restriction. (`#guard`, no axioms; `lake build` 1773 +
`lake exe spec` 104/104; headline `soundness` axioms unchanged: `propext`/`Classical.choice`/
`Quot.sound`.)

## Consequence for the plan

- **G2 / Caveat 4 is DONE (refuted).** Effectful-builder `fix` (the analyzer's `q1 ≠ ∅`) is
  unsound; the Lean pure-builder pin is *correct and necessary*. The "coverage gap" is
  re-classified to a **known source-language unsoundness** (like base-type `fix`).
- **A real remedy would have to be on the source-language side** (as base-type `fix` was): e.g.
  force `fix`'s builder latent to `∅` in `contextual.gleam` too, or make the recursive binding
  lazy / memoise the builder so construction effects fire once. Until then the analyzer over-
  accepts; the Lean model (with the pin) is the *sound* subset.
- Building the substitution-stable `EffSub'` (the other G2 bullet) is **not needed for
  soundness** and would only let the Lean model track the unsound feature — there is nothing
  sound there to track. Leave the pin.
