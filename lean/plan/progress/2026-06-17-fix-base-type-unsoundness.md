---
date: 2026-06-17
kind: soundness-counterexample
component: gleam_analysis (type checker) + gleam_interpreter (evaluator)
status: confirmed (both reference tools executed)
---

# EYG type-soundness counterexample: `fix` at a base-type fixpoint

## TL;DR

The EYG **type checker accepts** a closed program at type `Integer` (pure), and the
EYG **evaluator bad-crashes** that same program. Both results were produced by running
the actual reference tools (`gleam_analysis` and `gleam_interpreter`). That is a
genuine **type-soundness violation**: a well-typed program "goes wrong".

The offending program is the fixed-point combinator applied to a builder whose
fixpoint type is a **base type** rather than a function type:

```
fix (\x. int_add x 1)
```

This is the textbook *call-by-value `fix` at a non-function type* unsoundness. It is
**isolated to the `fix`/`fixed` builtin's type scheme**; the rest of EYG is unaffected
(an arrow-typed `fix (\self. \n. …)` is sound).

## The program

EYG concrete syntax:

```
!fix((x) -> { !int_add(x, 1) })
```

As `eyg/ir/tree` constructors (the form the snippets below use):

```gleam
ir.apply(
  ir.builtin("fix"),
  ir.lambda(
    "x",
    ir.apply(ir.apply(ir.builtin("int_add"), ir.variable("x")), ir.integer(1)),
  ),
)
```

Intuition: `fix : ∀α β. (α →⟨β⟩ α) →⟨β⟩ α`. The builder `\x. int_add x 1` forces
`x : Integer` and returns `Integer`, so it unifies the builder type at
`Integer →⟨{}⟩ Integer`, i.e. `α = Integer`, `β = {}`. Thus `fix (\x. x+1) : Integer`.
But the runtime fixpoint value is an internal `fixed` *closure/partial*, not an
`Integer` — so when it is consumed as the `Integer` argument of `int_add`, the cast
fails. In a call-by-value language a fixpoint can only inhabit a **function** type;
the scheme fails to enforce that.

## Reproduction — both reference tools (Gleam)

Run with the nix-provided toolchain (no global install needed):

```sh
nix shell nixpkgs#gleam nixpkgs#nodejs_22 --command gleam test
```

### (1) Type checker — `packages/gleam_analysis`

Add to `test/eyg/analysis/inference/levels_j/contextual_test.gleam` (it already defines
the `calc` helper used here, which runs `j.infer` + `binding.resolve` + `debug.mono`
and returns one `#(error, type, effect)` triple per IR node, head = whole program):

```gleam
pub fn fix_base_type_unsound_test() {
  // `!fix((x) -> { !int_add(x, 1) })`
  echo calc("!fix((x) -> { !int_add(x, 1) })", t.Empty)
}
```

**Observed top-level result (first triple):**

```
#(Ok(Nil), "Integer", "")
```

`Ok(Nil)` = **no type error**; type = **`Integer`**; effect = **`""` (pure)**. For
contrast, the arrow-typed fixpoint `!fix((self) -> { (n) -> { !int_add(n, 1) } })`
infers `(Integer) -> Integer` — the sound case.

The relevant scheme is in
`packages/gleam_analysis/src/eyg/analysis/inference/levels_j/contextual.gleam:530`:

```gleam
#("fix", t.Fun(t.Fun(q(0), q(1), q(0)), q(1), q(0))),
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^   q(0) (the fixpoint) is a FREE quantified
//        (q0 →⟨q1⟩ q0) →⟨q1⟩ q0         variable — nothing forces it to be a Fun.
```

### (2) Evaluator — `packages/gleam_interpreter`

Add to `test/eyg/interpreter/int_test.gleam` (it imports
`eyg/interpreter/expression as r` and `eyg/ir/tree as ir`):

```gleam
pub fn fix_base_type_unsound_test() {
  let prog =
    ir.apply(
      ir.builtin("fix"),
      ir.lambda(
        "x",
        ir.apply(ir.apply(ir.builtin("int_add"), ir.variable("x")), ir.integer(1)),
      ),
    )
  echo r.execute(prog, [])
}
```

**Observed result** (elided to the essential `Debug` reason):

```
Error(#(IncorrectTerm(expected: "Integer",
                      got: Partial(Builtin("fixed"), [Closure(param: "x", body: …)])),
        …control, env, stack…))
```

The runtime tried to use the internal `fixed` partial where an `Integer` was required
and raised `IncorrectTerm`.

## Why it is a soundness violation (not a sanctioned outcome)

EYG's semantics is total: ill-formed programs reduce to a `crash` outcome rather than
getting stuck. Soundness for EYG is therefore "a well-typed program's outcome is never
a *bad* crash" (every crash reason except `Unrepresentable`, the sanctioned
integer-overflow/parse trap, counts as bad). `IncorrectTerm` is a **bad** crash. So a
program accepted by the checker producing `IncorrectTerm` is exactly a soundness
violation, not an acceptable trap.

(Cross-checked in the Lean port: `FunctionalBigStep.eval` *and* the transparent
`Reduction.evalR` both reduce this program to
`Reason.IncorrectTerm "Integer" (Partial (Builtin "fixed") [...])`, and
`Reason.IsBad` is `True` for everything except `Unrepresentable` —
`lean/Eyg/Types/Soundness.lean`.)

## The fix (type-system side)

Restrict `fix`'s fixpoint to a **function type** (the only shape that is sound under
call-by-value), e.g.

```gleam
// fix : ∀ d γ r. ((d →⟨γ⟩ r) →⟨{}⟩ (d →⟨γ⟩ r)) →⟨{}⟩ (d →⟨γ⟩ r)
#("fix", t.Fun(
    t.Fun(t.Fun(q(0), q(1), q(2)), t.Empty, t.Fun(q(0), q(1), q(2))),
    t.Empty,
    t.Fun(q(0), q(1), q(2)))),
```

(Pinning the builder's evaluation latent to `{}` additionally keeps the standard
"build the recursive function purely" fragment; a builder that performs *while
constructing* the function would need general effect-row subsumption.) This narrows
what EYG accepts versus the current analyzer — it rejects base-type fixpoints, which
are unsound anyway — and is the restriction the Lean soundness proof encodes as
`HasTypeV.partialFixed` (`lean/Eyg/Types/Runtime.lean`); see
`progress/2026-06-17-T6b-partialFixed-reapplication.md` and Open Question 4 in
`eyg-type-soundness.md`. Alternatively, make the recursive binding lazy so the fixpoint
can inhabit any type.
