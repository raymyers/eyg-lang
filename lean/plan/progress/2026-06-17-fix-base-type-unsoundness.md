---
date: 2026-06-17
kind: soundness-counterexample
component: gleam_analysis (type checker) + gleam_interpreter (evaluator)
status: RESOLVED — scheme hardened in gleam_analysis + Lean, verified by running the analyzer
---

# EYG type-soundness counterexample: `fix` at a base-type fixpoint

> **Resolution (2026-06-17).** Fixed by hardening the `fix` scheme so the fixpoint is
> forced to a **function** type (`contextual.gleam:530`, mirrored in the Lean
> `Builtins.scheme`). The base-type program below now **fails to type-check**
> (`TypeMismatch(Integer, Fun(…))`) while real (arrow-typed) recursion still checks; the
> full analyzer suite still passes. See "Resolution" at the bottom.

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

## It crashes — it does *not* merely diverge

A natural objection: maybe this is just non-termination (which would be acceptable),
not a crash. It is a crash. The fuel-indexed evaluator's `Result` distinguishes
`.timeout` (fuel exhausted — the divergence proxy) from `.done (.crash …)` (halted at
an error). Sweeping fuel on `eval`/`evalR` (`Config.initial` of the program):

```
fuel    3  -> TIMEOUT      (terminal not yet reached)
fuel    8  -> TIMEOUT
fuel   50  -> CRASH: IncorrectTerm "Integer" (Partial (Builtin "fixed") [Closure "x" …])
fuel 100000 -> CRASH       (identical — more fuel does not change it)
```

A divergent program stays `.timeout` at *every* fuel; this one reaches a fixed crash
state in under 50 steps and stays there. The reason it halts rather than loops: the
builder `\x. int_add x 1` uses the bound recursive value `x` **immediately as an
integer** and never makes a recursive call, so the single unroll
`fix builder → builder (fixed) → int_add fixed 1` hits `Cast.asInteger fixed` and
fails at once. (Note "base-type fix" can also manifest as divergence for a builder
that *does* recurse — but this particular witness is a definite crash, which is the
stronger statement for soundness.)

Also note the *fixpoint result* type is the base type `Integer`, not a function type:
the builder `\x. int_add x 1` is `Integer → Integer`, and `fix : (α→α)→α` makes
`α = Integer`. (A recursive *function* would be `fix (\self. \x. …)`, two lambdas,
whose fixpoint is an arrow and is sound.)

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

## Resolution (applied & verified)

The first remedy was adopted. The `fix` scheme now forces the fixpoint `self` to be a
function type.

**`gleam_analysis` — `contextual.gleam:530`:**

```gleam
#("fix", {
  let self = t.Fun(q(0), q(2), q(3))           // the fixpoint is an arrow
  t.Fun(t.Fun(self, q(1), self), q(1), self)   // (self -><q1> self) -><q1> self
}),
```

**Verified by running the analyzer** (`nix shell nixpkgs#gleam nixpkgs#nodejs_22 --command
gleam test`), top-level result triples:

```
base-type   !fix((x) -> { !int_add(x, 1) })
  ->  #(Error(TypeMismatch(Integer, Fun(Var(0), Var(1), Var(2)))), …)   -- REJECTED
arrow-type  !fix((self) -> { (n) -> { !int_add(n, 1) } })
  ->  #(Ok(Nil), "(Integer) -> Integer", "")                           -- still accepted
```

The full `gleam_analysis` test suite still passes (no regressions).

**Lean model** updated to match (`lean/Eyg/Types/Scheme.lean`, `Builtins.scheme "fix"`,
arity 4):

```
fix : ((q0 →⟨q2⟩ q3) →⟨q1⟩ (q0 →⟨q2⟩ q3)) →⟨q1⟩ (q0 →⟨q2⟩ q3)
```

so the Lean `HasType` likewise cannot type `fix (\x. x+1)` (the builder's codomain
`Integer` can't equal the forced arrow `q0→⟨q2⟩q3`). `lake build` + `lake exe spec`
104/104, axioms clean. This also **aligns the reference with `HasTypeV.partialFixed`**:
both now force an arrow fixpoint, so the arrow restriction is no longer a Lean-side
divergence from gleam. The only remaining Lean under-approximation is the **pure-builder**
restriction (`partialFixed` pins the builder's eval latent to `∅`, while the scheme leaves
`q1` free) — sound, and liftable once effect-row subsumption (Open Question 3) lands.
