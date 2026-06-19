---
name: type-soundness-report
description: Caveats to the claim that EYG type soundness has been proven in Lean — what the kernel theorem actually says, and where it is qualified.
date: 2026-06-19
---

# EYG Type Soundness — What We Proved, and the Caveats

## The verified claim

The bundled theorem `Eyg.Types.soundness` (`Eyg/Types/Soundness.lean:4263`) takes **only**
`HasType [] prog τ ε` — no leftover `Fix*`/saturation hypotheses — and `#print axioms`
confirms it (and `soundness_evalR`, `soundness_evalR_pure`) depends on exactly

```
[propext, Classical.choice, Quot.sound]
```

standard classical Lean, with **zero `sorry`** and **no custom axioms**. The substance: a
well-typed closed program's behaviours are a silent typed value, a *sanctioned* crash, or a
boundary suspension on an in-row effect — never a "bad" (type-error) crash, never an
out-of-row effect.

The proof is genuine and covers the hard, **un-precedented** part (row-based algebraic
effects + handlers). The caveats below qualify *what "EYG type soundness" means* — all are
documented in the plan; none are sloppiness.

---

## Caveat 1 — Proven about `Reduce`, not the shipped interpreter *(biggest)*

The interpreter's `step`/`eval`/`Behaviors` are `partial def`, hence kernel-opaque, so
preservation is unprovable about them. The proof is over a **separately-defined transparent
relation `Reduce`** (`evalR`/`BehaviorsR`). The bridge to the real interpreter is
**executable agreement only** — `#guard` over 104 fixtures at build time — *not* a kernel
equality.

> Strictly: "a semantics that is executably identical to the interpreter on the test
> battery is sound," not "the interpreter is sound."

## Caveat 2 — Against a *declarative* judgment, not the real analyzer

`HasType` is hand-transcribed from `gleam_analysis`. There is **no proof** that the actual
inference algorithm (`do_infer`/`unify`) is sound/complete w.r.t. `HasType` (the unstarted
T8 stretch). "Well-typed" = "derivable in the Lean judgment"; its faithfulness to the
shipped checker rests on inspection.

## Caveat 3 — The reference type system was *unsound*, and was changed to make this true

Machine-checked counterexample (Open Question 4): in the original analyzer,

```
!fix((x) -> { !int_add(x, 1) })     -- infers : Integer, pure, NO error
```

type-checks as `Integer` yet bad-crashes at runtime (`IncorrectTerm`). EYG's `fix` as
originally specified is **not sound**. The remedy: `contextual.gleam:530` was edited to force
the fixpoint to a *function* type (arrow-typed recursion still checks). So soundness holds
for a **corrected** type system.

## Caveat 4 — `fix` restricted to a *pure builder* — *and the reference was unsound here too*

Beyond the arrow restriction, the Lean `fix` scheme is pinned to a `∅`-latent (pure) builder.
This is **not merely an under-approximation**: effectful-builder `fix` (`q1 ≠ ∅`), which the
reference analyzer accepts, is **genuinely unsound** under call-by-value (machine-checked,
2026-06-19). The runtime re-runs the builder on every recursive self-application (`do_fixed`),
so a builder's *construction* effects re-fire at each recursive call — outside any handler
installed at `fix`-creation. A closed program the analyzer types as pure `Integer`
(`#(Ok(Nil), "Integer", "")`) thus performs an **unhandled / out-of-row `Log`** under both the
reference interpreter and the Lean `eval`/`evalR`:

```
let f = handle Log(...)((_) -> { !fix((self) -> {
          let inner = (n) -> { !int_add(self(n), 1) }   -- recurses
          let _ = perform Log("building")               -- construction effect, re-fired per call
          inner }) })
f(5)                                                    -- ⟶ UnhandledEffect("Log", "building")
```

So the pure-builder pin is **load-bearing**, like the arrow restriction (Caveat 3) — soundness
holds for a *corrected* `fix`. Proof: `Eyg/Types/CexEffectfulFix.lean` (`#guard` over `eval`
and `evalR`) + `progress/2026-06-19-G2-effectful-fix-unsoundness.md` (reference-tool repro). A
real remedy is source-language-side (pin `q1=∅` in `contextual.gleam`, or make the recursive
binding lazy); general row subsumption would *not* recover soundness here.

## Caveat 5 — Let-polymorphism is restricted (value restriction + `noLambdaLet`)

`HasType.let_poly` (`Typing.lean:103`) generalizes only when the definition is a **lambda**
whose body contains **no nested *generalizable* `let`** — i.e. no `let` binding a lambda
(`Node.noLambdaLet`, `Ir/Tree.lean`; relaxed from `noLet` on 2026-06-19):

```
let id   = \x. x                in ...   -- ✓ generalized (combinator polymorphism)
let f    = \x. \y. x            in ...   -- ✓
let g    = \x. (let z = x in z) in ...   -- ✓ now allowed: nested let binds a *non-lambda*
let h    = \x. (let k = \y.y in k x) in  -- ✗ still excluded: nested let binds a *lambda*
```

Covers all rank-1 / combinator polymorphism **plus** any internal mono (non-function) `let` inside
a polymorphic function. **Full nested let-generalization** (a nested binding that itself
generalizes) is still not proven: the plan proves *why* the easy route fails
(`generalizes_subst_false`, a machine-checked theorem that `Generalizes` is not
substitution-stable), and the readiness keystone would need re-typing the body under the
instantiation — which is not a level map for that case
(`progress/2026-06-19-G1-noLambdaLet-relaxation-path.md`,
`…-instantiation-levelmap-gap.md`).

## Caveat 6 — "Never goes wrong" still permits `Unrepresentable` crashes

Soundness excludes only *bad* crashes (`Vacant`, `NotAFunction`, `NoMatch`, `MissingField`,
`UndefinedVariable`, `IncorrectTerm`, …). A well-typed program **may still crash** with
`Unrepresentable` — e.g. integer overflow:

```
!int_add(big, big)   -- well-typed : Integer, may crash Unrepresentable (sanctioned)
```

So it is "no *type-error* crash," not "no crash."

## Caveat 7 — Open-system results assume a well-behaved environment

The headline `soundness` covers silent (`tau`-only) terminations and boundary suspension
**unconditionally**. But **divergence** (`soundness_behaviorsR_diverges`) and
**reply-containing terminating traces** (`soundness_behaviorsR_terminates_value/_noBadCrash`)
are conditioned on `ReplyContract` / `TraceRepliesOk` — the assumption that the external world
feeds back **well-typed** reply values. That is the *rely* half of a rely-guarantee, an
assumption rather than a theorem.

## Caveat 8 — Scope exclusions

- **References / linking** (`ContentReference`/`ReleaseReference`/`RelativeReference`) are out
  of scope — they crash; the theorem is about closed, linked core terms (T8 stretch).
- **`Vacant`** (the todo/hole node) is excluded from "well-typed" by fiat (Open Question 2).
- `RowEquiv` decidability is deferred (not needed for the declarative proof).

---

## Bottom line

"We have proven EYG type soundness" should be read as:

> For a declarative judgment transcribed from (and in **two** places **correcting**) the gleam
> analyzer, a transparent reduction relation that **agrees with the interpreter on 104
> fixtures** is type-sound — for the fragment excluding effectful-`fix` (shown unsound, #4),
> nested let-generalization, and references — where "sound" still allows `Unrepresentable`
> crashes, and the open-system (divergence/reply) guarantees assume the environment returns
> well-typed replies.

Most consequential gaps: **#1** (executable-only bridge to the real interpreter) and **#2**
(no proof the checker matches the judgment). Most surprising: **#3 and #4** — the reference spec
was unsound in *two* `fix` ways (base-type and effectful-builder), both machine-checked and
corrected — and **#5/#6** (the polymorphism and "crash" qualifiers).
