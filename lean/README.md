# EYG in Lean 4

A Lean 4 formalization of [EYG](https://eyg.run): an executable interpreter, a
formal operational semantics, and a machine-checked type-soundness proof — all
in one project, wired to [cslib](https://github.com/fmontesi/cslib) (which pulls
in mathlib transitively).

The reference implementation is the Gleam interpreter in
`packages/gleam_interpreter`; the reference type system is `gleam_analysis`.
This project ports both to Lean and reasons about them.

## Layout

| Path | What it is |
| --- | --- |
| [`Eyg/Ir/`](Eyg/Ir) | The core term IR (`Tree`) and content addressing (`Cid`). |
| [`Eyg/Interpreter/`](Eyg/Interpreter) | Executable CEK interpreter — the workhorse. `partial def step`/`eval`, builtins, values. |
| [`Eyg/Spec/`](Eyg/Spec) | `Harness` — `lake exe spec` runs the `spec/` fixtures and exits non-zero on any failure. |
| [`Eyg/Semantics/`](Eyg/Semantics) | Formal operational semantics — see its [README](Eyg/Semantics/README.md). |
| [`Eyg/Types/`](Eyg/Types) | The `HasType` judgment, reduction relation, and the soundness proof. |

`Eyg.lean` re-exports the shipped modules (the `Types/*Spike*` and `G2*` files
are exploratory scaffolding and are intentionally not imported).

## The three artifacts

1. **Interpreter** — a CEK state machine structured like the Gleam original,
   pinned to behave identically by every fixture in `spec/`. Plan:
   [`plan/eyg-interpreter.md`](plan/eyg-interpreter.md).

2. **Semantics** — a fuel-indexed functional big-step interpreter reflected as
   a cslib labelled transition system, so a program's meaning is a *trace of
   effect events* plus an outcome, proved to agree with the interpreter. Plan:
   [`plan/eyg-semantics.md`](plan/eyg-semantics.md); rationale for the two-artifact
   split in [`plan/eyg-difference-semantics.md`](plan/eyg-difference-semantics.md).

3. **Type soundness** — Progress + Preservation plus effect-safety, over a
   transparent reduction relation `Reduce`. The bundled `Eyg.Types.soundness`
   (`Eyg/Types/Soundness.lean`) takes only `HasType [] prog τ ε`, has **no
   `sorry`** and **no custom axioms**. Plan:
   [`plan/eyg-type-soundness.md`](plan/eyg-type-soundness.md).

## What the soundness theorem does and doesn't claim

Read [`plan/report/type-soundness-report.md`](plan/report/type-soundness-report.md)
before relying on the result. In short: the proof is genuine and covers the hard,
un-precedented part (row-based algebraic effects + handlers), but is qualified —
it is about `Reduce` (bridged to the interpreter by executable agreement on the
fixtures, not kernel equality), against a hand-transcribed declarative `HasType`
rather than the shipped inference algorithm. The two coverage gaps (effectful-builder
`fix`, nested let-polymorphism) are tracked in
[`plan/eyg-type-soundness2-gaps.md`](plan/eyg-type-soundness2-gaps.md).

## Building

```sh
lake build          # build everything
lake exe spec       # run the spec/ fixture harness
```

Toolchain is pinned in `lean-toolchain`; cslib is pinned by revision in
`lakefile.toml`. A `flake.nix` provides the dev environment.

## Development history

The blow-by-blow record lives in [`plan/progress/`](plan/progress) (dated session
notes, especially the long G1/G2 arc closing the soundness walls) and the
supporting literature summaries in [`plan/references/`](plan/references). The
original instructions that seeded the project are in [`plan/SEED.md`](plan/SEED.md).
