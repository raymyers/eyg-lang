---
date: 2026-06-16
milestone: T0
status: mostly-complete (BehaviorsR + spec-harness line deferred)
---

# T0 — Transparent reduction substrate `Reduce`

## What shipped

`Eyg/Semantics/Reduction.lean`: a transparent, kernel-reducible small-step
relation `Reduce`, its fueled observable evaluator `evalR` (+ `runR` for an
effect oracle), determinism, untyped progress, and an executable
`evalR ≡ FBS eval` cross-check on the fixture battery. Full `lake build` green,
`lake exe spec` still `104/104` + `FBS≡interpreter 104/104`. Axioms on
`progressR`/`reduce_run_det`/`evalR_succ` are the clean three
(`propext`/`Classical.choice`/`Quot.sound`); zero `sorry`.

## The key design decision (and its deviation from the plan)

The plan's T0 asked for `inductive Reduce` with "one explicit constructor per
reduction rule" agreeing with `step` **one-step-to-one-step**. The obstacle: a
single machine `step` does unbounded work — `Match` re-dispatches via `call
branch inner`, `fix`/`list_fold` re-`call`, `doPerform` walks the stack — which
is exactly why `eval`/`apply`/`call` are `partial`. Transcribing that recursion
into inductive constructors would reintroduce the opacity we are escaping.

**Resolution.** Use the identity

```
  call f x ann env k  ≡  step (.V x, env, (Kontinue.Apply f env, ann) :: k)
```

(stepping a value against an `Apply f` frame *is* `call f x`). Re-express every
internal `call f x` as an explicit intermediate machine state. The only residual
recursions (`doPerform`/`move`) are structural on the stack list, so they stay
ordinary total `def`s. The whole one-step relation then collapses to a single
**non-recursive, total, transparent function** `reduce1Run : Config →
ReduceStep`, and `Reduce` is defined from it. Payoffs:

- **Determinism is `rfl`-level** (`reduce_run_det`) — no 25-case proof.
- **Inversion = `cases h : reduce1Run cfg`**, which *computes* and exposes the
  successor's structure. This is precisely what preservation (T3+) needs and what
  the opaque `step` (and `Step` in `Lts.lean`) cannot give.

**Deviation:** `Reduce` is therefore *finer-grained* than `step` — a
`Match`/`fix`/`deep` move becomes two `Reduce` steps (via the intermediate
`Apply` state). So the cross-check is at the **observable-outcome** level
(`evalR` vs. `eval`), not one-`Reduce`-to-one-`step`. Each intermediate state is
a genuine machine configuration, so no behaviour is invented — only granularity
differs, and the multi-step outcome agreement is what soundness actually
consumes. This is a strictly better basis for the metatheory than the literal
plan text; the plan's intent ("reason over a transparent relation, bridge to the
opaque `step` executably") is fully honoured.

### Faithfulness note on the effect boundary

For an *unhandled* top-level `perform`, `reducePerform` reports
`.perform op lift env k` using `reduceCall`'s `(env, k)`. The stack `k` matches
the real machine's `Break` debug stack exactly; the env may differ from the
machine's recorded `envP`, but it is **observationally inert** — after a
`reply`, the resumed `(.V v, envP, kP)` immediately meets `kP`'s top frame, whose
own captured env drives the continuation (the config env is used only by
`Delimit`/`Trace`, which merely forward it). The `runR` oracle fixture
(`Get`→5 ⟶ 15) exercises and confirms this.

## Remaining T0 items (next slice)

1. **`BehaviorsR`** — the `Reduce`-based mirror of S4 `Behaviors` (an LTS `MTr`
   over `Reduce` + the `terminates`/`suspended`/`diverges` set). `evalR` is the
   fueled half; the coinductive/trace half is deferred. This is what T7 will
   ultimately conclude soundness over.
2. **Spec-harness `Reduce≡step: N/N` line** — the agreement is currently enforced
   at *build time* via `#guard`s (a failure fails `lake build`, which is strong).
   A dedicated `lake exe spec` reporting line, folding `runR` through each
   fixture's oracle like `fbsAgreesInterp` does, would mirror the existing
   reporting style. Low risk; mechanical.

Neither blocks T1 (type language) or the T3 derisking checkpoint, both of which
build on `reduce1Run`/`Reduce` as delivered.
