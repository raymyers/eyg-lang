# EYG operational semantics

A formal operational semantics for EYG in Lean, in three layers that are proved
to coincide:

1. a **functional big-step** (FBS) interpreter — fuel-indexed, total, executable
   (`FunctionalBigStep.lean`, Milestone S1);
2. a **labelled transition system** (LTS) over the CEK configuration, reflected
   into `cslib` (`Lts.lean`, Milestone S2);
3. a proof that both agree with the executable `partial def` interpreter in
   `Eyg.Interpreter.State` (Milestone S5).

The "why" — why big-step-over-stores is the wrong ground truth for EYG, why a
*trace* (not a final value) is the observation, and why a value *relation* will
eventually be needed — is in `lean/plan/eyg-difference-semantics.md`. The
constructive plan is `lean/plan/eyg-semantics.md`.

## The model (Milestone S0)

| Concept   | Definition                              | cslib counterpart                         |
| --------- | --------------------------------------- | ----------------------------------------- |
| State     | `Config = Control × Env × Stack`        | the `State` of `LTS State Label`          |
| Label     | `tau \| perform op lift \| reply op v`  | the `Label` of `LTS State Label`          |
| Step      | `Step : Config → Label → Config → Prop` | `LTS.Tr` (S2)                             |
| Multistep | trace `List Label` between configs      | `LTS.MTr` (S2)                            |
| Outcome   | `value v \| crash reason`               | terminal-state predicates (S2)            |
| Divergence| `∀ fuel, eval fuel cfg = timeout`       | `OmegaSequence` ω-trace (S4)              |

**State = the CEK machine.** The LTS state is the interpreter's machine state,
so the semantics and the implementation share one step function. Concretely it
is `MState = run Config | wait op env k`: a running `Config = Control × Env ×
Stack`, plus a `wait` variant for a machine suspended at an unhandled effect
(needed because separate `perform`/`reply` labels require a state *between* the
request and its reply). Environments eliminate substitution, so there are no
capture-avoidance lemmas.

**Source terms are closed, linked core terms.** `import`/`#CID` references are
resolved by a prior linking phase; `ContentReference`/`ReleaseReference`/
`RelativeReference` nodes are therefore `crash` outcomes here, not steps.

### Label shape decision: separate `perform`/`reply` (not fused)

We observe effects as two distinct events — a `perform op lift` when an effect
reaches the boundary, and a later `reply op v` when the runner feeds a value
back — rather than a single fused `effect op lift reply`. Reasons:

* It matches the interpreter harness's two-phase protocol: `execute` breaks at
  an unhandled `perform`, and `resume` feeds a reply back. The trace is exactly
  the interleaving the harness already produces.
* **Divergence** (S4) must be able to observe a `perform` that never receives a
  `reply` (a server looping on effects forever). A fused label cannot express an
  unanswered request.
* Pure machine moves carry `tau`; the observable trace is the
  `perform`/`reply` subsequence (`Label.observable` erases the `tau`s).

## Totality without a type system

Ill-formed applications reduce to a `crash` outcome rather than getting stuck,
so the step relation is total. `crash` (including `Vacant`) is a first-class
observable from day one — row typing is postponed (difference-doc §"lightweight
middle ground").

## Status

* **S0 — frame & scope:** done. `Config`, `Label`, `Outcome` fixed
  (`Basic.lean`); Label shape decided; model mapped onto cslib (this file).
* **S1 — functional big-step:** `eval`/`run` executable
  (`FunctionalBigStep.lean`); fuel-monotonicity proved (`eval_mono`,
  `eval_timeout_antitone`); `FBS≡interpreter` cross-checked on all 104 spec
  fixtures via `lake exe spec`. Remaining: the general agreement *proof*
  (`eval_agrees_execute_value`, currently a stub — Milestone S5).
* **S2 — the LTS:** `eygLTS : LTS MState Label` defined over `step`
  (`Lts.lean`); `progress`/`not_stuck` proved; `HasTau` instance wired.
  The LTS state is `MState = run Config | wait op env k` (the `wait` variant is
  the suspended machine awaiting a reply — needed for separate `perform`/`reply`
  labels).
* **S3 — FBS ⟷ LTS:** `Correspondence.lean`. `instDeterministic`;
  `eval_sound_done`/`eval_sound_effect` (observable trace = emitted events);
  `eval_complete` (silent runs); `eval_iff_mtr` characterization.
* **S4 — behaviour & divergence:** `Behavior.lean`. `Behaviors cfg`
  (terminating trace+outcome, or divergent ω-trace); `outcome_unique`;
  `tauDiverges_iff_timeout` (both directions — internal divergence ⟺ `eval`
  times out at every fuel).
* **S5–S6:** see `lean/plan/eyg-semantics.md`.
