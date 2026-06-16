---
name: eyg-semantics-plan
description: Plan for EYG functional big-step semantics, wired into the cslib transition system, with traces and divergence
date: 2026-06-16
---

# EYG Formal Semantics in Lean — Implementation Plan

## Goal

Give EYG a **formal operational semantics** in Lean that:

1. is a **functional big-step** (FBS) interpreter in the CakeML/Owens style — a
   fuel-indexed definitional `eval`, total and executable, with divergence
   modeled as "times out at every fuel";
2. is reflected as a **labelled transition system (LTS)** using **cslib**
   (`Cslib.Foundations.Semantics.LTS`), so the observable behavior of a program
   is a *trace of effect events* plus an outcome — finite or infinite;
3. is proved **equivalent to the executable interpreter** from
   [`eyg-interpreter.md`](./eyg-interpreter.md), so the thing we test and the
   thing we reason about are the same artifact.

The rationale — why big-step-over-stores is the wrong ground truth for EYG, why
traces (not final values) are the observation, and why a value *relation* will
eventually be needed — is in
[`eyg-difference-semantics.md`](./eyg-difference-semantics.md). This plan is the
constructive version of that discussion.

## What cslib gives us

From the resolved dependency (`Cslib.Foundations.Semantics.*`):

- `LTS State Label` — a transition relation `Tr : State → Label → State → Prop`
  (`LTS/Basic.lean`).
- `LTS.MTr` — multistep transitions carrying a **trace** `List Label`, with
  `single/stepR/comp/split/nil_eq` and `IsExecution` lemmas already proved.
- `LTS.Deterministic`, `deterministic_imageFinite`, etc.
- `LTS/Bisimulation.lean`, `LTS/Simulation.lean`, `LTS/TraceEq.lean` — for
  stating and proving behavioral equivalence.
- `Foundations/Data/OmegaSequence/*` — infinite sequences, for **divergent**
  (infinite-trace) behaviors.
- `Foundations/Control/Monad/Free` (+ `Free/Effects`, `Free/Fold`) — a free
  monad with effect handling, as an optional denotational packaging.

## Core modeling choices

- **State of the LTS = the CEK machine configuration** reused from the
  interpreter: `Config := Control × Scope × Stack` (so the semantics stays
  recognizably close to the implementation — see difference-doc §"CEK as
  definitional semantics"). Environments eliminate substitution entirely: no
  capture-avoidance lemmas.
- **Label = effect event or silent step:**
  ```
  inductive Label
    | tau                                   -- internal reduction (no observation)
    | perform (op : String) (lift : Value)  -- effect raised to the boundary
    | reply   (op : String) (reply : Value) -- value fed back to the resumption
  ```
  Pure reduction steps are `tau`; the observable trace is the `perform`/`reply`
  subsequence. (A single fused `Label.effect op lift reply` is an alternative if
  we only ever observe matched request/response pairs — decide in S2.)
- **Outcome** (terminal states): `value v`, `crash reason` (`Vacant`,
  `NotAFunction`, `UnhandledEffect`, …), or non-termination. `crash` is a
  first-class observable from day one (difference-doc: `vacant` is a legitimate
  outcome).
- **Totality without a type system:** ill-formed applications reduce to a
  `crash` outcome rather than getting stuck, making the relation total — the
  lightweight middle ground from the difference-doc, postponing row typing.

---

## Milestone S0 — Frame & scope ✅

**Deliverable:** `Eyg/Semantics/README` fixing the model: `Config`, `Label`,
`Outcome`, and which cslib structures each maps onto. Agreement that source-side
terms are **closed, linked core terms** (`import`/`#CID` resolved by a prior
linking phase — difference-doc §"linking").

- [x] Model fixed in `Eyg/Semantics/Basic.lean` (`Config = Control × Env ×
      Stack`, `Label`, `Outcome`) and `Eyg/Semantics/README.md` (cslib mapping,
      linking assumption: reference nodes are `crash` outcomes).
- [~] Three theorems: `eval_agrees_execute_value` stub landed in
      `FunctionalBigStep.lean`. FBS↔LTS and `Deterministic` stubs deferred to
      S2 (they need `Step`/`eygLTS`, which don't exist yet).
- [x] Decide `Label` shape — **separate `perform`/`reply`** (not fused);
      rationale recorded in `Basic.lean` and `README.md` (harness two-phase
      protocol; divergence needs unanswered `perform`s).

## Milestone S1 — Functional big-step interpreter (total, executable)

**Deliverable:** `Eyg/Semantics/FunctionalBigStep.lean` — a fuel-indexed
`eval : Nat → Config → Result` that terminates, `#eval`s, and shares the step
rules with the interpreter.

- [x] `Result := done Outcome | timeout | effect (op) (lift) (resume : Value →
      Config)` — effects return a **resumption** (difference-doc §FBS), so the
      semantics is executable against an oracle/runner.
- [x] `eval (fuel+1) cfg` = one `step` then recurse; `eval 0 _ = timeout`.
      Reuses the interpreter's `step` from `State.lean` (so all step rules are
      shared). `#guard`s cross-check value/crash/timeout/effect cases.
- [x] `eval` is monotone in fuel: more fuel never changes a non-`timeout`
      result (`eval_succ_mono` for +1, `eval_mono` for `≤`). The workhorse lemma
      for everything downstream. Corollary `eval_timeout_antitone` (timeout is
      downward-closed in fuel) lands the S4 divergence handle early.
- [x] `run : Config → oracle → Result` iterates resumptions against a list of
      `(label, lift, reply)` replies (mirrors the spec harness's effect-folding);
      `#guard`ed on a resume-through-`Get` example.
- [x] Cross-check: on every `spec/` fixture, `run` agrees with the M6
      interpreter harness. Wired into `lake exe spec` (`fbsAgreesInterp`,
      `interpFinal`); reports `FBS≡interpreter: 104/104` and fails the run on any
      disagreement. A concrete instance of the S5 bridge over the whole suite.

## Milestone S2 — The EYG LTS in cslib ✅

**Deliverable:** `Eyg/Semantics/Lts.lean` defines `eygLTS : LTS MState Label`
and the terminal/outcome predicates.

- [x] `inductive Step : MState → Label → MState → Prop` from the CEK rules,
      defined *over* the interpreter's `step`: pure moves are `tau`; the effect
      boundary emits `perform op lift`; resuming emits `reply op v`.
- [x] `def eygLTS : LTS MState Label := ⟨Step⟩`, with `eygLTS_Tr` simp lemma and
      a `HasTau (Label m)` instance (τ = `tau`) for cslib's weak/divergence API.
- [x] Outcome predicates `MState.outcome?`/`Terminated`/`IsValue`/`IsCrash`;
      `progress` (every state is `Terminated` or steps) ⇒ `not_stuck` (cslib
      `Stuck` is empty for `eygLTS`). Proof cases on `step` abstractly.
- [x] `eygLTS.MTr` available for free (cslib); one-step `MTr` reply example.
- **State refinement:** the LTS state is `MState = run Config | wait op env k`,
  not bare `Config` — separate `perform`/`reply` labels need a suspended state.
  `wait` holds the captured resume context; rationale in `Lts.lean`.
- **Constraint:** `step` is `partial def`-backed ⇒ irreducible, so concrete
  `tau`/`perform` transitions can't use `rfl`. Does not block S3/S5 (proofs case
  on `step c e k` abstractly). See
  `progress/2026-06-16-partial-def-irreducibility.md`.

## Milestone S3 — FBS ⟷ LTS correspondence

**Deliverable:** the fueled interpreter and the relational LTS describe the same
finite executions.

- [x] `eval_sound_done` / `eval_sound_effect`: a finished `eval` (terminal
      outcome, or suspended at an effect) is mirrored by an `eygLTS.MTr` to a
      state with the same outcome / `wait`, and the **observable** trace is
      exactly the emitted events (`[]` for value/crash, `[perform op lift]` for
      an effect).
- [x] `eval_complete`: a `tau`-only multistep to a terminal state is realized by
      `eval` at some fuel (induction on `MTr`). Effectful runs belong to `run`,
      not bare `eval`, so completeness is stated for silent traces.
- [x] `Deterministic eygLTS`: `instDeterministic` in `Correspondence.lean`,
      via `cases h1 <;> cases h2 <;> simp_all` (`step` pins tau/perform; the
      label pins reply). Feeds cslib's `deterministic_imageFinite`.
- [x] `eval_iff_mtr`: `(∃ fuel, eval fuel cfg = done o) ↔ (silent MTr to a
      terminal state with outcome o)`, combining sound + complete (uniqueness via
      `instDeterministic`).

## Milestone S4 — Observable behavior: traces & divergence ✅

**Deliverable:** `Eyg/Semantics/Behavior.lean` defining `Behaviors cfg` as a
finite trace + outcome, or an infinite trace.

- [x] `Behavior := terminates (trace) (outcome) | diverges (ωSequence Label)`;
      `Behaviors : Config → Set Behavior` via `eygLTS.MTr` (finite) and
      `eygLTS.ωTr` (infinite).
- [x] `diverges` uses cslib `ωSequence` — an infinite run emitting an ω-trace,
      capturing effectful non-termination a big-step semantics can't express.
- [x] `outcome_unique`: the silent terminal outcome of a config is determined
      (via S3 `eval_iff_mtr` + `eval_mono`). (Full trace-singleton-ness not
      separately needed; outcome determinacy is the substantive part.)
- [x] Connect to FBS: `tauDiverges_iff_timeout` — `TauDiverges cfg ↔ ∀ fuel,
      eval fuel cfg = timeout`, **both directions** (backward builds the infinite
      `loopSucc` trajectory). `TauDiverges := eygLTS.Divergent (.run cfg)`.

## Milestone S5 — Interpreter ≡ semantics (the bridge theorem) ✅ (with caveat)

**Deliverable:** the executable `partial def` interpreter of
`eyg-interpreter.md` agrees with the total FBS semantics on all terminating
runs, and both agree with the LTS.

- [~] `interpreter_eq_fbs` as a **kernel theorem is precluded**: `execute` is
      `loop (step …)` with `loop` a `partial def` ⇒ logically opaque, no
      equational lemmas (`unfold loop` fails). The unprovable stub was removed;
      **no `sorry` remains** in the project. See
      `progress/2026-06-16-interpreter-bridge-partial-def.md`.
- [x] Interpreter↔FBS agreement is established **executably** over the trace
      (perform/reply oracle): `Spec.Harness.fbsAgreesInterp`, `FBS≡interpreter:
      104/104` via `lake exe spec` (S1). The testing-level analogue of
      `executeLemma`.
- [x] Tie the knot among the **total** artifacts (kernel-proved):
      `eval_done_mem_behaviors` / `eval_effect_mem_behaviors` /
      `timeout_mem_behaviors` in `Behavior.lean` give
      interpreter →(exec, 104/104)→ FBS →(proof)→ LTS (S3) →(proof)→
      Behaviors (S4).

## Milestone S6 — Metatheory & packaging (stretch — partial; rest tracked)

**Deliverable:** reusable equivalence machinery and the denotational option.
`Eyg/Semantics/Metatheory.lean` lands the free wins; the rest stays deferred as
the on-ramp to verified compilation.

- [ ] **Value relation** `V : Value → Value → Prop` (structural on
      records/variants/strings/ints, behavioral on closures) — *deferred by
      design* (sequencing notes): the genuinely new proof tool, only pays off
      with a compiler/target. The behavioural-closure case needs a step-indexed
      / coinductive definition.
- [x] Trace equivalence / bisimulation packaging via `LTS/TraceEq.lean`:
      `MStateTraceEq`, `mstateTraceEq_equiv`, and `mstate_traceEq_sim` (trace
      equivalence is a simulation, from `instDeterministic`). Determinism also
      gives `ImageFinite` for free.
- [ ] Optional denotational packaging via `Foundations/Control/Monad/Free` —
      deferred (optional).
- [x] **Shared builtin specification** — *satisfied by construction*: FBS
      `eval`/`run` drive the interpreter's `step` → `callBuiltin`/`Builtin.run`,
      so there is one builtin implementation shared by interpreter and FBS (and
      reusable by any future target). Exercised by `FBS≡interpreter: 104/104`.

## Milestone S7 — Review findings: crash / unhandled-effect coverage (unfinished)

Raised by the 2026-06-16 diff review (commits `8123d47f..3c66765c`). The core
development is sound — full build green, `lake exe spec` 104/104 + FBS agreement,
zero `sorry`, axioms clean (`propext`/`Classical.choice`/`Quot.sound` only). The
following are coverage/coherence gaps, all clustered on the **crash / unhandled
effect** path, not proof defects.

- [ ] **Crash-outcome conformance is untested against the spec.** All 104
      `spec/evaluation/*.json` fixtures expect a `value`; **none** expects a
      `break`/error, and every effect fixture supplies matching replies. So the
      `FBS≡interpreter: 104/104` cross-check never exercises the `eval`
      `.done (.crash reason)` branch, nor the `.effect ≡ .error UnhandledEffect`
      reconciliation case in `Spec.Harness.fbsAgreesInterp`. The harness *decoder*
      supports `break` expectations (`UndefinedVariable`/`UndefinedBuiltin`/
      `NotImplemented`→`Vacant`), but the authoritative suite has zero negative
      fixtures. Net: "matches the interpreter/spec on every fixture" currently
      means the **value path only**; crash agreement (FBS ↔ interpreter ↔ spec) is
      unverified. *Fix:* add negative fixtures (and an unhandled-effect-at-top-
      level fixture) upstream, or add dedicated `#guard`s cross-checking `eval`'s
      crash against `execute`'s error on the same term.

- [ ] **Doc vs. model: `UnhandledEffect` is documented as a crash but modeled as
      an open perform.** `Basic.lean` (`Outcome` doc) and `README.md` list
      "`UnhandledEffect` at top level" as a `crash` example, but the model never
      produces it: `eval` maps `UnhandledEffect` to `.effect` (suspended),
      `MState.outcome?` returns `none`, and the LTS lets a `wait` state `reply`
      with *any* value (an open-system reading). The interpreter `execute`, by
      contrast, returns `.error UnhandledEffect` — a closed crash. The two are
      reconciled only by the ad-hoc `fbsAgreesInterp` case, not at the `Behaviors`
      level. *Fix:* correct the docs and decide the intended reading (open
      boundary vs. closed top-level crash); they currently disagree.

- [ ] **`Behaviors` cannot classify a top-level unhandled effect; `eval_effect_
      mem_behaviors` is misnamed.** Unlike its siblings `eval_done_mem_behaviors`
      / `timeout_mem_behaviors` (which conclude `… ∈ Behaviors cfg`),
      `eval_effect_mem_behaviors` concludes an `MTr`-to-`wait`, *not* a
      `Behaviors` membership — because `Behavior` has only `terminates` and
      `diverges`, no constructor for "ends suspended at an unanswered effect." So
      the "tie the knot: interpreter → eval → Behaviors" claim has a hole exactly
      at the effect case. *Fix:* either add a `Behavior.suspended op lift`
      constructor (open reading) or fold a top-level unhandled effect into a
      `crash` outcome (closed reading), then rename/retarget the lemma so its name
      matches its conclusion.

---

## Definition of done

- [x] `eval` total + monotone (`eval_mono`); `eygLTS` defined on the CEK machine
      state (`MState`).
- [x] FBS↔LTS soundness/completeness (`eval_sound_done`/`eval_sound_effect`/
      `eval_complete`/`eval_iff_mtr`) and `Deterministic eygLTS` proved —
      **no `sorry` anywhere in the project**.
- [x] `Behaviors` covers value / crash / divergence, with divergence via
      `OmegaSequence`; `tauDiverges_iff_timeout` ties divergence to `eval`.
- [~] `interpreter_eq_fbs` over traces: a *kernel* theorem is precluded
      (`partial def loop` is opaque). Established **executably** instead
      (`FBS≡interpreter: 104/104`), with the proof-level knot tying the total
      artifacts (`eval` → `Behaviors` → LTS). Documented in
      `progress/2026-06-16-interpreter-bridge-partial-def.md`.
- [x] S6 on-ramp: TraceEq/bisimulation packaging + shared-builtin done; value
      relation and denotational packaging tracked as deferred.

**Status (2026-06-16): core plan S0–S5 complete; S6 partially landed with the
remainder tracked as the deliberately-deferred compiler on-ramp. Full build
green, `lake exe spec` green (104/104 fixtures + FBS agreement), zero `sorry`.**

## Sequencing notes

- S1–S3 are the critical path and are pure metatheory over the interpreter's
  step function — do them as soon as `State.lean` (interpreter M2/M5) is stable.
- S4 (divergence) depends only on S2/S3, not on builtins.
- S6's value relation is deliberately deferred: it is "the genuinely new proof
  machinery relative to IMP" and only pays off once a compiler/target enters the
  picture. Keep the semantics usable without it.
