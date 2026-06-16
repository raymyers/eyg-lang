---
name: eyg-type-soundness-plan
description: Plan to prove EYG type soundness (Progress + Preservation, incl. row & effect safety) in Lean, over a transparent reduction relation for the CEK machine, against the gleam_analysis reference type system
date: 2026-06-16
---

# EYG Type Soundness in Lean — Implementation Plan

## Goal

Prove **type soundness** for EYG in Lean: a well-typed closed program never
"goes wrong". Concretely, the two classical theorems plus the EYG-specific
effect-safety strengthening:

1. **Preservation** — if a configuration is well-typed at `τ ! ε` (type `τ`,
   effect row `ε`) and it steps, the successor is well-typed at the same type
   and a compatible effect row; and any effect *label* emitted by the step is a
   member of `ε`.
2. **Progress** — a well-typed configuration is either a value, *suspended on an
   effect that its row permits*, or can take a step that is **not** a `crash`.
3. **Soundness corollary (the EYG-meaningful statement).** Because the existing
   semantics is already *total* (ill-formed terms reduce to a `crash` outcome
   rather than getting stuck — see `eyg-semantics.md` §"Totality without a type
   system"), the substance of soundness here is: **a well-typed program's
   `Behaviors` never contain a `crash` outcome, and every `perform` it emits is
   in its declared effect row.** Equivalently, `eval` never returns
   `.done (.crash _)` for a well-typed term.

This turns the untyped `progress`/`not_stuck` already proved in `Lts.lean`
(every state is `Terminated` or steps) into the *typed* statement that the
terminal outcome of a well-typed program is never one of the crash reasons
(`Vacant`, `NotAFunction`, `NoMatch`, `MissingField`, `UndefinedVariable`,
`IncorrectTerm`, `UndefinedBuiltin`, …) and that unhandled effects only escape
when the type's effect row is non-empty.

## What we have (reference material — all in-repo)

The authoritative EYG type system already exists as the gleam analysis package
and is the specification we mirror:

- `packages/gleam_analysis/src/eyg/analysis/type_/isomorphic.gleam` — the **type
  representation**: `Var | Fun(arg, eff, ret) | Binary | Integer | String |
  List | Record(row) | Union(row) | Empty | RowExtend(label, field, tail) |
  EffectExtend(label, #(lift, reply), tail) | Never | Promise`. Note the arrow
  `Fun` carries an **effect row** as its middle component, and records/unions/
  effects are all **rows** (`Empty`/`RowExtend`/`EffectExtend`).
- `.../inference/levels_j/contextual.gleam` — **the typing rules per IR node**
  (`do_infer`), the **builtin type schemes** (`builtins()`), and the primitive
  schemes for `Cons`/`Extend`/`Select`/`Overwrite`/`Tag`/`Case`/`NoCases`/
  `Perform`/`Handle`. This is the rule-by-rule spec for the Lean typing judgment.
- `.../type_/binding.gleam` — `Mono`/`Poly`, `gen`/`instantiate`/`resolve`:
  let-generalization (with **effect-safe** generalization — `close`/`close_eff`
  only generalize effect tails that don't escape) and instantiation.
- `.../type_/binding/unify.gleam` — `rewrite_row`/`rewrite_effect`: rows unify
  **up to commuting distinct labels** (Rémy/Leijen scoped-row equality). This is
  the row-equivalence relation our declarative judgment must build in.

And the dynamics we are proving sound:

- `Eyg/Semantics/Basic.lean` (`Config`, `Label`, `Outcome`), `Lts.lean`
  (`MState`, `Step`, `eygLTS`, the untyped `progress`/`not_stuck`),
  `Behavior.lean` (`Behaviors`), `Correspondence.lean` (`instDeterministic`,
  `eval_iff_mtr`), `FunctionalBigStep.lean` (`eval`/`run`).
- `Eyg/Interpreter/{Value,Break,State}.lean` — `Value`, `Reason` (the crash
  outcomes a type system must exclude), and the machine `step`.

### External references (summarized in `references/`)

The relevant literature has been retrieved and distilled into
`lean/plan/references/` — read these before the milestone they back:

- [`references/progress-preservation-recipe.md`](./references/progress-preservation-recipe.md)
  — Wright–Felleisen / TAPL / Software Foundations syntactic-soundness skeleton,
  the lemma DAG, and how to phrase soundness for a **total/crash** semantics.
  Backs the `progress`/`preservation` shape used in every slice (T3–T7) and the
  de Bruijn binder decision (T1).
- [`references/row-types-scoped-labels.md`](./references/row-types-scoped-labels.md)
  — Leijen, *Extensible Records with Scoped Labels*: the exact row-equality rules
  (`eq-swap`/`eq-head`) and `rewrite_row` (Fig. 3) that EYG's `RowEquiv` mirrors,
  plus a normalization (stable-sort) decision-procedure tip. Backs **T1**.
- [`references/algebraic-effects-handlers-soundness.md`](./references/algebraic-effects-handlers-soundness.md)
  — Koka / Links / Frank / Eff / Wrocław type-and-effect soundness: effect-row
  threading, `perform`/`handle` rules, handler-frame + resumption typing, the
  deep/shallow flag, and the effect-safety statement. Backs **T5** (and the
  effect-safety corollaries in **T7**).
- [`references/abstract-machine-type-soundness.md`](./references/abstract-machine-type-soundness.md)
  — CEK / typed-continuation soundness: continuation-stack typing as an
  **answer-type transformer** (`K : A ⇒ B`), closure/environment typing that
  replaces the substitution lemma, and why the step relation must be a transparent
  inductive. Backs **T0** and the runtime-typing definitions introduced in **T3**
  (`StackWf`/`EnvWf`/`HasTypeV`).

Key cross-cutting findings from the survey:
- **No published Lean (or confirmed Coq/Agda) mechanization of syntactic
  progress+preservation for a row-based handler calculus exists** — EYG's proof
  would be novel. Closest templates: Eff (Twelf, set-based dirt), Wrocław-2018 &
  Hazel/Tes (Coq/Iris, semantic), PEPM-2024 (intrinsically-typed Agda machine).
- The machine-soundness sources type the configuration via **simulation against a
  typed contextual semantics**, *not* by typing the CEK frames directly — so
  typing EYG's `Delimit`/`Resume` frames (T5) is the genuinely novel obligation;
  PEPM-2024's intrinsic-typing style is the nearest precedent. A lower-risk
  alternative is the simulation route (don't type the machine config; prove it
  simulates a typed contextual/`Reduce` semantics) — this is the explicit T5 fork.

## ⚠️ Central architectural constraint (must be resolved in T0)

**Preservation cannot be proved about the existing `step`.** The interpreter's
machine (`eval`/`apply`/`call`/`callBuiltin`/`doPerform`/…) is `partial def`, so
`step c e k` is **kernel-opaque and irreducible** — see
`progress/2026-06-16-partial-def-irreducibility.md`. Every existing metatheory
proof works *abstractly* (`cases h : step c e k`, relate whatever it returns) and
never needs to know **what** `step` computes. Preservation is different: proving
"applying a closure extends the env with the argument", "`Select l` on a record
returns field `l`", "a handler frame discharges effect `l` from the row" requires
the *actual reduction behavior* of each rule. An opaque `step` makes this
impossible at the kernel level (the same wall that precluded a kernel
`interpreter_eq_fbs` in S5).

So T0 must furnish a **transparent reduction relation** with explicit, reducible
rules. Recommended approach (decided in T0, see Open Questions):

> Define `inductive Reduce : MState m → Label m → MState m → Prop` with **one
> explicit constructor per CEK reduction rule**, transcribed from `state.gleam` /
> the Lean `step` match arms (still environment-based — no substitution, no
> capture-avoidance). Soundness is proved over `Reduce`. `Reduce` is then cross-checked
> to agree with the opaque `step`/`eval` **executably** on every `spec/` fixture
> (the proven-by-testing bridge already used for `FBS≡interpreter: 104/104`), so
> the relation we reason about and the machine we run stay in lockstep without a
> kernel equation lemma for `partial def`.

This keeps the CEK/environment model (the whole reason substitution lemmas were
avoided) while making preservation provable.

## Core modeling choices

- **Declarative, not algorithmic.** We define a *declarative* typing judgment
  (relation) and prove the dynamics sound against it. We do **not** prove
  algorithm-J inference (`contextual.gleam`) sound/complete — that is a separate
  project (sketched as the T8 stretch). The judgment's rules and schemes are
  transcribed from `do_infer`/`builtins()` so "well-typed" means the same thing.
- **Rows up to reordering.** Record/union/effect rows are equal up to permutation
  of *distinct* labels (mirroring `rewrite_row`/`rewrite_effect`). Typing carries
  an explicit `RowEquiv` relation rather than syntactic equality.
- **Effect rows on the arrow.** Function types are `Fun arg ε ret`; the typing
  judgment threads an ambient effect row `ε`. `Perform l` adds `l` to the row;
  `Handle l` discharges it. Soundness includes **effect safety**: emitted
  `perform` labels are in the ambient row.
- **Crashes = the "stuck" states.** There is no separate stuck predicate to add;
  the crash `Outcome`/`Reason`s already *are* the failures. Soundness =
  "well-typed ⇒ outcome is never `crash`".
- **Closed, linked terms.** As in `eyg-semantics.md`: reference nodes
  (`ContentReference`/`ReleaseReference`/`RelativeReference`) are out of scope
  (they crash); the theorem is about closed, linked core terms. References can be
  admitted later via a `refs : Cid → Poly` typing context (mirroring
  `Context.refs`), tracked as a stretch.

---

## Plan structure: vertical slices, not horizontal layers

This is research-grade work with **no existing Lean/Coq/Agda mechanization of
row-based handler soundness to copy** (see `references/`). To avoid a big-bang
integration where no theorem is green until the end, the milestones are
**vertical slices of the language**, each delivering a *complete, sorry-free
`progress` + `preservation` + no-crash result for a growing fragment*:

```
T0  substrate        →  T1 types/rows  →  T2 schemes/builtins   (foundations)
T3  PURE CORE         (functions, let, literals; ε pinned to empty)   ← first green theorem
T4  + records/unions/rows
T5  + effects & handlers   (the novel part; effect safety)
T6  + let-polymorphism & full builtin table   (full language)
T7  packaging & corollaries     T8  stretch
```

Two rules keep the slices cheap to grow:

1. **Fix all judgment signatures once, in T3** — `HasType`/`HasTypeV`/`EnvWf`/
   `StackWf`/`MStateWf` carry the effect row *from the start* (pinned to `empty`
   in T3). Later slices **add constructors/cases**, never re-type the judgments,
   so `preservation`/`progress` proofs extend by new cases rather than rewrites.
2. **Define the full `Ty` and the canonical reduction `Reduce` up front** (T0/T1);
   slices just start *using* the record/union/effect constructors.

### What the kernel soundness theorem is actually *about* (important)

The shipped artifacts — `eval`, `eygLTS`/`Step`, `Behaviors` — are all built on
the **opaque `partial def` `step`**, so a kernel theorem cannot compute through
them (the S5 wall). Therefore **`Reduce` is the canonical object of the soundness
theorem**: T0 also gives `Reduce` its own observable layer (`BehaviorsR`, a
fueled `evalR`), and *all* of `preservation`/`progress`/`soundness` are stated
and kernel-proved over `Reduce`/`BehaviorsR`. The link from `Reduce` to the shipped
opaque `eval`/`Behaviors` is **executable agreement only** (the S5-style
`Reduce≡step` test on every fixture), never a kernel equality. This is honest and
sufficient — the soundness result is a real kernel theorem about a semantics
that is *executably identical* to the interpreter — but the plan must not claim a
kernel `eval`-level corollary, which the opaque `step` precludes.

---

## Milestone T0 — Transparent substrate `Reduce` + its observable layer

**Deliverable:** `Eyg/Semantics/Reduction.lean` — an explicit, reducible
relational CEK step `Reduce`, a `Reduce`-based fueled evaluator `evalR` and behaviour
set `BehaviorsR`, and an executable cross-check that `Reduce` agrees with the opaque
`step`/`eval`. A progress note records the decision.

- [x] `inductive Reduce : MState m → Label m → MState m → Prop` with **transparent,
      reducible** rules covering every reduction (var lookup, lambda→closure, apply
      push/pop, let, the `Switch` primitives `Cons`/`Extend`/`Overwrite`/`Select`/
      `Tag`/`Match`/`NoCases`, `Perform`, `Handle`/`Delimit`, `Resume`, builtin
      saturation), transcribed from `state.gleam` / the Lean `step` arms. Pure
      moves carry `.tau`; the effect boundary emits `.perform`; resuming a `wait`
      emits `.reply`. Environment-based — no substitution. **DELIVERED** in
      `Eyg/Semantics/Reduction.lean` via a single transparent *function*
      `reduce1Run : Config → ReduceStep` (each internal `call f x` re-expressed as
      an intermediate `Apply`-frame state, so no `partial` recursion survives);
      `Reduce` is defined from it. ⇒ determinism is `rfl` and inversion is
      `cases h : reduce1Run cfg`. **Deviation:** `Reduce` is finer-grained than
      `step` (a `Match`/`fix`/`deep` move = two `Reduce` steps), so agreement is at
      the observable-outcome level, not one-step-to-one-step — see
      `progress/2026-06-16-T0-transparent-reduce-substrate.md`.
- [~] **`Reduce`-based observable layer**: `evalR : Nat → Config m → Result`
      (fuel-structural, reuses FBS `Result`) **DELIVERED** (+ `runR` for an effect
      oracle). `BehaviorsR : Config m → Set Behavior` (the `MTr`-over-`Reduce`
      mirror of S4 `Behaviors`) is **deferred** to the next T0 slice — it is what
      T7 concludes about.
- [x] **`Reduce` is deterministic** (`reduce_run_det`) and total in the untyped
      sense (`progressR`: every state is a crash/value terminal or has a `Reduce`
      move). Both green, axioms clean.
- [~] **Executable agreement** `Reduce ≈ step`: enforced at **build time** via
      `#guard`s comparing `evalR`/`runR` outcomes to FBS `eval`/`run` on the
      fixture battery (a failure fails `lake build`). The dedicated `lake exe spec`
      `Reduce≡step: N/N` reporting line is **deferred** (mechanical; mirror
      `fbsAgreesInterp`). This is by design not a kernel theorem (opaque
      `partial def`).

## Milestone T1 — Type language & row equivalence

**Deliverable:** `Eyg/Types/Ty.lean` — the **full** EYG type language (records,
unions, effects all present) and a *decidable* row-equivalence.

- [x] `inductive Ty` mirroring `isomorphic.Type`: `var`, `fun (arg eff ret)`,
      `binary`, `integer`, `string`, `list`, `record (row)`, `union (row)`,
      `empty`, `rowExtend (label) (field) (tail)`,
      `effectExtend (label) (lift) (reply) (tail)`, `never`, `promise`.
      **Type variables: de Bruijn** (`Ty.var : Nat → Ty`); `deriving DecidableEq`.
      **DELIVERED** in `Eyg/Types/Ty.lean`.
- [x] Smart constructors: `unit = record empty`, `boolean`, `result`, `option`,
      `rows`, `record'`, `union'` (mirror `isomorphic.gleam`). **DELIVERED.**
- [~] **Row well-formedness / kinding** `Ty.WfRow`/`Ty.WfEff` — **deferred** to T1b
      (introduce alongside the typing judgment in T3, where value-row vs. effect-row
      kinding is actually consumed). Keep minimal.
- [x] **`RowEquiv` / `EffEquiv`** = Leijen's row equality — **DELIVERED** as
      `TyEquiv` (the congruence closure of `refl`/`symm`/`trans`, per-constructor
      congruence incl. `eq-head` `congrRow`/`congrEff`, and `swapRow`/`swapEff` with
      the load-bearing `l ≠ l'` guard). `tyEquiv_equivalence : Equivalence TyEquiv`
      (axiom-free); `RowEquiv`/`EffEquiv` are aliases. **The stable-sort
      `normalizeRow` + `RowEquiv ↔ normalizeRow r = normalizeRow s` decidability is
      the T1b follow-up** — the declarative soundness proof needs only the relation
      and its equivalence laws (decidability is for the algorithmic layer, T8).
- [ ] Reconcile with the interpreter's **canonical (sorted, unique-key) records**
      (`recordInsert`/`mkRecord`): a lemma that a sorted field list realizes a row
      `RowEquiv`-equal to any permutation — the hinge for `Select`/`Extend`/
      `Overwrite` preservation in T4. *(With the normalization route this is nearly
      immediate: dynamic records are already in normal form.)*

## Milestone T2 — Schemes, instantiation, builtin table

**Deliverable:** `Eyg/Types/Scheme.lean` — type substitution, instantiation, and
the primitive/builtin scheme tables.

- [x] Type substitution `Ty.subst` (into rows/effect rows) + lemmas
      (`subst_subst` compositionality, `subst_id`, and `subst_tyEquiv` =
      `subst` commutes with `RowEquiv`). **DELIVERED** in `Eyg/Types/Scheme.lean`.
      Capture-free by construction (`Ty` has no internal binders).
- [x] `Scheme` (∀-quantified `Ty`) with `instantiate : Scheme → List Ty → Ty`
      (de Bruijn open) mirroring `binding.instantiate`. **DELIVERED** (`Scheme.mono`
      for monomorphic). **`gen` (generalization) deferred to T6** as planned.
- [~] **Primitive schemes** (`cons`/`extend`/`select`/`tag`/`case_`/`perform`/
      `handle`…): **deferred** — introduced per slice that consumes them (data in
      T4, effects in T5), as the plan directs.
- [x] **Builtin scheme table** `Builtins.scheme` from `builtins()` — the T3
      arithmetic/string/core subset (`equal`, `fix`, `int_*`, `string_*`).
      **DELIVERED**; grow per slice; complete in T6.

## Milestone T3 — Slice 1: pure monomorphic core (first green theorem)

**Deliverable:** `Eyg/Types/Typing.lean` + `Eyg/Types/Runtime.lean` +
`Eyg/Types/Soundness.lean` — the **full judgment signatures** plus the rules for
the pure fragment, and a complete `progress`+`preservation`+`soundness` for it.
**This milestone proves the entire pipeline end-to-end before any hard feature.**

- [x] `HasType : Ctx → Node m → Ty → Ty → Prop` (env, term, type, **effect row** —
      present now; pure-core terms typeable at any `ε`, pinned to `empty` in the
      soundness statement), `Ctx = List (String × Scheme)`. **DELIVERED** in
      `Eyg/Types/Typing.lean` (T3a): rules `var`, `lam`, `app` (effect threading —
      the function's latent effect = ambient `ε`, per `do_infer`'s
      `unify(test_eff, eff)`), monomorphic `let_`, `int`/`str`/`bin`, `builtin`
      (instantiate `Builtins.scheme`), and the **`TyEquiv` conversion rule**.
      Sanity-typing `example`s for `(\x.x) 1`, `let`, `int_add 2 3`, value
      `ε`-generality, and a row-reorder conversion — all green.
- [ ] Runtime typing with **full signatures**: `HasTypeV : Value m → Ty → Prop`
      (literals, `Closure` via `EnvWf` + body typing — `references/abstract-
      machine-type-soundness.md` §3; `Partial` at its residual arrow), `EnvWf : Env
      m → Ctx → Prop` (lock-step) with the **lookup lemma** (replaces the
      substitution lemma), `StackWf : Stack m → (Ty × Ty) → (Ty × Ty) → Prop`
      (**continuation as answer-type transformer** `A ⇒ B`; the `Arg`/`Apply`/
      `Assign`/`CallWith` frames only in this slice), and `MStateWf : MState m → Ty
      → Ty → Prop`.
- [ ] **Canonical-forms lemmas** for the slice (arrow ⇒ `Closure`/saturatable
      `Partial`; `integer` ⇒ `.Integer`).
- [ ] `preservation` (`MStateWf s τ ε → Reduce s μ s' → MStateWf s' τ ε`) and
      `progress` (`MStateWf s τ ε → s.IsValue ∨ ∃ μ s', Reduce s μ s' ∧
      ¬ μ.IsCrashMove`) **over `Reduce`**, by `cases` on `Reduce`.
- [ ] **`soundness` over `BehaviorsR`** for the pure fragment: well-typed ⇒ never
      `crash`; terminal value has type `τ`. **Green, sorry-free, axioms clean.**
- [x] Sanity `example`s typing real fixtures (`(\x.x) 1 : integer`, an arithmetic
      term) — **DELIVERED** in T3a; optional `#guard` against `gleam_analysis`
      `type_at` deferred.

**T3 status:** the typing judgment (T3a) is green. The runtime-typing layer
(`HasTypeV`/`EnvWf`/`StackWf`/`MStateWf`), canonical-forms lemmas, and the
`preservation`/`progress`/`soundness` proofs are the next T3 sub-slices.

## Milestone T4 — Slice 2: records, unions, rows

**Deliverable:** extend the T3 files with structured data; re-green the theorems.

- [ ] Add typing rules (primitive schemes from T2) for `Empty`/`Extend`/`Select`/
      `Overwrite`/`Tag`/`Case`/`NoCases`/`Cons`/`Tail`, using `RowEquiv` on the row
      arguments.
- [ ] Extend `HasTypeV` (`Record` fields realize a record row via the T1 sorted-row
      hinge; `Tagged l v` inhabits a union row containing `l`; `LinkedList`) and the
      canonical-forms lemmas (record row ⇒ `.Record`; union row ⇒ `.Tagged`).
- [ ] Extend `preservation`/`progress` with the new `Reduce` cases — `Select l` on a
      record returns field `l` (no `MissingField`), `Case` matches a present tag
      (no `NoMatch`). Re-green `soundness` for the data fragment.

## Milestone T5 — Slice 3: effects & handlers (the novel part)

**Deliverable:** effect-row threading and handler soundness; **effect safety**.
This is the milestone with no direct mechanization precedent — see the fork below.

- [ ] **Un-pin the effect row.** Add typing rules `Perform` (singleton-row arrow
      `Fun(a, EffectExtend(l,(a,b),Empty), b)` — Koka's "operation as Var" trick,
      `references/algebraic-effects-handlers-soundness.md` §2) and `Handle`
      (input `EffectExtend(l,(a,b),tail)` → output `tail`; `l` discharged; all of
      `Σ(l)` handled; bind `resume`), with the `shallow : Bool` flag flipping the
      resumption's codomain row (deep = discharged `tail`; shallow = undischarged).
- [ ] **DECISION (fork, resolve at the top of T5):** typing the CEK `Delimit`/
      `Resume` frames directly has **no precedent** (the literature types machines
      by *simulation* against a typed contextual semantics). Two routes:
      - *(a) Direct frame typing* — extend `StackWf` so a `Delimit` frame discharges
        an effect label from the row and `Resume` types the reified continuation.
        Reuses the existing machine; matches EYG's goal; highest novelty/risk.
      - *(b) Simulation fallback* — define a small contextual reduction with typed
        evaluation contexts (Koka/Links style), prove `progress`/`preservation`
        there (well-trodden: context typing + replacement lemma), then prove `Reduce`
        simulates it. Lower proof risk for the metatheory, but adds a second
        semantics + a simulation proof.
      **Recommendation:** attempt (a) for one effect first (it reuses everything);
      fall back to (b) if `Resume`/continuation typing stalls. T3/T4 already prove
      the pipeline, so this fork is isolated to the effect layer.
- [ ] **Effect safety in `preservation`:** if `μ = .perform op lift` then `op ∈ ε`
      (and `lift`/reply have the row's declared types). `wait op env k` typed so
      `op ∈ ε`.
- [ ] **`progress` with the effect escape clause:** a well-typed non-value is a
      value, *suspends on `op ∈ ε`*, or takes a non-crash step (no
      `UnhandledEffect` outside the row). Re-green `soundness` incl. effect safety.

## Milestone T6 — Slice 4: let-polymorphism & full builtins (full language)

**Deliverable:** the remaining generality; `progress`+`preservation`+`soundness`
for the **whole** core language.

- [ ] **Let-generalization** `gen` (deferred from T2), declaratively and
      **effect-safe** (only generalize effect tails that don't escape — mirror
      `close`/`close_eff`; Open Question #3). Extend the `Let` rule and re-green.
- [ ] **Complete the builtin scheme table** (`fix`, `list_fold`, `binary_fold`,
      all `string_*`/`int_*`, …) and the builtin-saturation preservation case
      (saturated builtin yields its scheme's return type, via `Reduce`'s explicit
      builtin rule).
- [ ] Full `soundness` re-green over `BehaviorsR` for the complete language.

## Milestone T7 — Packaging & corollaries

**Deliverable:** `Eyg/Types/Soundness.lean` — the headline statements + hygiene.

- [ ] `soundness : HasType [] prog τ ε → ∀ b ∈ BehaviorsR (Config.initial prog),
      b` is `terminates trace (value v)` with `HasTypeV v τ`, or
      `suspended`/`diverges` with **every** `perform op` in the trace satisfying
      `op ∈ ε`, and **never** `terminates _ (crash _)`. (T5/T6 preservation+progress
      folded over the trace + `outcome_unique`.)
- [ ] **Pure ⇒ effect-free** `pure_no_perform : HasType [] prog τ empty → …` the
      observable trace has no `perform` labels (Eff's `A!∅` purity certificate —
      `references/algebraic-effects-handlers-soundness.md` §4).
- [ ] **Executable transfer to the shipped interpreter** (not a kernel claim): the
      `Reduce≡step` fixture agreement (T0) means the soundness result holds *of the
      interpreter we actually run*. Document this exactly as S5 documents its
      bridge; do **not** state a kernel `eval`/`Behaviors`-level corollary.
- [ ] Axiom hygiene: `#print axioms soundness` clean (`propext`/`Classical.choice`/
      `Quot.sound` only); zero `sorry` across the project.

## Milestone T8 — Stretch: algorithmic soundness, references, value relation

**Deliverable:** none required for the core result; the on-ramp to a verified
checker / compiler.

- [ ] **Algorithmic soundness**: relate a Lean port of `contextual.do_infer` (or a
      `check : Node → Option (Ty × Ty)`) to `HasType` — "inference succeeds with
      `τ ! ε` ⟹ `HasType [] e τ ε`". Makes "the analyzer says OK" imply soundness;
      depends on porting `unify`. Large.
- [ ] **References / linking**: extend `Ctx` with `refs : Cid → Scheme`
      (mirroring `Context.refs`) so linked references type-check instead of crash.
- [ ] **Value relation** `V : Value → Value → Prop` (deferred S6 item): structural
      on data, behavioral/step-indexed on closures — the bridge to compiler
      correctness.

---

## Definition of done

- [ ] **T0:** transparent `Reduce` + `BehaviorsR`/`evalR`; `Reduce≡step` green on every
      fixture; the opaque-`partial def` blocker is resolved by reasoning over `Reduce`.
- [ ] **T1–T2:** full `Ty`; `RowEquiv`/`EffEquiv` proved an equivalence (and
      decidable via normalization); schemes + the builtin table.
- [ ] **T3 (the derisking checkpoint):** `progress`+`preservation`+`soundness`
      green and sorry-free for the **pure monomorphic core**, with the *final*
      judgment signatures (so later slices only add cases).
- [ ] **T4/T5/T6:** each re-greens `soundness` for its larger fragment — data,
      then effects+handlers (**incl. effect safety**: emitted `perform` ∈ row),
      then let-polymorphism + full builtins.
- [ ] **T7:** headline `soundness` over `BehaviorsR`; `pure_no_perform`; executable
      transfer to the interpreter documented (kernel claim stays at the `Reduce`
      level); axioms clean; zero `sorry`; `lake build` + `lake exe spec` green.

## Decisions made (baked into the milestones)

These were open in the first draft and are now resolved by the structure above —
recorded here so the rationale is not lost:

- **Reduction substrate = explicit relational `Reduce`** (T0), reasoned over for
  soundness; the bridge to the opaque `step` is executable, not kernel. (Re-founding
  `step` as a structural `def` with equation lemmas was the alternative — heavier,
  not justified.)
- **Type variables = de Bruijn** (T1) — canonical types, decidable equality, no
  α-renaming.
- **`RowEquiv` via stable-sort normalization** (T1) — yields decidability + the
  equivalence laws cheaply.
- **Monomorphic first, generalize in T6** (T2/T6) — slices T3–T5 use monomorphic
  `let` + polymorphic builtin/primitive schemes; let-generalization is added last.
- **Sequencing = vertical slices** (T3 pure → T4 data → T5 effects → T6 poly),
  each green before the next — the effect layer (no precedent) is isolated to T5.

## Open questions (still to settle)

1. **CEK frame typing vs. simulation, for effects** (decided at the top of T5).
   Direct `Delimit`/`Resume` frame typing (reuses the machine, novel) vs. a typed
   contextual semantics + a `Reduce`-simulates-it proof (well-trodden metatheory,
   second semantics). Recommendation: try direct for one effect, fall back to
   simulation if continuation typing stalls. This is the single largest remaining
   risk and the reason effects are their own slice.
2. **`Vacant` typing.** `do_infer` types `Vacant` at a fresh var but records an
   `Error` (the "todo/hole" node). It is *shape*-typeable yet its dynamic outcome
   is `crash (Vacant)`. Decide: **exclude `Vacant` from "well-typed"** (treat the
   recorded `Error` as not-well-typed — recommended, matches `do_infer`), or accept
   `crash Vacant` as the one sanctioned crash. Directly affects the no-crash
   statement; settle in T3 when the `HasType` rules are fixed.

## Do we have what we need? (answer to the prompt's question)

**Mostly yes — the type system is fully specified in-repo** (`gleam_analysis`),
so there is no need to invent the rules: types (`isomorphic.gleam`), per-node
typing + builtin schemes (`contextual.gleam`), generalization (`binding.gleam`),
and row equality (`unify.gleam`) are all there to transcribe. The dynamics, LTS,
`Behaviors`, and determinism are already built and proved.

**One real internal blocker, surfaced as T0:** the machine `step` is an opaque
`partial def`, so preservation cannot be proved about it directly — we must
reason over a transparent reduction relation and bridge to `step` executably.
This is the single most important thing to get right; everything downstream
assumes it.

**External references — retrieved and summarized in [`references/`](./references/):**
- [`references/row-types-scoped-labels.md`](./references/row-types-scoped-labels.md)
  — Leijen, *Extensible Records with Scoped Labels*: the exact row-equality
  (`eq-swap`/`rewrite_row`) model and its metatheory; the cleanest precedent for
  T1's `RowEquiv` (plus a stable-sort normalization tip for decidability).
- [`references/algebraic-effects-handlers-soundness.md`](./references/algebraic-effects-handlers-soundness.md)
  — Koka / Links / Frank / Eff / Wrocław metatheory: type-and-effect soundness for
  algebraic effects and handlers (T3 `Perform`/`Handle` rules, T4 handler-frame +
  resumption typing, the deep/shallow flag, T5/T6 effect safety).
- [`references/abstract-machine-type-soundness.md`](./references/abstract-machine-type-soundness.md)
  — CEK / typed-continuation soundness: the `StackWf` "continuation as answer-type
  transformer" pattern and closure/environment typing for T4 (and why T0's `Reduce`
  must be transparent).
- [`references/progress-preservation-recipe.md`](./references/progress-preservation-recipe.md)
  — Software-Foundations / Wright–Felleisen *Progress + Preservation* skeleton and
  lemma DAG; how to phrase soundness for a total/crash semantics. The EYG-specific
  deltas (rows, effects, environment-machine) are covered by the three above.

**What the survey changed in our confidence:** the in-repo `gleam_analysis` spec
remains sufficient for the *type system itself*, and the four summaries give
concrete, transcribable rule shapes for every milestone. Two cautions surfaced:
(1) **no existing Lean/Coq/Agda mechanization of row-based handler
progress+preservation** — EYG's would be novel, so budget accordingly; (2) typing
the CEK `Delimit`/`Resume` frames directly (T4) has **no direct precedent** (the
literature types machines by *simulation* against a typed contextual semantics) —
keep the simulation route as a fallback if direct frame-typing proves too costly.
Both are reflected in the milestones above.
