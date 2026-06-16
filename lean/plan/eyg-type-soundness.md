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
  Backs the overall shape (T5/T6/T7) and the binder decision (T1).
- [`references/row-types-scoped-labels.md`](./references/row-types-scoped-labels.md)
  — Leijen, *Extensible Records with Scoped Labels*: the exact row-equality rules
  (`eq-swap`/`eq-head`) and `rewrite_row` (Fig. 3) that EYG's `RowEquiv` mirrors,
  plus a normalization (stable-sort) decision-procedure tip. Backs **T1**.
- [`references/algebraic-effects-handlers-soundness.md`](./references/algebraic-effects-handlers-soundness.md)
  — Koka / Links / Frank / Eff / Wrocław type-and-effect soundness: effect-row
  threading, `perform`/`handle` rules, handler-frame + resumption typing, the
  deep/shallow flag, and the effect-safety statement. Backs **T3/T4/T5/T6**.
- [`references/abstract-machine-type-soundness.md`](./references/abstract-machine-type-soundness.md)
  — CEK / typed-continuation soundness: continuation-stack typing as an
  **answer-type transformer** (`K : A ⇒ B`), closure/environment typing that
  replaces the substitution lemma, and why the step relation must be a transparent
  inductive. Backs **T0/T4**.

Key cross-cutting findings from the survey:
- **No published Lean (or confirmed Coq/Agda) mechanization of syntactic
  progress+preservation for a row-based handler calculus exists** — EYG's proof
  would be novel. Closest templates: Eff (Twelf, set-based dirt), Wrocław-2018 &
  Hazel/Tes (Coq/Iris, semantic), PEPM-2024 (intrinsically-typed Agda machine).
- The machine-soundness sources type the configuration via **simulation against a
  typed contextual semantics**, *not* by typing the CEK frames directly — so
  typing EYG's `Delimit`/`Resume` frames (T4) is the genuinely novel obligation;
  PEPM-2024's intrinsic-typing style is the nearest precedent. A lower-risk
  alternative is the simulation route (don't type the machine config; prove it
  simulates a typed contextual/`Red` semantics).

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

> Define `inductive Red : MState m → Label m → MState m → Prop` with **one
> explicit constructor per CEK reduction rule**, transcribed from `state.gleam` /
> the Lean `step` match arms (still environment-based — no substitution, no
> capture-avoidance). Soundness is proved over `Red`. `Red` is then cross-checked
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

## Milestone T0 — Reduction substrate: a transparent step

**Deliverable:** `Eyg/Semantics/Reduction.lean` — an explicit relational CEK
step `Red` that is reducible (so preservation is provable), plus a progress note
recording the decision, plus an executable cross-check that `Red` agrees with the
opaque `step`/`eval`.

- [ ] Decide and document the substrate (Open Question #1). Default: explicit
      relational `Red`, environment-based, transcribed from `step`.
- [ ] `inductive Red : MState m → Label m → MState m → Prop` with one constructor
      per reduction rule (var lookup, lambda→closure, apply push/pop, let, the
      `Switch` primitives `Cons`/`Extend`/`Overwrite`/`Select`/`Tag`/`Match`/
      `NoCases`, `Perform`, `Handle`/`Delimit`, `Resume`, builtin saturation).
      Pure moves carry `.tau`; the effect boundary emits `.perform`; resuming a
      `wait` emits `.reply` (same `Label` discipline as `Step`).
- [ ] **`Red` is deterministic** (`Red s μ s₁ → Red s μ' s₂ → …`) and total in the
      same sense as the untyped `progress` (no transparent stuck states except the
      crash ones). Reuse to re-derive `progress`/`not_stuck` for `Red`.
- [ ] Executable agreement `Red ≈ step`: a `#guard`/`lake exe spec` check that one
      `Red` step matches one `step` move on the spec fixtures (the S5-style
      proven-by-testing bridge). Report e.g. `Red≡step: N/N`.
- [ ] (Optional, if cheap) bridge `Red`↔`Step` where `Step`'s `step c e k = …`
      hypotheses can be discharged — at minimum keep both and reason over `Red`.

## Milestone T1 — Types, rows, and row equivalence

**Deliverable:** `Eyg/Types/Ty.lean` — the EYG type language and the row-
equivalence relation.

- [ ] `inductive Ty` mirroring `isomorphic.Type`: `var`, `fun (arg eff ret)`,
      `binary`, `integer`, `string`, `list`, `record (row)`, `union (row)`,
      `empty`, `rowExtend (label) (field) (tail)`,
      `effectExtend (label) (lift) (reply) (tail)`, `never`, `promise`. Decide
      type-variable representation (Open Question #2: de Bruijn vs. named-with-
      freshness). Recommend **de Bruijn / locally-nameless** for variables bound
      by type schemes to avoid α-renaming pain.
- [ ] Smart constructors / notation: `unit = record empty`, `boolean`,
      `result`, `option`, `rows`, `record`, `union` (mirror `isomorphic.gleam`).
- [ ] **Row well-formedness / kinding.** Distinguish *value rows* (under
      `record`/`union`) from *effect rows* (under `fun`'s middle slot /
      `effectExtend`). A predicate `Ty.WfRow`/`Ty.WfEff` ruling out e.g. an
      `effectExtend` inside a record row. Keep minimal — only what soundness needs.
- [ ] **`RowEquiv` / `EffEquiv`** — rows equal up to commuting *distinct* labels
      (the content of `rewrite_row`/`rewrite_effect`): reflexive, symmetric,
      transitive, congruent, and `rowExtend l₁ a (rowExtend l₂ b r) ≈
      rowExtend l₂ b (rowExtend l₁ a r)` when `l₁ ≠ l₂`. Prove it is an
      equivalence relation. This is the **new proof machinery** for soundness
      (analogous to, but heavier than, IMP's nothing).
- [ ] Reconcile with the interpreter's **canonical (sorted, unique-key) records**
      (`recordInsert`/`mkRecord`): a lemma that a sorted field list realizes a row
      that is `RowEquiv` to any permutation — the hinge between dynamic record
      values and row types in preservation for `Select`/`Extend`/`Overwrite`.

## Milestone T2 — Type schemes, substitution, instantiation

**Deliverable:** `Eyg/Types/Scheme.lean` — polymorphism and the primitive/builtin
scheme tables.

- [ ] Type substitution `Ty.subst` (mono and into rows/effect rows) with the
      standard lemmas (compositionality; substitution commutes with `RowEquiv`).
- [ ] `Scheme` (∀-quantified `Ty`) with `instantiate : Scheme → Ty` (fresh/de
      Bruijn open) mirroring `binding.instantiate`/`open`. Decide whether to model
      `gen` (generalization) declaratively (close over non-escaping vars) — Open
      Question #3 (value restriction / effect-safe generalization, cf.
      `close_eff`).
- [ ] **Primitive schemes** for every non-application node, transcribed from
      `contextual.gleam`'s `prim`/`cons`/`extend`/`overwrite`/`select`/`tag`/
      `case_`/`nocases`/`perform`/`handle`. These ARE the typing rules for those
      nodes.
- [ ] **Builtin scheme table** transcribed from `builtins()` (`int_add`, `equal`,
      `fix`, `list_fold`, `string_*`, …). One Lean table, used by both the typing
      judgment (T3) and the canonical-forms/preservation reasoning for builtin
      saturation (T5). Start with a representative subset; complete incrementally.

## Milestone T3 — Declarative typing judgment for terms

**Deliverable:** `Eyg/Types/Typing.lean` — `HasType`, one rule per IR node.

- [ ] `HasType : Ctx → Node m → Ty → Ty → Prop` (env, term, type, **effect row**),
      `Ctx = List (String × Scheme)`. One constructor per `Expr` arm, mirroring
      `do_infer`:
  - [ ] `Variable` (instantiate scheme from `Ctx`), `Lambda` (arrow with the
        body's effect row in the middle slot; the lambda *itself* is pure),
        `Apply` (function's effect row + argument's row + the latent arrow row all
        combine — read off `do_infer`'s effect threading carefully).
  - [ ] `Let` with generalization (per T2 decision), `Integer`/`String`/`Binary`,
        `Tail`/`Cons`/`Empty`/`Extend`/`Select`/`Overwrite`/`Tag`/`Case`/`NoCases`
        (via T2 primitive schemes), `Perform` (adds the effect to the row),
        `Handle` (discharges it), `Builtin` (via T2 table), `Vacant` (well-typed
        at any type but its dynamic outcome is a crash — see Open Question #5).
  - [ ] A **subsumption/conversion rule** allowing `RowEquiv`/`EffEquiv` rewriting
        of a derivation's type/row (so syntactic row order never blocks a rule).
- [ ] Sanity `example`s: type a handful of spec fixtures (`(\x.x) 1 : Integer`,
      a record `Select`, a `perform`/`handle` round-trip) by hand to validate the
      rules before building the heavy metatheory.
- [ ] (Cross-check, optional) `#guard` that the hand-typed fixtures' types agree
      with `gleam_analysis` `type_at`/`type_` output where a fixture exists.

## Milestone T4 — Semantic typing: values, environments, stacks, configs

**Deliverable:** `Eyg/Types/Runtime.lean` — typing of runtime artifacts and the
configuration-typing relation. This is the heart of CEK soundness.

- [ ] **Value typing** `HasTypeV : Value m → Ty → Prop`: `Integer:integer`, …,
      `Record` fields realize a record row (using the T1 sorted-row hinge),
      `Tagged l v` inhabits a union row containing `l`, `LinkedList` elements,
      and **`Closure param body env`** well-typed iff `body` is well-typed under
      `env`'s typing extended with `param` (ties to `HasType`).
- [ ] **`Partial switch applied`** typing: a partially-applied primitive/builtin
      is typed at the *residual* arrow of its scheme after consuming `applied`
      (canonical-forms input for `Apply` preservation).
- [ ] **Environment typing** `EnvWf : Env m → Ctx → Prop` (pointwise value typing
      against schemes).
- [ ] **Stack / continuation typing** `StackWf : Stack m → (Ty × Ty) → (Ty × Ty)
      → Prop` — a continuation is typed as a transformer from the *hole's* type+
      effect to the *answer's* type+effect. Crucially, a `Delimit`/handler frame
      **discharges** an effect label from the row (the effect-safety invariant),
      and `Resume`/`Arg`/`Apply`/`Assign`/`CallWith` frames thread types per the
      reduction rules. This is the subtlest definition in the project.
- [ ] **Configuration typing** `MStateWf : MState m → Ty → Ty → Prop` combining
      control (`E`/`V`), env, and stack so that the whole machine is well-typed at
      an answer type+row. `wait op env k` typed so that `op` is in the row.
- [ ] **Canonical forms lemmas**: a value of type `integer` is `.Integer _`; of a
      record row is `.Record` with those fields; of an arrow is a `Closure` or a
      saturatable `Partial`; of a union is `.Tagged`. These feed Progress.

## Milestone T5 — Preservation

**Deliverable:** `Eyg/Types/Preservation.lean`.

- [ ] `preservation : MStateWf s τ ε → Red s μ s' → MStateWf s' τ ε'` with
      `EffEquiv`/row-compatible `ε'` (effect row only shrinks or is preserved;
      `reply` consumes a pending effect). Induction on `Red` (transparent thanks
      to T0); each case uses the matching canonical-forms / scheme lemma.
- [ ] **Effect labelling**: if `μ = .perform op lift` then `op` is a member of
      `ε` (and `lift` has the row's declared lift type); if `μ = .reply op v` then
      `v` has the declared reply type. The effect-safety half of preservation.
- [ ] Builtin saturation case: applying a saturated builtin yields a value of the
      scheme's return type (uses `callBuiltin`'s behavior via `Red`'s explicit
      builtin rule, not the opaque `step`).
- [ ] Multistep corollary: `MStateWf` is invariant along `eygLTS.MTr`/`Red*`
      (fold preservation over the trace), and the observable trace's labels are
      all in the (evolving) effect row.

## Milestone T6 — Progress

**Deliverable:** `Eyg/Types/Progress.lean`.

- [ ] `progress_typed : MStateWf s τ ε → s.IsValue ∨ (suspended on op ∈ ε) ∨
      ∃ μ s', Red s μ s' ∧ ¬ μ.IsCrashMove`. Concretely: a well-typed
      non-value, non-suspended state can take a **non-crash** step. Via canonical
      forms (T4): the control + top frame always match a non-crash reduction rule.
- [ ] **No-crash corollary** `well_typed_not_crash : MStateWf s τ ε →
      ¬ s.IsCrash` — the headline. Each crash `Reason` (`NotAFunction`, `Vacant`,
      `NoMatch`, `MissingField`, `UndefinedVariable`, `IncorrectTerm`,
      `UndefinedBuiltin`) is shown unreachable from a well-typed state by
      canonical forms (e.g. `NotAFunction` needs a non-arrow in function position,
      excluded by canonical forms for arrows).
- [ ] **Unhandled-effect characterization**: a well-typed state suspends
      (`wait op …`) only when `op ∈ ε`; so a program typed with `ε = empty`
      (a `pure()` context, cf. `contextual.pure`) never suspends — it terminates
      with a value or diverges silently.

## Milestone T7 — Soundness over `Behaviors` (the payoff)

**Deliverable:** `Eyg/Types/Soundness.lean` — tie progress+preservation to the
S4 `Behaviors` and the S1 `eval`.

- [ ] `soundness : HasType [] prog τ ε → ∀ b ∈ Behaviors (Config.initial prog),
      b` is `terminates trace (value v)` with `HasTypeV v τ`, or
      `suspended/diverges` with **every** `perform op` in the trace satisfying
      `op ∈ ε` — and **never** `terminates _ (crash _)`. (Combine T5 multistep +
      T6 no-crash + `outcome_unique`.)
- [ ] `eval_well_typed_no_crash : HasType [] prog τ ε → ∀ fuel,
      eval fuel (Config.initial prog) ≠ .done (.crash _)` — the FBS-level
      restatement (via `eval_iff_mtr`/`eval_sound_done`), so the executable
      semantics also witnesses soundness.
- [ ] **Pure ⇒ effect-free** `pure_no_perform : HasType [] prog τ empty → …` the
      trace has no `perform` labels (specializing effect safety).
- [ ] Axiom hygiene: `#print axioms soundness` clean (`propext`/`Classical.choice`
      /`Quot.sound` only); zero `sorry`.

## Milestone T8 — Stretch: algorithmic soundness & value relation

**Deliverable:** none required for the core result; tracked as the on-ramp to a
verified type checker / compiler.

- [ ] **Algorithmic soundness**: relate a Lean port of `contextual.do_infer`
      (or a *checker* `check : Node → Option (Ty × Ty)`) to `HasType` — "if
      inference succeeds with `τ ! ε`, then `HasType [] e τ ε`". This is what makes
      "the analyzer says OK" imply soundness. Large; depends on porting `unify`.
- [ ] **References / linking**: extend `Ctx` with `refs : Cid → Scheme`
      (mirroring `Context.refs`) so linked content/release references type-check
      instead of crashing.
- [ ] **Value relation** `V : Value → Value → Prop` (the deferred S6 item):
      structural on data, behavioral/step-indexed on closures — the bridge to
      compiler correctness, where soundness of the source type system is a
      prerequisite.

---

## Definition of done

- [ ] A transparent reduction `Red` exists and is cross-checked against `step`
      executably (T0); the opaque-`partial def` blocker is resolved.
- [ ] `Ty`, `RowEquiv`/`EffEquiv` (proved an equivalence), schemes, and
      `HasType` (one rule per node, transcribed from `gleam_analysis`) are defined
      and validated on sample fixtures.
- [ ] `preservation` and `progress_typed` proved over `Red`, including
      **effect safety** (emitted `perform` labels ∈ the effect row).
- [ ] `well_typed_not_crash` and `soundness` (over `Behaviors`) proved; the
      `eval`-level restatement holds; pure programs emit no effects.
- [ ] No `sorry`; axioms clean; `lake build` + `lake exe spec` green (incl. any
      new `Red≡step` / typing cross-checks).

## Open questions / decisions to settle (mostly in T0–T2)

1. **Reduction substrate** (T0). Explicit relational `Red` (recommended) vs.
   re-founding `step` as a structural/fuel `def` with equation lemmas (heavier,
   but yields a *kernel* `Red ≈ step` instead of an executable one). The opaque
   `partial def step` cannot be used directly for preservation either way.
2. **Type-variable representation** (T1). De Bruijn / locally-nameless
   (recommended, no α-renaming) vs. named with a freshness side-condition (closer
   to `binding.gleam`'s integer keys).
3. **Generalization / value restriction** (T2/T3). EYG generalizes `let` only in
   effect-safe positions (`close`/`close_eff`). Decide how much of that to model
   declaratively, or whether to start with a **monomorphic core** (no `let`-poly,
   builtins still polymorphic via schemes) to land soundness sooner, then add
   generalization.
4. **Scope sequencing** — recommend proving soundness for a **pure core first**
   (functions, `let`, integers/strings, records+`Select`/`Extend`, unions+`Case`)
   with `ε = empty`, *then* adding effect rows + `Perform`/`Handle`/`Resume`.
   Effects (esp. handler-frame typing in T4 and effect safety in T5/T6) are the
   genuinely hard, novel part and benefit from a solid pure base.
5. **`Vacant` typing.** `do_infer` types `Vacant` at a fresh var with an `Error`
   (it is the "todo/hole" node). It is *well-typed* but its dynamic outcome is a
   `crash (Vacant)`. Decide: either exclude `Vacant` from "well-typed-and-
   runnable" (treat its typing error as not-well-typed — recommended, matches
   `do_infer` recording `Error`), or accept that `crash Vacant` is the one
   sanctioned crash. This choice directly affects the `well_typed_not_crash`
   statement.

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
  transformer" pattern and closure/environment typing for T4 (and why T0's `Red`
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
