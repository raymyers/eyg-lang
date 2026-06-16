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
      **T1b partial DELIVERED** (`Eyg/Types/TyEquivInv.lean`): head-shape invariance
      `tyEquiv_shape` + per-head inversion lemmas
      `tyEquiv_{fun,integer,string,binary,record,union}_inv` (what the T3
      preservation case split needs). Remaining: `normalize`/`normalizeRow` +
      `tyEquiv_iff` + decidability + component inversion (prerequisite for the
      `StackWf` conversion handling — see
      `progress/2026-06-16-T3c-preservation-design.md`).
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
- [~] Runtime typing with **full signatures**. **Value half DELIVERED** (T3b,
      `Eyg/Types/Runtime.lean`): `HasTypeV : Value m → Ty → Prop` (literals,
      `Closure` via `EnvWf` + body typing, `Partial` builtin at its residual arrow
      via `BuiltinPartialWf`), `EnvWf : Env m → Ctx → Prop` (lock-step) with the
      **`envwf_lookup` lemma** (replaces the substitution lemma). **Continuation
      half DELIVERED** (T3c-i, `Eyg/Types/Machine.lean`): `StackWf` (answer-type
      transformer, frames `nil`/`trace`/`assign`/`arg`/`applyf`/`callwith`) and
      `MStateWf` (control yields `τin`; stack carries it to `τ`; `wait` pinned to
      `False` until T5). `mStateWf_initial` bridges a well-typed program to its
      initial state. Signatures now **fixed** (plan rule 1).
- [x] **Canonical-forms lemmas** — **DELIVERED** (T3b): `canonical_integer`/
      `_string`/`_binary` (base ⇒ literal) and `canonical_arrow` (arrow ⇒ `Closure`
      or builtin `Partial`). Resting builtin partials are typed *only at arrows*, so
      the impossible cases drop out by index mismatch.
- [x] `preservation` (`MStateWf s τ ε → Reduce s μ s' → MStateWf s' τ ε`)
      **DELIVERED** in `Eyg/Types/Soundness.lean`, sorry-free, axioms clean, over the
      transparent `Reduce`. `reply` vacuous (`wait` untyped); `perform` impossible
      (`not_perform` — pure-core **effect safety**: no `HasTypeV` rule types a
      `Perform` partial, and `reduceCallBuiltin` never performs); `tau` splits into
      `preservation_E` (eval steps) and `preservation_V` (frame steps incl. the
      closure-application crux). The builtin **application/saturation** case is
      isolated behind the hypothesis `BuiltinAppPreserves` (the **T6** obligation:
      per-builtin `Builtin.run` typing; `int_add` may trap with `Unrepresentable`).
- [x] **`soundness_value` over `evalR`** — **DELIVERED** (T3c-iii), sorry-free,
      axioms clean: a well-typed config whose `evalR` terminates with a value yields
      a value of the answer type `τ` (type preserved through the whole run). Fuel
      induction over `preservation` + `reduce1Run_done_value_typed` (`StackWf.nil`
      pins `τ` at the empty stack; saturated builtins defer to `hsat`).
- [x] **`progress`** — **DELIVERED** (T3c-iii), sorry-free, axioms clean: a
      well-typed state steps (`.tau`), is a terminal value, or terminates with a
      *sanctioned* crash (`Unrepresentable`, `¬ Reason.IsBad`) — never a bad crash
      (`Vacant`/`NotAFunction`/`NoMatch`/`MissingField`/`UndefinedVariable`/
      `IncorrectTerm`/`UndefinedBuiltin`/…), never `.perform`. Uses
      `builtin_scheme_isBuiltin` (analyzer table ⊆ interpreter table), `envwf_lookup`
      (no `UndefinedVariable`), and the isolated T6 hypothesis `BuiltinAppNoBadCrash`.

**T3 is the green derisking checkpoint — DONE for the pure monomorphic core:**
`preservation` + `progress` + `soundness_value` over the transparent `Reduce`/
`evalR`, all sorry-free, axioms `propext`/`Classical.choice`/`Quot.sound`. A
well-typed pure-core program never goes wrong (no bad crash, no unhandled effect)
and its result is typed. The two T6 obligations are cleanly isolated as the
hypotheses `BuiltinAppPreserves` / `BuiltinAppNoBadCrash` (builtin saturation via
`Builtin.run`). The full judgment signatures are fixed, so T4/T5/T6 extend by
**adding constructors/cases**.
- [x] Sanity `example`s typing real fixtures (`(\x.x) 1 : integer`, an arithmetic
      term) — **DELIVERED** in T3a; optional `#guard` against `gleam_analysis`
      `type_at` deferred.

**T3 status:** judgment (T3a), runtime value typing + canonical forms (T3b),
continuation/state typing `StackWf`/`MStateWf` (T3c-i), and the `HasType`
generation/inversion lemmas (T3c-ii(a)) are all green and axiom-clean. **All
infrastructure preservation needs is now in place**, and the crux
closure-application case has been hand-validated against it. A key simplification
was found: convert the produced *value/result* type to the stack's exact expected
type (via `HasType.conv`/`HasTypeV.conv`), which removes the need for any
`stackWf_conv` or `StackWf.nil` change (and hence the normalization dependency).
The remaining work — write `preservation` (the `tau` split per the validated
recipe; `reply` vacuous; `perform` impossible), `progress`, `soundness` over
`evalR` — and the full recipe are in
`progress/2026-06-16-T3c-preservation-design.md`. Builtin **saturation** stays a
T6 obligation.

## Milestone T4 — Slice 2: records, unions, rows

**Deliverable:** extend the T3 files with structured data; re-green the theorems.

- [x] Add typing rules (primitive schemes from T2) for the data nodes. **`Empty`/
      `Tail` DELIVERED** (T4a) — value-producing, threaded green through the whole
      pipeline (`HasType.tail/empty`, `HasTypeV.listNil/recordNil`, `inv_tail/empty`,
      `preservation_E`/`progress` cases). **`Cons`/`Tag`/`Case`/`NoCases`/`Select`/
      `Extend`/`Overwrite` ALL DELIVERED — the full data fragment is done** — they
      produce `Partial`s and
      do the operation in `reduceCall`, so they need: (1) per-operator `HasType` rules
      (instantiate the `cons()/extend()/select()/…` schemes); (2) operator-`Partial`
      and result-value (`LinkedList`/`Record`/`Tagged`) `HasTypeV` cases; (3)
      **`canonical_arrow` extended** beyond `Closure ∨ Partial-Builtin` to the
      operator partials, and `preservation_V`'s function-value split updated to
      dispatch on the switch (the closure case is untouched; each operator's
      `reduceCall` arm proves its operation preserves); (4) the **sorted-record ↔ row
      reconciliation** (T1 deferred item) for `Extend`/`Select`/`Overwrite`. Suggested
      order: `Cons` (lists, no rows) → `Tag`/`Case`/`NoCases` (variants) →
      `Extend`/`Select`/`Overwrite` (records, needs the row reconciliation).
- [x] Extend `HasTypeV` and canonical forms. **DELIVERED:** `listNil`/`listCons` +
      `canonical_list`; `tagged` (union membership) + `partialTag`; `recordNil`;
      non-empty `Record` fields realize a record row via the lookup-based `record`
      (`hpres`/`hmatch`) + `canonical_record`/`record_get`; union-row ⇒ `.Tagged`
      (`canonical_union`) for `Case`.
- [x] Extend `preservation`/`progress` with the new `Reduce` cases. **DELIVERED:**
      the **list** (`Cons`), **variant** (`Tag`/`Case`/`NoCases`), and **record**
      (`Select`/`Extend`/`Overwrite`) fragments — all green through
      `preservation`+`progress`+`soundness_value`. `Case`
      (the row-reasoning crux) uses the `Eyg/Types/Row.lean` metatheory: HIT — the
      guarded (first-occurrence) `RowContains` forces the payload to type at the
      union's head; MISS — `tyEquiv_rowContains_mp` lands the tag in the tail and
      `rowContains_tyEquiv` surfaces it so the value re-types at `union tail` (no
      `NoMatch`). **Remaining:** the **record** ops `Select`/`Extend`/`Overwrite` —
      these need a record-value typing (`RecordWf`: sorted fields realize a row) and
      the sorted-record↔row reconciliation (the record analog of the variant row
      work, with the `recordInsert`/`recordGet` sorting). Re-green `soundness` for the
      full data fragment. **`Select` DELIVERED** via `RecordWf` + `recordWf_get` (no
      `MissingField`), `canonical_record`, `tyEquiv_recordRow`. **`Extend` DELIVERED**
      (T4c): `HasType.extend` (∀α r. α → {r} → {l:α|r}), `HasTypeV.partialExtendNil`/
      `partialExtendOne`, `inv_extend`, `recordInsert_get_eq`/`recordInsert_get_ne`,
      and the `preservation_V`/`progress` cases — green through
      `preservation`+`progress`+`soundness_value`. **The ⚠ FINDING is resolved:**
      `RecordWf` is **lookup/predicate-based** (`hpres`/`hmatch` over `recordGet`),
      so it is duplicate-collapsing by construction — the value `{l:new}` realizes
      the type `{l:new, l:old}` because both `recordGet` views agree on the visible
      first field (`recordInsert_get_eq`) and the tail row re-types via
      `tyEquiv_recordRow`/`tyEquiv_rowContains`. **`Overwrite` DELIVERED** (T4d): same
      shape as `Extend` (`HasType.overwrite`, `partialOverwriteNil`/`partialOverwriteOne`,
      `inv_overwrite`) but the input row already carries `l` (`{l:β|r}`), so the
      `reduceCall` `MissingField` trap is excluded exactly like `Select` (head
      `RowContains` ⇒ `record_get` ⇒ `recordGet fields l = some _`); the result re-types
      at `{l:α|r}` via the same `recordInsert_get_eq/ne` + tail `RowContains.tail`
      reasoning. **The entire T4 record/union/list data fragment is now green through
      `preservation`+`progress`+`soundness_value`, sorry-free, axioms clean.** Original
      finding recorded in `progress/2026-06-16-T4-row-machinery-boundary.md`.

## Milestone T5 — Slice 3: effects & handlers (the novel part)

**Deliverable:** effect-row threading and handler soundness; **effect safety**.
This is the milestone with no direct mechanization precedent — see the fork below.

- [x] **Effect-row metatheory** (`Eyg/Types/EffRow.lean`, T5a) — the effect analog
      of `Eyg/Types/Row.lean`: `EffContains eff l a b` (first-occurrence membership
      of operation `l : (lift a, reply b)` in an effect row), `tyEquiv_effContains`
      (`TyEquiv` preserves membership, lift/reply up to `TyEquiv`),
      `tyEquiv_effContains_mp`, and `effContains_tyEquiv` (surface a handled op to the
      row head — the inverse, for `Handle`). Axiom-free; the row machinery the effect
      safety statement and the `Handle` discharge both need, built before the harder
      `Perform`/`Handle`/frame-typing work so that layer is isolated.
- [x] **Transparent effect boundary** (`Reduction.lean` `doPerformR`, T5b) — the
      *effect analog of the T0 substrate fix*. **FINDING:** the `Reduce` path's
      `reducePerform` was still calling the interpreter's **opaque `partial def
      doPerform`**, so any kernel reasoning about the `.perform` boundary (effect
      safety: emitted `op ∈ ε`; `wait` typing) was blocked exactly as the original
      `step` opacity blocked preservation (the T0 wall, reappearing for effects).
      `doPerform` is, however, **structurally decreasing on the stack `k`** (the
      `partial` was unnecessary), so it is now mirrored by a total transparent twin
      `doPerformR : … → Stack → acc → Return` that `reduce1Run` uses instead. The
      `.perform`/`Resume` reduction is therefore kernel-transparent and a preservation
      proof can `cases`/unfold the stack walk. Validated executably: `lake build`
      green and `lake exe spec` 104/104 (the `evalR`/`runR` `#guard` battery exercises
      the perform/handle fixtures, so the twin is behaviourally identical to the
      interpreter's `doPerform`). This was a prerequisite the plan had not surfaced;
      the direct-frame-typing route (fork (a)) is now unblocked.
- [x] **Un-pin the effect row — `Perform` + effect safety DELIVERED** (T5c, design in
      `progress/2026-06-16-T5-unpin-perform-design.md`). The effect row is no longer
      pinned: `HasType.perform` (`∀α β μ. α →⟨l:(α,β)|μ⟩ β`, Koka operation-as-variable
      with an arbitrary tail) makes `Perform l arg` typeable exactly when the ambient
      row carries `l` (effect safety falls out of the `app` rule's latent = ambient).
      `HasTypeV.partialPerformNil`, `inv_perform`, and the new `MStateWf` `wait` clause
      `∃ a b replyTy, EffContains ε op a b ∧ TyEquiv b replyTy ∧ StackWf k replyTy ε τ`
      (the 3-existential form sidesteps any stack-input conversion). `preservation` now
      proves **effect safety**: a `.perform` lands a well-typed `wait` with `op ∈ ε`
      (`preservation_perform` + `reduceCall_perform_wait` +
      `stackWf_doPerformR_unhandled`: a typed stack has no `Delimit`, so the transparent
      `doPerformR` reports unhandled and the effect escapes). `progress` gains the
      **effect-escape disjunct** (a well-typed non-value steps / is a value / sanctioned
      crash / suspends on `.perform op` with `EffContains ε op a b`). The `.reply` case
      is conditioned on the `ReplyContract` (typed reply) — sound because closed `evalR`
      never replies, so `soundness_value` stays green untouched; the contract only bites
      at `runR`/`BehaviorsR` (T6/T7). All sorry-free, axioms
      `propext`/`Classical.choice`/`Quot.sound`; `lake exe spec` 104/104; a sanity
      `example` types `perform "Log" "hi" : unit ! ⟨Log:(String,unit)⟩`.
- [~] **Type `Handle`.** ⚙ **Design worked out** in
      `progress/2026-06-16-T5-handle-design.md`. **Continuation keystone DELIVERED**
      (T5d', `Eyg/Types/Runtime.lean`): `StackSegWf seg σin εin σout εout` (a segment
      typing tracking *both* endpoint type+row) + `stackSeg_append` (compose two
      segments end-to-end). This **corrects** the first T5d attempt
      (`stackWf_move`/`stackWf_append`, `Machine.lean`): those assume a *uniform*
      ambient row and so cannot compose across the row-discharging `Delimit` frame —
      `StackSegWf` tracks the per-endpoint rows and *does* (axioms `propext`). It is
      what types `Resume`'s captured `move acc k` continuation in the wiring below.
      (`StackSegWf` is standalone now; it joins the `HasTypeV` mutual block when
      `partialResume` references it — `stackSeg_append` re-proves by `induction seg` +
      `cases hseg`, which mutual inductives support.) The `handle` scheme abbrevs
      (`kontTy`/`handlerTy`/`execTy`/`handleTy`) are in `Typing.lean`.
      **Remaining cascade** (one atomic unit — `StackWf.delimit` breaks every
      `cases hst` site at once): `StackWf.delimit` + the mixed
      `StackSegWf ++ StackWf → StackWf` lemma; `HasType.handle` + `inv_handle` +
      `hasType_expr_form` arm (+ `rcases` bumps); `HasTypeV.partialHandleNil`/
      `partialHandleOne`/`partialResume` (+ `conv`/`canonical_arrow`); the
      **dispatch lemma** (`stackWf_doPerformR_unhandled` → handled-`.tau`-vs-escape,
      with effect-safety *through* non-matching `Delimit`s — the one hard proof left,
      §5 of the note); `delimit` cases at the 4 `cases hst` sites; and
      preservation/progress for `reduceDeep` / `Delimit`-pop / handled-`perform` /
      `Resume`. Remaining beyond the keystone: the `handle` scheme; the `Delimit`
      answer-type-transformer frame that discharges `l`; the `Resume` reified-
      continuation typing as a stack-*segment* transformer `reply ⇒ ret`; the
      generalization of `stackWf_doPerformR_unhandled` to a handled-`.tau`-vs-escape
      dispatch; and the one new metatheory point — the ambient row *shrinks* across a
      `Delimit`, which the per-frame `StackWf` row already accommodates). Highest-risk
      slice (continuation typing, no precedent); fork (b) simulation remains the
      fallback. Now the only remaining effect rule. With `Handle`/`Delimit`
      a typed `StackWf` *will* carry a `Delimit` frame, so `stackWf_doPerformR_unhandled`
      generalizes to "walk to the nearest matching `Delimit`": a handled `perform`
      resumes (`.tau`) rather than escaping. Add `Handle`
      (input `EffectExtend(l,(a,b),tail)` → output `tail`; `l` discharged; all of
      `Σ(l)` handled; bind `resume`), with the `shallow : Bool` flag flipping the
      resumption's codomain row (deep = discharged `tail`; shallow = undischarged), and
      type the `Delimit`/`Resume` frames (T5 fork (a), direct frame typing — now
      unblocked by the transparent `doPerformR`).
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
- [~] **Builtin-saturation typing.** ⚙ **Per-builtin `Builtin.run` typing DELIVERED**
      (T6a, `Eyg/Types/Soundness.lean`) — *independent of the `Handle` blocker, and
      confirmed mechanical*. Every builtin in the analyzer scheme table **except the
      stack-coupled `fix`** now has its `run` typed green: `run_int_{add,subtract,
      multiply,absolute,to_string,compare,divide,parse}`, `run_string_{append,length,
      uppercase,lowercase,starts_with,ends_with}`, `run_equal` — each extracts the typed
      args via the canonical-forms lemmas, computes `run`, and types the result
      (`int`/`str`/`bool`/`result`/`ordTag`), with the `int_*` overflow and `int_parse`
      traps shown to be the sanctioned `Unrepresentable`. Value-typing helpers added:
      `hasTypeV_unit`/`hasTypeV_bool`/`hasTypeV_ok`/`hasTypeV_error`/`hasTypeV_ordTag`.
      **Remaining:** `fix` (special — re-applies via a pushed frame, not `run`); and the
      **assembly** into the isolated hypotheses `BuiltinAppPreserves`/
      `BuiltinAppNoBadCrash` (case on `id`, extract args from `BuiltinPartialWf`, split
      under-saturation accumulation vs. saturation, plus the special
      `fix`/`list_fold`/`binary_fold` arms of `reduceCallBuiltin`). The grow-the-scheme-
      table part is also here if any untyped builtins are added.
      **Scoping finding (sharpens T6b):** `list_fold`/`binary_fold` are **not in the
      analyzer scheme table**, so they are *out of scope* for `BuiltinAppPreserves` (a
      `Partial (Builtin "list_fold")` is not typeable — `partialBuiltin` requires a
      scheme). So among the stack-coupled specials, **only `fix` matters**, and it is the
      genuinely hard one: `reduceCallBuiltin "fix" [builder]` produces an *internal*
      `Partial (Builtin "fixed") [builder]` which has **no scheme** (analogous to
      `Handle`'s internal `Resume`), so typing the fix successor needs bespoke handling
      of the `fixed` partial, not the standard `partialBuiltin`. The clean route is to
      isolate a `FixPreserves` sub-hypothesis and discharge `BuiltinAppPreserves` for the
      ~13 general builtins via the (now-proven) `run_*` lemmas + the saturation/
      accumulation case split. So T6b reduces to: the `BuiltinPartialWf`/arity plumbing
      for the general builtins (mechanical, uses T6a) + the isolated `fix`.
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

- [~] **T0:** transparent `Reduce` + `evalR` ✅; `Reduce≈step` via build-time
      `#guard`s ✅; the opaque-`partial def` blocker resolved by reasoning over
      `Reduce` ✅. `BehaviorsR` + the dedicated `lake exe spec Reduce≡step` line:
      deferred.
- [~] **T1–T2:** full `Ty` ✅; `RowEquiv`/`EffEquiv` proved an equivalence ✅ (+ the
      head/component inversion lemmas the proof needs ✅); schemes + builtin table ✅.
      `RowEquiv` decidability via normalization: deferred (not needed for the proof).
- [x] **T3 (the derisking checkpoint):** `progress`+`preservation`+`soundness_value`
      **green and sorry-free for the pure monomorphic core**, axioms clean, with the
      *final* judgment signatures (so later slices only add cases). The two builtin
      saturation obligations are isolated as the hypotheses `BuiltinAppPreserves` /
      `BuiltinAppNoBadCrash` (T6).
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
