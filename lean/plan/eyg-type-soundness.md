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
- [x] **`Reduce`-based observable layer**: `evalR : Nat → Config m → Result`
      (fuel-structural, reuses FBS `Result`) **DELIVERED** (+ `runR` for an effect
      oracle). `BehaviorsR : Config m → Set Behavior` (the `MTr`-over-`Reduce`
      mirror of S4 `Behaviors`) **DELIVERED** (`Eyg/Semantics/BehaviorR.lean`):
      `reduceLTS := ⟨Reduce⟩`, `BehaviorsR` (the three-shape mirror over
      `reduceLTS.MTr` + the transparent `MState.terminalR?`), and the tie-the-knot
      `evalR_sound_done`/`evalR_done_mem_behaviorsR` (a terminating `evalR` is a
      terminating member of `BehaviorsR` — a *kernel* theorem, `reduce1Run` being
      transparent). Axioms clean. It is what T7 concludes about.
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

> **✅ T5 DELIVERED (2026-06-17, commit "T5 Handle/Delimit DELIVERED"; design in
> `progress/2026-06-16-T5-handle-design.md`, delivery in
> `progress/2026-06-17-T5-handle-delivered.md`).** `Handle`/`Delimit`/`Resume` are typed
> (`HasType.handle`; `HasTypeV.partialHandleNil/One/partialResume`; `StackWf.delimit` +
> `StackWf.conv` + the six conv-folding frame-inversion lembas; `StackSegWf`/`stackWf_resume`)
> and **`preservation`/`progress`/`soundness*` re-green over the full effect language** via
> the fork's chosen route **(a) direct frame typing** (Open Question 1 resolved in favour of
> (a) — the simulation fallback (b) was not needed). `preservation`/`preservation_V` now
> conclude `∃ε'` (the ambient row shrinks across a `Delimit`-pop, grows across `reduceDeep`).
> `lake build` + `lake exe spec` 104/104, no `sorry`, headline axioms clean, **no new
> `axiom`s**. **`ε`-free value + no-bad-crash soundness is UNCONDITIONAL for the full language
> incl. `Handle`** (modulo `Fix*`). Two follow-up obligations are isolated as explicit
> hypotheses (same pattern as `BuiltinAppPreserves`/`Fix*`, *not* axioms): **`HandlerObligations`**
> (the three handler dispatches — perform stack-walk to the matching `Delimit`, `reduceDeep`
> install, `Resume` feed) and **`TauKeepsRow`** (the T7 row-evolution gate; true for the
> handler-discharge-free fragment; gates only the row-dependent effect-escape/divergence/reply
> results). Delivered via resumable-WIP grinding (45→14→6→0 errors over four passes).
>
> **✅ HANDLER DISPATCHES FULLY DISCHARGED (2026-06-18, commit "remove the discharged
> HandlerObligations hypothesis").** All three (`install`, `resume`, `perform`) are now
> *proved* and the `HandlerObligations` hypothesis is **removed** — `preservation`/`progress`/
> `soundness*` no longer assume any handler-dispatch obligation. Route: `install` via the
> generalized `StackWf.delimit` (row subsumption `tail ⊑ ε`); `resume` via the generalized
> `StackSegWf.delimit` + the discharge-row-quantified `partialResume` (`resume_preserves`);
> `perform` (the genuine continuation-typing crux — design §5, no precedent) via the
> generalized `StackSegWf.nil` + `hasType_ctxConv` + `stackSeg_conv_input`/`_output` (ordinary
> induction, NO mutual recursor) + the `doPerformR` walk (`perform_walk`/`perform_preserves`).
> `lake build` 1771 jobs, `lake exe spec` 104/104, headline axioms clean, no `sorry`/no new
> `axiom`s. **Remaining isolated hypotheses are now only `Fix*` (effectful-builder fix) and
> `TauKeepsRow`** (the T7 row-evolution gate for the row-dependent effect-escape/divergence
> results). The `ε`-free value + no-bad-crash soundness is **unconditional for the full
> language including `Handle`** (modulo `Fix*`).
>
> **✅ `TauKeepsRow` ELIMINATED (T7 RowEvolves; 2026-06-18, 6 commits,
> `progress/2026-06-18-T7-rowevolves-Bpreservation-delivered.md`).** The false `TauKeepsRow`
> hypothesis is **deleted**: the row-dependent soundness results (effect escape / divergence /
> suspension / reply-containing terminating traces) are now **unconditional in `TauKeepsRow`**,
> gated only on the *true, dischargeable* `BuiltinAppPreservesB` (+ pre-existing `Fix*`). Built
> via the base-row engine — `StackWfB` (+ `conv`, the seven `stackWfB_*_inv`, `stackWfB_toStackWf`),
> the dispatch B-lemmas (`stackSeg_toStackWfB`/`resume`/`install`/`perform_walk_B`/…),
> `preservation_E_B`/`_V_B`/`preservation_tau_B`/`preservation_keep_B`, the escape boundary
> (`stackWfB_escape` with the reply-`TyEquiv` link, `noHandlerFor` baked into `MStateWfB.wait`,
> `mStateWfB_perform_escape`), and `soundnessR_effect_B` — then re-threaded all 15 consumers
> (`soundness`/`soundness_behaviorsR_diverges`/`_suspended`/`_terminates_*`/`soundness_evalR`/
> `pure_*`) to `MStateWfB`+`hsatB`. Axioms clean (`propext`/`Classical.choice`/`Quot.sound`), no
> new `axiom`s, `lake build` 1771 + `lake exe spec` 104/104.
>
> **✅ `BuiltinAppPreservesB` DISCHARGED (same day).** `builtinApp_arity1_B`/`_arity2_B` +
> `builtinAppPreservesB : FixPreservesB → BuiltinAppPreservesB` (the 16-arm `scheme_cases`
> dispatch), `FixPreservesB` isolated like `FixPreserves`. The headline `soundness`/`soundness_evalR`/
> `soundness_evalR_pure` re-pointed to take `FixPreserves`/`FixNoBadCrash`/`FixPreservesB` only —
> **the same `Fix*` family as the ε-free results**. So the row-dependent soundness (effect escape /
> divergence / suspension / reply traces) is now gated on `Fix*` alone, with **no `TauKeepsRow` and
> no standalone saturation hypothesis**. Axioms clean, `lake build` 1771 + `lake exe spec` 104/104.
>
> **✅ `FixNoBadCrash` DISCHARGED (2026-06-18).** The `fix`-*creation* `reduceCall` only ever
> `.tau`-steps (special arm builds the `fixed` partial; otherwise the catch-all accumulates,
> `builtinArity "fix" = 1` so `Builtin.run "fix"` is never reached), so it never crashes:
> `reduceCallBuiltin_fix_ne_crash` + `fixNoBadCrash : FixNoBadCrash m` (unconditional — no pure
> builder needed). Removed from the headline; `soundness`/`soundness_evalR`/`soundness_evalR_pure`
> now take **only the two preservation hypotheses `FixPreserves` + `FixPreservesB`**.
>
> **✅ `FixPreserves`/`FixPreservesB` DISCHARGED (2026-06-18) — headline soundness is now
> UNCONDITIONAL.** Per the user's decision (fork (i): narrow the `fix` scheme to a `∅`-latent
> **pure builder**, accepting analyzer-divergence — it rejects builder-side-effecting recursion the
> reference analyzer accepts, but covers all standard curried recursion). Two changes were needed,
> not one: (1) the pure-builder narrowing (`Builtins.scheme "fix"` `q1 → ∅`) handles the
> **saturation** case (the partial's argument is exactly `partialFixed`'s pure builder); (2) a
> newly-discovered **over-application gap** — `FixPreserves` was *unsatisfiable as stated* because
> `fix`'s arrow return type let `partialBuiltin` type a fictional over-applied `Partial "fix" [b₀]`,
> whose application accumulates to an untypeable partial — was closed by enforcing the (already
> *intended*, never *enforced*) **strict-under-application invariant** `applied.length < arity` on
> `HasTypeV.partialBuiltin` (bundled as `PartialBuiltinWf`), which forces `applied = []`. Then
> `fixPreserves`/`fixPreservesB` are *proved* (the `fixed[builder]` successor types via
> `partialFixed` + `applyf` with `retTy = self`), and the headline `soundness`/`soundness_evalR`/
> `soundness_evalR_pure` re-pointed to supply them internally — they now take **only**
> `HasType [] prog τ ε`. Axioms `propext`/`Classical.choice`/`Quot.sound`; no `sorry`; no new
> `axiom`s; `lake build` 1772 + `lake exe spec` 104/104. The only remaining Lean-side
> under-approximation vs. the reference analyzer is the pure-builder pin (effectful-builder `fix`
> awaits Open Question 3's row subsumption); the **value/no-bad-crash/effect-safety soundness for
> the full language is now hypothesis-free** (modulo that pure-builder fragment). Findings:
> `progress/2026-06-18-fix-discharge-overapplication-blocker.md`.

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

- [x] **Let-generalization** `gen` — **✅ DELIVERED (2026-06-19, restricted `let_poly`,
      `progress/2026-06-19-T6-let_poly-DELIVERED.md`).** `HasType.let_poly` (value-restricted, scheme
      `genAt n defnTy`, `CtxWf n Γ` + `noLet lbody`) + value-aware `StackWfV`/`StackWfE` (and B-mirror
      `StackWfVB`/`StackWfEB`) carrying the polymorphic readiness from the let-push to the Assign-pop;
      `preservation`/`progress`/`soundness*` re-green over **both** engines. `lake build` 1772 + spec
      104/104, no `sorry`, axioms `propext`/`Classical.choice`/`Quot.sound`, no new `axiom`s. Key insights:
      the **instantiation-vs-`LevelMap`** finding (→ restricted `noLet` route, arbitrary-σ `hasType_subst`
      with vacuous `Let` arms), and **mono-only `StackWf.assign`** (poly assigns are transient, so
      `stackWf_toStackWfV/E` are unconditional). Residual under-approximations: `noLet`-body (no internal
      `let` inside a polymorphic function — covers all combinator polymorphism) + the pre-existing
      pure-builder `fix` pin. *Original plan (now historical):* declaratively and
      **effect-safe** (only generalize effect tails that don't escape — mirror
      `close`/`close_eff`; Open Question #3). Extend the `Let` rule and re-green.
      **FOUNDATION DELIVERED** (`progress/2026-06-16-T6-gen-substitution-infra.md`,
      two green commits): the de Bruijn substitution infrastructure — `Ty.shift`,
      `Scheme.instantiate` re-based on the **shift convention** (ambient body-var
      `i ≥ arity` ⇒ ambient var `i - arity`; identical normal form for all current
      closed/mono schemes, so the project + spec stay green), `Scheme.substScheme`,
      and the commutation lemmas `subst_instantiate`/`subst_instantiate'` (the latter
      unconditional in `args`, via the `instArgs` witness) — plus the **term-level
      `hasType_subst`** (`Eyg/Types/Substitution.lean`: `HasType Γ e τ ε → HasType
      (substCtx σ Γ) e (subst σ τ) (subst σ ε)`, axioms clean). The scheme type-var
      **convention is now pinned** (shift-based), resolving the gen-scoping blocker.
      **⚠ New finding:** the *value*-level `HasTypeV v τ → HasTypeV v (subst σ τ)` is
      **false** for open row types (substituting a row-tail var adds record/union
      labels the value lacks). Resolution: the **value restriction** — `gen`
      generalizes only syntactic-value `defn`s, whose runtime forms
      (closure/literal/operator-partial/`[]`/`unit`) are all arrow/base/closed-row
      and *do* satisfy substitution, while `σ` fixes the captured context by
      construction. The **closure case** of the value lemma is delivered
      (`hasTypeV_subst_closure`, conditioned on `σ` fixing the captured context);
      `Ty.freeVars`/`subst_eq_of_fixes_free` supply the context-fixing reasoning.
      **⚠ Deepened finding:** the closure-context proviso must hold for *every*
      context the runtime env realizes, but `HasTypeV`'s closure context `Γcap` is
      existential and `EnvWf` non-unique, so `FV(Γcap) ⊆ FV(Γ)` is not recoverable
      post-hoc — `gen` needs a **context-freshness invariant threaded through
      `MStateWf`** (the closure-runtime analogue of HM's "don't generalize env vars"),
      an invasive change comparable to the `fix`/`Handle` invariants.
      **⚙ DECLARATIVE KEYSTONE DELIVERED** (2026-06-18,
      `progress/2026-06-18-T6-gen-declarative-keystone.md`, `Eyg/Types/Generalization.lean`):
      the route that **sidesteps both** the de Bruijn `gen` computation *and* the
      `MStateWf`-freshness blocker. Following the judgment's declarative style, `let_poly`
      will quantify over *any* scheme satisfying the predicate `Generalizes s Γ defnTy`
      (every instantiation is a `Γ`-fixing substitution instance of `defnTy`) — no principal
      `gen` is computed (that is the T8 inference layer). The **value restriction** +
      `closure_typed_of_lambda_subst` type the closure at the *known* let-site `Γ` (no
      existential capture context), so `generalizes_closure_ready` discharges the exact
      `EnvWf.cons` clause `∀ args, HasTypeV v (s.instantiate args)` **without** any
      `MStateWf` freshness invariant. `generalizes_mono` shows monomorphic `let` is the
      `arity = 0` degenerate case. Green, axioms `propext`/`Quot.sound`, no new `axiom`s.
      **Remaining (the atomic build-breaking cascade):** (a) the `HasType.let_poly`
      constructor (value-restricted) + `inv_let_poly` + `hasType_expr_form` arm; (b) generalize
      the `StackWf`/`StackSegWf.assign` frame from `.mono defnTy` to an arbitrary scheme with a
      stored `Generalizes` witness; (c) re-green `preservation` (`Assign`-pop uses
      `generalizes_closure_ready`) / `progress`; (d) a polymorphic-reuse `example`.
      **⚠ Rigorous finding (2026-06-18):** the *easy* route — a value-agnostic readiness
      premise on the `assign` frame (`∀ v, HasTypeV v defnTy → ∀ args, HasTypeV v
      (s.instantiate args)`) — is **provably impossible**: it is exactly the false
      value-substitution lemma (false even for arrow `defnTy`, via a closure capturing an
      open-row-typed variable `σ` doesn't fix). Since `MStateWf`'s value case decouples the
      value's type from the stack (`∃ τin, HasTypeV v τin ∧ StackWf k τin ε τ`), the
      `Assign`-pop sees only an arbitrary `v : defnTy` and **cannot** know it is the let's
      closure without a **machine-level frame↔control coupling invariant** threaded through
      `MStateWf` (the surface `Handle`/`TauKeepsRow` touched). So `let_poly` is a focused
      milestone slice, not a mechanical edit; the keystone makes its hardest *semantic*
      obligation a one-liner once the stored `Γ`-typing is in hand. See the progress note.
      **⚙ DESIGN SHARPENED (2026-06-18, `progress/2026-06-18-T6-let_poly-coupling-design-sharpened.md`):**
      resolves the two items the first coupling note left open. Tracing the reduction
      (`Reduction.lean:241` push stores `fenv = env`; `:222` pop binds into `fenv`) pins the exact
      mechanism that **defeats pop-time readiness reconstruction**: in the generic preservation
      state `env`/`fenv` are independent fields and `Γc`/`Γf` independent existentials, so the
      keystone's coherent `(Γ, EnvWf·Γ, λ-typing, Generalizes)` package is unavailable at the pop.
      **Resolution:** compute the closed readiness `Rdy : ∀args, HasTypeV (Closure x' body' env)
      (s.instantiate args)` **at the push** (the one coherent point — `generalizes_closure_ready`
      applies directly to `hdefn`), then *carry* `Rdy` + the value-coupling `val = w` across the
      single lambda→closure step via a **value-aware stack predicate `StackWfV`** (value-aware only
      at the `Assign` head; recurses through `trace`, drops to plain `StackWf` where the head
      consumes the value). The `MStateWf` value case becomes `∃τin, HasTypeV v τin ∧ StackWfV v k
      τin ε τ`; `StackWf.assign` generalizes to store an arbitrary scheme. The checklist (incl. the
      **required B-world mirror** — adding the constructor breaks the base-row engine arms) and two
      concrete E-side carry options are in the note. No code this session (the cascade is
      all-or-nothing; no standalone green increment exists — confirmed); `lake build` 1772 + spec
      104/104 still green.
      **⚙ FOUNDATIONAL FREE-VAR LEMMAS DELIVERED** (2026-06-18, `Eyg/Types/Scheme.lean`): a
      constructor probe surfaced a *new* obstacle — `hasType_ctxConv`'s `let_poly` arm needs
      `Generalizes` to survive a `TyEquiv` binding-rewrite, which the syntactic context-fixing does
      not give directly. The two lemmas that unblock it (`generalizes_ctxConv`) are landed green and
      standalone: **`Ty.fixes_free_of_subst_eq`** (converse of `subst_eq_of_fixes_free`:
      `subst σ t = t → ∀ i ∈ freeVars t, σ i = .var i`) and **`Ty.freeVars_tyEquiv`** (`TyEquiv`
      preserves the free-var set). `lake build` 1772 + spec 104/104. The constructor/cascade probe
      itself was reverted (the full slice is all-or-nothing through the two-engine `Soundness.lean`);
      these two lemmas are the kept increment. **`generalizes_ctxConv` also DELIVERED**
      (`Eyg/Types/Generalization.lean`, + `substCtx_eq_self_iff`): `TyEquiv σ' σ → Generalizes s
      (Δ++(x,.mono σ)::Γ) d → Generalizes s (Δ++(x,.mono σ')::Γ) d` — the typing-layer obstacle the
      probe found, now fully pre-cleared in the exact shape the `hasType_ctxConv` `let_poly` arm
      consumes. **All standalone-green increments for `let_poly` are now landed**; the remaining work
      (the `HasType.let_poly` constructor + value-aware `StackWfV` + generalized `StackWf.assign` +
      both preservation engines) has no committable sub-increment and is the dedicated implementation
      session.
      **⚠ IMPLEMENTATION ATTEMPT — HARD WALL FOUND at `hasType_subst`** (2026-06-18,
      `progress/2026-06-18-T6-let_poly-hasType_subst-blocker.md`, WIP in
      `progress/2026-06-18-T6-let_poly-WIP.patch`). The typing-layer cascade went green up to
      `Generation` (the `HasType.let_poly` constructor, `hasType_ctxConv` arm via `generalizes_ctxConv`,
      unified `inv_let`, `hasType_expr_form` arm — all compile), then hit a **mathematical** wall, not
      proof engineering: the term-level substitution lemma `hasType_subst` (arbitrary σ) is **FALSE**
      for `let_poly` because **`Generalizes` is not substitution-stable** — a machine-checkable
      counterexample (`sc=⟨1,var0⟩`, `Γ=[(y,.mono(var1))]`, `defnTy=var0`, `σ=[0↦var1]`) shows σ can
      collide a generalized variable into `FV(Γ)`, and "σ fixes `FV(Γ)`" does not rescue it. Since
      `hasType_subst` feeds the readiness keystone (`closure_typed_of_lambda_subst`) and must be total
      over nested `let_poly`, the **freshness/de-Bruijn-LEVEL discipline the PLAN deferred is now
      mandatory** (recommended fix: index `Generalizes` by a level `n`, constrain σ below `n`). This is
      the real remaining T6 gen crux — a structural change threading a level through
      `HasType`/`hasType_subst`/the `StackWf.assign` frame. Reverted; `lake build` 1772 + spec 104/104
      green. **The blocker is MACHINE-CHECKED** (`Eyg/Types/Generalization.lean`): `cex_pos`/`cex_neg`
      + **`generalizes_subst_false`** — a closed Lean proof that the `generalizes_subst` implication is
      false — so the declarative-keystone route's insufficiency is a *theorem*, not a hand-argument.
      (This sharpens the optimism of `progress/2026-06-18-T6-gen-declarative-keystone.md`: the keystone
      does **not** sidestep the freshness blocker — the blocker re-emerges at `hasType_subst`.)
      **⚙ RESOLUTION DESIGNED** (`progress/2026-06-18-T6-let_poly-level-redesign-design.md`): the
      de-Bruijn-**level** redesign — a level-indexed `GeneralizesAt n s d` (generalized vars `≥ n`,
      witnessing `σ'` fixes `[0,n)`) that *is* substitution-stable for level-map `σ`. The note pins the
      **non-obvious crux** a naive "add a level" attempt misses: **nested `let_poly` at deeper levels**
      `n' > n` — the keystone's instantiation `σ'` fixes `[0,n)` but acts on `[n,∞) ⊇ [n',∞)`, so the
      level must be threaded *structurally* (bumped at each binder) and `hasType_subst` re-levelled as it
      descends, with the ambient-into-ambient condition `∀i<n, FV(σ i) ⊆ [0,n)`. Scoped milestone:
      (1) the minimal-blast-radius call — full `HasTypeAt n` vs. a `WfBelow n` side-invariant;
      (2) `generalizesAt_subst`; (3) re-state `hasType_subst` with the level-map premise;
      (4) the unchanged machine coupling. Items 1–3 are the genuine multi-session structural
      prerequisite. **`GeneralizesAt` + the bridge `generalizesAt_to_generalizes` + `generalizesAt_mono`
      DELIVERED green** (`Eyg/Types/Generalization.lean`); **`generalizesAt_subst` resisted a direct
      proof** — finding: the *declarative* `∃σ'` form does not reduce arbitrary substituted-scheme
      instantiations through `subst_instantiate'`, so it likely needs a **constructive** `GeneralizesAt`
      (`s = gen_n d`, computed generalization) — a design fork recorded in the redesign note. Tree green:
      `lake build` 1772 + spec 104/104.
      **⚙ CONSTRUCTIVE-GEN FORK DELIVERED — `generalizesAt_subst` GREEN** (2026-06-18,
      `progress/2026-06-18-T6-let_poly-constructive-genAt-delivered.md`). The design fork is landed: a
      *computed* generalization **`Scheme.genAt n d`** (= `⟨genArity n d, subst (reindexGen n ·) d⟩`, with
      `Ty.genArity`/`Ty.reindexGen` + `genArity_spec`) makes the witness scheme body **structurally**
      `subst (reindexGen …) d`, so substitution-stability becomes a `subst`/`shift` **commutation**, not an
      existential chase. Delivered green, axioms `propext`/`Quot.sound` only: `genAt_generalizesAt`
      (`GeneralizesAt n (genAt n d) d`); the level-map class **`Ty.LevelMap n σ`** (fixes `[n,∞)`, keeps
      `[0,n)` within `[0,n)` — the ambient-into-ambient condition); arity stability **`genArity_subst`**
      (`LevelMap n σ → (subst σ d).genArity n = d.genArity n`); the commutation **`genAt_substScheme`**
      (`substScheme σ (genAt n d) = genAt n (subst σ d)`); and the headline **`generalizesAt_subst`**
      (`LevelMap n σ → GeneralizesAt n (substScheme σ (genAt n d)) (subst σ d)`) — exactly what the
      `hasType_subst` `let_poly` arm needs once the rule pins its scheme to `genAt`. Foundational reusable
      lemmas `Ty.subst_congr_free`/`Ty.mem_freeVars_subst` added (`Scheme.lean`). `lake build` 1772 + spec
      104/104. **Remaining for the slice (now unblocked; multi-step structural, no standalone-green
      sub-increment through the two-engine `Soundness.lean`):** (1) pin the `let_poly` rule's scheme to
      `genAt` + the minimal-blast-radius level carrier (`HasTypeAt n` vs. `CtxWf n`/`TyWf n`
      side-invariant); (2) re-state `hasType_subst` with the `LevelMap n σ` premise (its `let_poly` arm
      discharges via `generalizesAt_subst`); (3) the unchanged machine coupling (`StackWfV`, both engines).
      **⚙ ITEM-1 DECISION + DESCENT GLUE DELIVERED** (2026-06-18,
      `progress/2026-06-18-T6-let_poly-levelmap-mono-and-wfbelow-decision.md`). Item 1 is **resolved in
      favour of the `WfBelow n` side-invariant** (not a full `HasTypeAt n`): the enabling fact is that
      **`Soundness.lean` does not import `Substitution`/`Generalization`**, so the level `n` lives only in
      (a) the `let_poly` constructor's premises (scheme `genAt n defnTy` + a context-below-`n` witness) and
      (b) `hasType_subst`/`genAt_closure_ready` — **both off the Soundness import path**. The two
      preservation engines therefore treat `let_poly` as an *opaque* constructor carrying a body typing +
      a precomputed closed `Rdy` (from `genAt_closure_ready` at the push), and **never mention `n`** — so
      the soundness side is the plain `StackWfV` cascade with *no* level threading, and the full
      `HasTypeAt n` alternative is unnecessary. The nested-`let_poly` "re-level on descent" crux is
      dissolved by **`Ty.LevelMap.mono`** (`LevelMap n σ → n ≤ n' → LevelMap n' σ`, green, axioms clean):
      the outer-scope `σ` is automatically a `LevelMap` at every deeper let's level, so `hasType_subst`'s
      `let_poly` arm discharges the inner `generalizesAt_subst` from the *same* `σ` — no re-levelling.
      **⚙ `hasType_subst` ARM RESOLVED + `CtxWf` INFRA DELIVERED** (2026-06-18,
      `progress/2026-06-18-T6-let_poly-hasType_subst-arm-design-resolved.md`). Landed green (gen branch,
      off the Soundness path; axioms clean): the scheme/context free-var metatheory the arm needs —
      `Ty.mem_freeVars_shift`, `Scheme.freeVars`/`mem_freeVars`/`substScheme_eq_of_fixes_free`/
      `mem_freeVars_substScheme`, and **`CtxWf n Γ`** (+ `CtxWf.mono`, `ctxWf_cons`, `ctxWf_substCtx`,
      `ctxWf_fixed`). The `let_poly` arm of `hasType_subst` is now fully worked out: it reconstructs via
      `genAt_substScheme` + `ctxWf_substCtx`, whose **only** requirement beyond the let_poly node's
      *stored* `CtxWf n_lp Γ` is `LevelMap n_lp σ` — obtained from `LevelMap n σ` + `n ≤ n_lp` via
      `LevelMap.mono`. **No global `CtxWf`/`TyWf` is needed** (the non-`let_poly` arms never consume
      `CtxWf`), killing the intermediate-type-escape worry. **⚠ Refined item-1 nuance:** the single
      residual gate `n ≤ n_lp` (nested lets' levels ≥ enclosing) is a let-level-monotonicity of the
      *static* program — threadable through preservation as **one light, unchanging global invariant** on
      `MStateWf` (reduction creates no new let nodes), far lighter than full `HasTypeAt n` level-indexing.
      So the engines carry exactly one constant side-hypothesis (supplying `n ≤ n_lp` to the readiness
      keystone at the push), not per-rule level threading.
      **⚙ CASCADE ATTEMPTED — typing layer green; two blockers pinned** (2026-06-18,
      `progress/2026-06-18-T6-let_poly-cascade-attempt.md` + WIP patch
      `progress/2026-06-18-T6-let_poly-cascade-WIP.patch`). The **typing-layer cascade builds**: def
      relocation (`genAt`/`genArity`/`reindexGen`/`Scheme.freeVars`→`Scheme.lean`, `CtxWf`→`Typing.lean`),
      the `HasType.let_poly` constructor, `hasType_ctxConv` arm (+ `ctxWf_ctxConv`), `inv_let` unified to a
      mono/poly **disjunction** (the `Generalizes`-unified form is blocked by a `Generation`↔`Generalization`
      import cycle), and the `hasType_expr_form` arm — all compile. **Blocker 1:** `hasType_subst`'s
      `let_poly` arm needs the gate `n ≤ n_node` (so `LevelMap.mono` supplies `LevelMap n_node σ` for
      `genAt_substScheme`/`ctxWf_substCtx`); since `n_node` is in the *derivation* not the term, this needs
      a small **`WfLevel n` inductive over derivations** (~20 trivial arms) threaded through `hasType_subst`,
      with the keystone supplied `WfLevel (n_lp+arity)` from the light program let-leveling invariant.
      **Blocker 2:** the value-aware `StackWfV` two-engine coupling (unchanged shape; gated on Blocker 1
      since it needs the compiled keystone). No green intermediate exists (the constructor breaks
      `hasType_subst`/`weakenEff`/both engines at once), so the `.lean` edits were reverted to keep the tree
      green; the WIP patch applies cleanly. Soundness touch points located: `weakenEff` (`:52`) +arm; the two
      `inv_let` consumers (`:204`,`:2728`) split on the disjunction.
      **⚠ DESIGN-LEVEL FINDING — the readiness substitution is the INSTANTIATION, not a `LevelMap`**
      (2026-06-18, `progress/2026-06-18-T6-let_poly-instantiation-levelmap-gap.md`). Wiring the keystone
      revealed that `generalizesAt_subst`/`genAt_substScheme` (built for *ambient* level-map substitutions)
      do **not** serve the readiness keystone: it re-types the generalized lambda **body** under the
      **instantiation** witness `σ_args`, which maps `v ≥ n+arity ↦ var (v−n−arity)` (a down-shift) and so is
      **not a `LevelMap`** — yet with `let_poly` present `hasType_subst` for arbitrary `σ` is false
      (`generalizes_subst_false`). A `LevelMap` witness `σ'` (identity above `n+arity`, valid since
      `FV(defnTy) ⊆ [0,n+arity)`) exists **only when the instantiation `args` are low** (`FV ⊆ [0,n+arity)`),
      which fails for the common `\y. id y` (polymorphic use at a locally-bound type). **Decisive split:** a
      generalized lambda body with **no nested `let_poly`** re-types under *arbitrary* `σ` via the existing
      arms (no `LevelMap`, no gap) — covering `\x.x`, `\x.\y.x`, … i.e. **all practical rank-1
      polymorphism**; only **nested** let-generalization is hard (high-`args` × nested-generalized
      interplay). **Revised plan:** ship a **restricted `let_poly`** (forbid nested let-generalization in the
      generalized body, via a syntactic `NoLet`-body premise or a light `ProgWf` invariant) using the
      *original arbitrary-`σ`* `hasType_subst` with a **vacuous** `let_poly` arm — this needs none of the
      `LevelMap`/`generalizesAt_subst` machinery and unblocks the `StackWfV` engine coupling. **Defer** full
      nested `let_poly` (needs readiness *without* re-substituting the body under instantiation — scheme-typed
      closures / lazy instantiation; the `LevelMap` route does **not** close it). The `LevelMap.mono`/`CtxWf`/
      `genAt_substScheme` infra stays committed-green for that future full version.
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
      **T6b ASSEMBLY DELIVERED** (`Eyg/Types/Soundness.lean`): `builtinAppPreserves`
      (`FixPreserves m → BuiltinAppPreserves m`) and `builtinAppNoBadCrash`
      (`FixNoBadCrash m → BuiltinAppNoBadCrash m`) — sorry-free, axioms clean. The
      saturation machinery is factored into reusable lemmas: `reduceCallBuiltin_other`
      (a non-special key takes the generic arity-dispatch branch — proved by `split`,
      sidestepping the unreducible string-literal matcher), `reduceCallBuiltin_sat`/
      `_acc`/`_sat_crash`/`ne_value` (the four outcomes), `builtinPartialWf_append`
      (peel one more typed arg), and `scheme_cases` (enumerate the 16-entry table). Two
      per-arity drivers (`builtinApp_arity1`/`arity2`, `builtinNoBad_arity1`/`arity2`)
      do the `BuiltinPartialWf` peel + saturate/accumulate split once; each builtin case
      just feeds in its `run_*` (or `run_*_noBad`, or an inline never-errors proof) lemma.
      **Key structural fact:** a partial typed at a *single* residual arrow forces the
      arg count to be exactly `arity − 1` or fewer, so saturate ⇔ codomain non-arrow and
      accumulate ⇔ codomain still an arrow — the two branches line up with the typing
      automatically. The `.done (.value _)` clause is vacuous (general builtins only
      `.tau` or `.done (.crash _)`). Wrappers `preservation_fix`/`progress_fix`/
      `soundness_value_fix` re-state the headline theorems with the general-builtin
      obligation discharged, leaving only `fix`. `lake build` + `lake exe spec` 104/104.
      **Remaining for T6b:** the isolated `fix` (`FixPreserves`/`FixNoBadCrash` — the
      `fixed` internal partial, analogous to `Handle`'s `Resume`); and any new builtins
      added to the scheme table (extend `scheme_cases`). The `fix` slice is **scoped** in
      `progress/2026-06-16-T6b-fix-scoping.md`: it needs a bespoke `HasTypeV.partialFixed`
      rule + a ~5-site `HasTypeV` cascade (a self-contained mini-`Handle`, lower risk than
      real `Handle` — no continuation capture/row discharge), deferred as its own slice.
      **Effect-weakening foundation for `fix` DELIVERED** (2026-06-17): `EffSub`
      (`Eyg/Types/EffSub.lean`, see Open Question 3 +
      `progress/2026-06-17-T6b-effsub-foundation.md`) — the row-subsumption relation
      finding 3 demands; `effSub_empty` types the `fix` pure-builder application under the
      effectful recursion ambient. The `StackWf` weakening variant that consumes it is the
      remaining step before `partialFixed`. **CONSUMING SLICE DELIVERED** (2026-06-17,
      `progress/2026-06-17-T6b-effect-weakening-consuming-slice.md`): generalized
      `HasType.app` + `StackWf.arg/applyf/callwith` carry `Ty.EffWeaken εf ε` (substitution-
      stable `TyEquiv εf ε ∨ TyEquiv εf .empty`); `weakenEff` admissible; `inv_app`/
      `hasType_subst` updated; builtin-saturation hypotheses decoupled (no `EffWeaken`
      needed). Green, sorry-free, axioms clean, spec 104/104. Only `partialFixed` remains for
      `fix`. **`partialFixed` + `fixed` RE-APPLICATION DELIVERED** (2026-06-17,
      `progress/2026-06-17-T6b-partialFixed-reapplication.md`): `HasTypeV.partialFixed`
      (the bespoke rule for the unscheme'd `fixed` partial, pinned to an **arrow** fixpoint
      `D→⟨γ⟩R` with a **pure** builder) + the full `HasTypeV` cascade (conv/`canonical_arrow`/
      the 7 `cases` sites) + `reduceCall_fixed`/`fixed_reapply_preserves` (the unrolling
      `builder (fix builder) arg` preserves — `Apply builder` weakens via `effWeaken_empty`,
      `CallWith arg` via the calling frame's `hw`). **Constraint A done:** added the
      `EffWeaken εf ε` premise to `BuiltinAppPreserves`/`FixPreserves`, threaded `hw` at every
      `hsat`/`hfix` site. The `fixed` re-application is **proven** inside `builtinAppPreserves`/
      `builtinAppNoBadCrash`. Green, sorry-free, axioms clean, spec 104/104. **⚠ Correctness
      finding:** the fixpoint type **must** be an arrow — typing it at an arbitrary `α` (per
      the raw gleam scheme) is *unsound* (a `fixed` `Partial` would inhabit base types,
      breaking canonical forms; `fix (\x.x+1) : Int` is well-typed yet cast-crashes). The
      arrow restriction is sound and covers all real recursion. **Still a hypothesis:**
      `FixPreserves`/`FixNoBadCrash` (the fix *creation* `reduceCall (fix-partial)`) — general-`B`
      creation needs the builder pure but the scheme's `q1` is free, so it is *not* dischargeable
      without either (i) pinning the `fix` scheme to a `∅`-latent builder (sound, analyzer-
      divergent narrowing) or (ii) general row subsumption (Open Question 3). The slice makes
      `FixPreserves` a *satisfiable* (pure-builder-inhabitable) hypothesis and does the novel
      `fixed`-re-application metatheory; the residual creation discharge is the planner (i)/(ii) fork.
- [x] Full `soundness` re-green over `BehaviorsR` for the complete language — ✅ the headline
      `soundness`/`soundness_evalR`/`soundness_behaviorsR_*` hold over both engines for the full core
      language **including let-polymorphism** (2026-06-19, `let_poly` delivered), `fix`, effects/`Handle`,
      records/unions/lists. `lake build` 1772 + spec 104/104, axioms clean, no `sorry`.

## Milestone T7 — Packaging & corollaries

**Deliverable:** `Eyg/Types/Soundness.lean` — the headline statements + hygiene.

- [~] `soundness : HasType [] prog τ ε → ∀ b ∈ BehaviorsR (Config.initial prog),
      b` is `terminates trace (value v)` with `HasTypeV v τ`, or
      `suspended`/`diverges` with **every** `perform op` in the trace satisfying
      `op ∈ ε`, and **never** `terminates _ (crash _)`. (T5/T6 preservation+progress
      folded over the trace + `outcome_unique`.)
      **Whole-program soundness over `evalR` DELIVERED** (`Eyg/Types/Soundness.lean`):
      `soundness_evalR` — a closed well-typed program's `evalR` at any fuel is a
      *timeout*, a *value of type `τ`*, a *sanctioned `Unrepresentable` crash* (never a
      type-error crash), or an *emitted effect `op ∈ ε`*. Built from the three pieces
      `soundness_evalR_value` / `soundness_evalR_noBadCrash` / `soundnessR_effect`
      (fuel induction folding `preservation_tau_fix` + `progress_fix`; the effect case
      threads `ε` across silent steps and reads membership off the effect-escape
      disjunct). All modulo the isolated `fix` (`FixPreserves`/`FixNoBadCrash`); axioms
      clean. The `BehaviorsR` substrate + `evalR_done_mem_behaviorsR`
      (`Eyg/Semantics/BehaviorR.lean`) connect `evalR` to `BehaviorsR`.
      **`BehaviorsR`-level soundness (silent terminations) DELIVERED**: the
      `MTr ⟶ evalR` bridge `evalR_complete` (`BehaviorR.lean`, the Reduce analogue of
      `eval_complete`) lifts the result to `soundness_behaviorsR_noBadCrash` /
      `soundness_behaviorsR_value` (`Soundness.lean`) — a well-typed program's *silent*
      terminating `BehaviorsR` behaviour is never a bad crash, and a terminating value
      is typed. Axioms clean. **`suspended` (open-boundary) soundness DELIVERED**:
      `evalR_complete_effect` (`BehaviorR.lean`, the suspended-run completeness bridge —
      a single-`perform` observable trace is realized by an `evalR` effect emission) +
      `soundness_behaviorsR_suspended` (`Soundness.lean`): a well-typed program that
      suspends performing `op` at the boundary does so on `op ∈ ε` (open-system effect
      safety). Axioms clean. **Headline `soundness` theorem DELIVERED**
      (`Eyg/Types/Soundness.lean`): the single bundled `soundness` — a closed well-typed
      program's every `BehaviorsR` behaviour is a silent typed value, a silent sanctioned
      crash (never a bad/type-error crash), or a boundary suspension on an in-row effect.
      Axioms clean. **`diverges` ω-effect-safety DELIVERED** (`Eyg/Types/Soundness.lean`):
      `soundness_behaviorsR_diverges` — a closed well-typed program's *divergent*
      `BehaviorsR` behaviour emits only `perform`s in its declared row `ε`. Built from
      `ωTr_all_wf` (every state along the infinite `reduceLTS.ωTr` execution stays
      well-typed at `(τ,ε)` — ordinary `ℕ`-induction folding the new `preservation_keep_fix`,
      the exact-`ε` variant valid for the pre-`Handle` fragment) + `ωTr_effect_safe`
      (`preservation_perform` reads `op ∈ ε` off each emitted boundary) + `reduce_perform_inv`.
      Conditioned on the world supplying well-typed replies along the witnessing execution
      (`ReplyContract` per step); axioms clean. **Reply-containing *terminating* traces
      DELIVERED** (`Eyg/Types/Soundness.lean`): `soundness_behaviorsR_terminates_value` /
      `_noBadCrash` — an *open* terminating `BehaviorsR` behaviour (whose trace may contain
      `perform`/`reply` labels, beyond the `evalR`-bridged silent case) yields a typed value
      / never a bad crash. Built from `mTr_terminal_wf` (fold `preservation_keep_fix` over the
      finite `reduceLTS.MTr`) + `terminalR_run`, conditioned on the trace-level
      `TraceRepliesOk` (every `Label.reply op v` carries a value inhabiting `op`'s declared
      reply type — the reply value lives in the label). Axioms clean. **Remaining:** discharge
      `fix`.
- [x] **Pure ⇒ effect-free** `pure_no_perform` (Eff's `A!∅` purity certificate)
      **DELIVERED** (`Eyg/Types/Soundness.lean`): `pure_no_perform_evalR` — a program
      typed at the **empty** effect row never has `evalR = .effect _ _ _` (the empty
      row is uninhabited, so `soundnessR_effect`'s `EffContains empty op` is impossible);
      and `soundness_evalR_pure` — a pure program's `evalR` is only timeout / typed value
      / sanctioned crash, never an emitted effect. Axioms clean. **Observable-level purity
      DELIVERED**: `pure_no_suspend_behaviorsR` (a pure program has *no* suspended
      `BehaviorsR` behaviour) and `pure_no_perform_diverges` (a pure program's divergent
      trace contains no `perform` label) — the `BehaviorsR` analogues of the `evalR`
      certificate, via `replyContract_empty` (the empty-row `ReplyContract` is vacuous).
      Axioms clean.
- [x] **Executable transfer to the shipped interpreter** (not a kernel claim):
      **DOCUMENTED** — the `Reduce≈step` agreement is enforced at build time via the
      `evalR`/`runR` `#guard` battery over the spec fixtures (`Reduction.lean`; `lake
      exe spec` 104/104), so the kernel soundness results over `BehaviorsR`/`evalR` hold
      *of the interpreter we actually run*. The `BehaviorR.lean` module docstring states
      the claim stays at the `Reduce` level (no kernel `eval`/`Behaviors` corollary), per
      the S5 convention.
- [x] Axiom hygiene: all headline soundness theorems print `propext`/`Classical.choice`/
      `Quot.sound` only (verified `soundness_evalR`/`soundness_behaviorsR_*`/
      `soundness_evalR_pure`); **zero `sorry` across the project** (`Eyg/`). The two
      `Fix*` hypotheses are explicit assumptions, not axioms.

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

- [x] **T0:** transparent `Reduce` + `evalR` ✅; `Reduce≈step` via build-time
      `#guard`s ✅; the opaque-`partial def` blocker resolved by reasoning over
      `Reduce` ✅; `BehaviorsR` ✅ (`Eyg/Semantics/BehaviorR.lean`). The dedicated
      `lake exe spec Reduce≡step` *reporting line* is still cosmetic-deferred (the
      `#guard` battery already enforces agreement at build time).
- [~] **T1–T2:** full `Ty` ✅; `RowEquiv`/`EffEquiv` proved an equivalence ✅ (+ the
      head/component inversion lemmas the proof needs ✅); schemes + builtin table ✅.
      `RowEquiv` decidability via normalization: deferred (not needed for the proof).
- [x] **T3 (the derisking checkpoint):** `progress`+`preservation`+`soundness_value`
      **green and sorry-free for the pure monomorphic core**, axioms clean, with the
      *final* judgment signatures (so later slices only add cases). The two builtin
      saturation obligations are isolated as the hypotheses `BuiltinAppPreserves` /
      `BuiltinAppNoBadCrash` (T6).
- [x] **T4/T5/T6 — ALL DELIVERED.** **T4 data** (records/unions/lists) ✅; **T5 effects** —
      `Perform` + effect safety ✅, **`Handle`/`Delimit` DELIVERED** ✅ (2026-06-17, the
      central novel slice; typing + `preservation`/`progress`/`soundness*` re-green over the
      full effect language via direct frame typing; `lake build` + spec 104/104, axioms clean,
      no new axioms; `ε`-free value/no-bad-crash unconditional incl. `Handle`; the three
      handler dispatches + the T7 row-evolution isolated as explicit hypotheses
      `HandlerObligations`/`TauKeepsRow` — `progress/2026-06-17-T5-handle-delivered.md`); **T6** — full builtin
      table + per-builtin run typing ✅ and the saturation obligations discharged for all
      general builtins ✅; **`fix`** — `partialFixed` + the `fixed` re-application proven ✅
      (`progress/2026-06-17-T6b-partialFixed-reapplication.md`), the fix *creation*
      (`FixPreserves`/`FixNoBadCrash`) still a hypothesis pending the (i)/(ii) discharge fork;
      **let-generalization `gen` — ✅ DELIVERED (2026-06-19, restricted `let_poly`,
      `progress/2026-06-19-T6-let_poly-DELIVERED.md`):** `HasType.let_poly` + value-aware
      `StackWfV`/`StackWfE` (+ B-mirror `StackWfVB`/`StackWfEB`) carrying the polymorphic readiness;
      `preservation`/`progress`/`soundness*` re-green over **both** engines; `lake build` 1772 + spec
      104/104, no `sorry`, axioms clean, no new `axiom`s; a polymorphic-`let` sanity example types.
      Residual under-approximations: the `noLet`-body restriction (no internal `let` in a generalized
      lambda — covers all combinator polymorphism) + the pre-existing pure-builder `fix` pin.
- [~] **T7:** headline `soundness` over `BehaviorsR` — value/no-bad-crash/effect-escape
      (`soundness_evalR`), silent terminations + open-boundary suspension over
      `BehaviorsR` ✅; **`diverges` ω-effect-safety** (`soundness_behaviorsR_diverges`) ✅;
      `pure_no_perform` ✅; executable transfer documented ✅; axioms clean ✅; zero `sorry`
      ✅; `lake build` + `lake exe spec` green ✅; **reply-containing terminating traces**
      (`soundness_behaviorsR_terminates_value`/`_noBadCrash`, via `TraceRepliesOk`) ✅;
      **`TauKeepsRow` ELIMINATED + `BuiltinAppPreservesB` discharged** ✅ (2026-06-18, the T7
      RowEvolves base-row engine — `StackWfB`/`preservation_*_B`/`stackWfB_escape`/
      `soundnessR_effect_B`; row-dependent soundness now gated on the `Fix*` family only;
      `progress/2026-06-18-T7-rowevolves-Bpreservation-delivered.md`).
      **`FixNoBadCrash` discharged** ✅ (2026-06-18, `fixNoBadCrash`).
      **`FixPreserves`/`FixPreservesB` DISCHARGED** ✅ (2026-06-18) — via the user-chosen
      pure-builder `fix`-scheme narrowing **+** the strict-under-application invariant
      (`PartialBuiltinWf`, closing the over-application gap that made the bare hypothesis
      unsatisfiable). `fixPreserves`/`fixPreservesB` proved; headline `soundness`/`soundness_evalR`/
      `soundness_evalR_pure` now take **only `HasType [] prog τ ε`** — *no isolated hypotheses
      remain*. Axioms clean, no `sorry`, `lake build` 1772 + spec 104/104. The single residual
      under-approximation vs. the reference analyzer is the pure-builder pin (effectful-builder
      `fix` ⇒ Open Question 3). See `progress/2026-06-18-fix-discharge-overapplication-blocker.md`.

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

1. **CEK frame typing vs. simulation, for effects** — ✅ **RESOLVED in favour of (a)
   direct frame typing** (2026-06-17, T5 delivered). `StackWf.delimit`/`StackWf.conv` +
   the conv-folding frame-inversion lemmas + `StackSegWf`/`stackWf_resume` typed the
   `Delimit`/`Resume` frames directly over the existing machine; the simulation fallback
   (b) was **not** needed. The continuation typing did not stall (the `StackWf.conv`
   inversion infra was the key enabler). Residual: the handler-dispatch + T7 row-evolution
   obligations are isolated as `HandlerObligations`/`TauKeepsRow` (follow-up, not a
   semantics fork). *(Original note: Direct `Delimit`/`Resume` frame typing (reuses the
   machine, novel) vs. a typed contextual semantics + a `Reduce`-simulates-it proof; try
   direct, fall back to simulation if continuation typing stalls.)*
2. **`Vacant` typing.** `do_infer` types `Vacant` at a fresh var but records an
   `Error` (the "todo/hole" node). It is *shape*-typeable yet its dynamic outcome
   is `crash (Vacant)`. Decide: **exclude `Vacant` from "well-typed"** (treat the
   recorded `Error` as not-well-typed — recommended, matches `do_infer`), or accept
   `crash Vacant` as the one sanctioned crash. Directly affects the no-crash
   statement; settle in T3 when the `HasType` rules are fixed.
3. **⚠ Effect weakening / row subsumption — NEWLY SURFACED (2026-06-16, by the `fix`
   attempt).** The current `StackWf.applyf`/`callwith` require a function's latent
   effect to **exactly equal** the frame's ambient row (mirroring gleam's
   `unify(test_eff, eff)`). This is fine for T3–T5 (every applied function's latent
   *was* the ambient by construction), but **`fix`'s unrolling applies the *pure*
   builder inside the effectful recursion ambient**, which exact-match cannot type —
   and likewise a **pure builtin can currently only be applied in a pure ambient**, so
   the effectful fragment has *no* effect weakening at all. Soundly typing `fix` (and a
   realistic effectful fragment) needs a **row-subsumption** extension — an
   `applyf`/`callwith` variant allowing the function's latent row to be a *sub-row* of
   the ambient (`ε_fun ⊑ ε`), plus a `RowSub` relation and its `TyEquiv`/`EffContains`
   metatheory. A core type-system change (touches `StackWf` and likely `HasType.app`),
   comparable in weight to `Handle`. Full diagnosis in
   `progress/2026-06-16-T6b-fix-scoping.md` (finding 3); it subsumes the earlier
   effect-consistency concern. **FOUNDATION DELIVERED** (2026-06-17,
   `progress/2026-06-17-T6b-effsub-foundation.md`): the `EffSub` (effect subrow)
   relation + its metatheory (`Eyg/Types/EffSub.lean`, green, axiom-clean, additive) —
   `effSub_refl`/`trans`, **`effSub_empty`** (the pure-function-under-effectful-ambient
   key), `tyEquiv_effSub` compat, guarded `effSub_extend`, `effContains_mono`,
   `effContains_extend_inv`. Membership-based, so effect safety survives weakening by
   construction. **Remaining:** the *consuming* slice, whose architecture is now settled
   (`progress/2026-06-17-T6b-effect-weakening-architecture.md`) with two rigorous results:
   **(1) irreducible core** — the `StackWf` application frames (`arg`/`applyf`/`callwith`)
   *must* carry `EffSub εf ε` (function latent `⊑` ambient); no surface design avoids it,
   because exact-match `app` makes term-level `weakenEff` non-admissible (covariance wall).
   **(2) chosen surface** — **generalize the `HasType.app` rule** (function latent `εf`
   with `EffSub εf ε`), which makes `weakenEff` admissible and touches **only `inv_app`**
   among inversions; the `subEff`-constructor alternative (cascades through all ~18
   inversions) is rejected. **⚠ Corrected premise (machine-checked counterexample):** the
   bare membership `Ty.EffSub εf ε` is **not** substitution-stable (`EffSub (var 0) .empty`
   holds vacuously but its `σ`-image `EffSub ⟨a⟩ .empty` is false), so it would break the
   existing `hasType_subst` (needed by `gen`/`let_poly`). The substitution-stable premise
   is `εf = ε ∨ εf = .empty` (the empty-restricted weakening — sufficient for `fix`'s pure
   builder and pure builtins; a general row-variable-aware subsumption is future work).
   Execution checklist (5 files, one atomic no-green-intermediate slice) is in the
   architecture note; session-sized, comparable to `Handle`. Closes the "pure builtin only
   applicable in a pure ambient" gap too (finding 3).
   **CONSUMING SLICE DELIVERED** (2026-06-17,
   `progress/2026-06-17-T6b-effect-weakening-consuming-slice.md`): `Ty.EffWeaken εf ε :=
   TyEquiv εf ε ∨ TyEquiv εf .empty` (the substitution-stable premise, implemented with
   `TyEquiv` not syntactic `=` so it absorbs `conv`'s ambient move and `weakenEff` needs no
   empty-inversion) is now the premise of the generalized `HasType.app` and of the
   `StackWf.arg/applyf/callwith` frames; `weakenEff` (admissible), `inv_app` (the only
   inversion that changed), `hasType_subst` (via `subst_effWeaken`), and the closure-
   application crux (re-types the body at the ambient) all green. The four builtin-
   saturation hypotheses were **decoupled** (function latent ⊥ stack ambient) rather than
   given an `EffWeaken` premise — the discharge never reads the function latent, so the
   T6a/T6b `run_*`/arity machinery is untouched. **Finding:** `hasTypeV_funWeaken` is *false*
   as a general value lemma (operator partials pin their latent rigidly) and *unnecessary* —
   the `fix` builder is applied through an `EffWeaken`-carrying frame, so the crux weakens it
   directly. All sorry-free, axioms clean, `lake build` + `lake exe spec` 104/104. **`fix`'s
   `partialFixed` slice is now unblocked** (apply the pure builder under the effectful
   ambient via `effWeaken_empty` at the pushed `applyf` frame).

   **⚠ CONVERGENCE (2026-06-17, after T5 Handle delivery + the partial discharge).** The
   *general* row subsumption this question is about (`tail ⊑ ε`, beyond the empty-restricted
   `EffWeaken`) is now the **single foundation gating three separate remaining items**:
   (i) **effectful-builder `fix`** (`Fix*` for `q1 ≠ ∅`); (ii) the **Handle dispatch
   discharge** — `resume`/`install` are proved only under an *exact* row (`resume_preserves_exact`/
   `install_preserves_exact`, banked green), and wiring them in needs a **generalized
   `StackWf.delimit`** that discharges `l` from the ambient with `tail ⊑ ε` (route b in
   `progress/2026-06-17-T5-handle-discharge.md`); (iii) **`TauKeepsRow → RowEvolves`** (the T7
   downward-`EffContains`-reflection across discharges depends on the same subsumption).
   So a single **`EffSub'` (substitution-stable, row-variable-aware subrow) foundation** is the
   highest-leverage next slice — it unlocks `fix` *and* fully discharges the Handle obligations
   *and* the T7 row-evolution. This is the clear top priority for the next foundational session.

4. **`fix` was UNSOUND at base-type fixpoints — now RESOLVED by hardening the scheme
   (2026-06-17; `progress/2026-06-17-fix-base-type-unsoundness.md`).** The fix: force the
   fixpoint to a **function** type. `contextual.gleam:530` is now
   `let self = t.Fun(q0,q2,q3); t.Fun(t.Fun(self,q1,self), q1, self)`, and the Lean
   `Builtins.scheme "fix"` (arity 4) mirrors it. **Verified by running the analyzer** (nix
   gleam): `!fix((x) -> { !int_add(x, 1) })` now gives `Error(TypeMismatch(Integer, Fun …))`
   (rejected), arrow-typed recursion still checks, full analyzer suite green; Lean `lake
   build` + spec 104/104, axioms clean. This also aligns the reference with
   `HasTypeV.partialFixed` (both force an arrow fixpoint), so that restriction is no longer a
   Lean-side divergence — the only remaining Lean under-approximation is the **pure-builder**
   pin (`q1` free in the scheme vs. `∅` in `partialFixed`), liftable via Open Question 3.

   <details><summary>Original counterexample (machine-checked, pre-fix)</summary>

   A closed program well-typed by the **reference analyzer** bad-crashed. Confirmed on all
   three legs:
   - **Typing (reference analyzer, executed via nix `gleam 1.17.0`):** the gleam `fix` scheme
     `(q0→⟨q1⟩q0)→⟨q1⟩q0` (`contextual.gleam:530`) leaves the fixpoint `q0` free. Running
     `j.infer` on `!fix((x) -> { !int_add(x, 1) })` gives top-level `#(Ok(Nil), "Integer", "")`
     — **no error, type `Integer`, pure**.
   - **Crash (both interpreters):** FBS `eval` *and* `evalR` reduce it to
     `Reason.IncorrectTerm "Integer" (Partial "fixed" [...])` (the `fixed` value is fed where an
     `Int` is expected; the cast fails).
   - **Badness:** `IncorrectTerm ∈ Reason.IsBad` (only `Unrepresentable` is sanctioned).
   So **type soundness for EYG's `fix` is FALSE** as specified by the analyzer; it holds only for
   the **arrow-fixpoint** fragment (`q0 = D→⟨γ⟩R`), which is what `HasTypeV.partialFixed` enforces
   and which covers all real recursion (the arrow-typed `fix (\self. \n. …)` infers fine). This
   is the classic call-by-value-`fix`-at-a-base-type unsoundness; the remedy is to restrict
   `fix`'s fixpoint to function types (or make the recursive binding lazy).

   </details>

   (Post-fix: the general `FixPreserves`/`FixNoBadCrash` remain isolated hypotheses,
   dischargeable for the **pure-builder** fragment via `partialFixed`; effectful builders
   (`q1 ≠ ∅`) await Open Question 3's effect-row subsumption.)

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
