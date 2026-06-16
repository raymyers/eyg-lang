# Type Soundness for Abstract Machines (CEK, typed continuations)

> Reference summary for the EYG type-soundness plan (`../eyg-type-soundness.md`),
> milestone **T4 — Semantic typing: values, environments, stacks, configs** (and
> the T0 decision that the step relation must be a transparent inductive). The
> "continuation as answer-type transformer" recipe for `StackWf`, plus
> environment/closure typing that replaces the substitution lemma.

**Citation / source URLs:** Pfenning, *Call-by-Push-Value* (15-816 Lecture 21)
https://www.cs.cmu.edu/~fp/courses/15816-f16/lectures/21-cbpv.pdf · Harper, *PFPL
Supplement: Programming with Continuations*
https://www.cs.cmu.edu/~rwh/pfpl/supplements/letcc.pdf and *PFPL* 2nd ed. Ch. 28
(K machine) https://www.cs.cmu.edu/~rwh/pfpl/ · Aldrich, *Lecture Notes:
Soundness* (17-363)
https://www.cs.cmu.edu/~aldrich/courses/17-363/notes/lecture10-soundness.pdf ·
Wright & Felleisen, *A Syntactic Approach to Type Soundness*, Inf. & Comp. 115(1),
1994 https://dl.acm.org/doi/10.1006/inco.1994.1093 · Amin & Rompf, *Type Soundness
Proofs with Definitional Interpreters*, POPL 2017, and *From F to DOT*
https://arxiv.org/pdf/1510.05216 · "A Soundness Proof of STLC by Definitional
Interpreters in Agda" https://continuation.passing.style/blog/stlc-soundness.html
· Felleisen, Findler, Flatt, *Semantics Engineering with PLT Redex*, MIT Press
2009.

*Accuracy note:* Pfenning's CBPV notes, Harper's supplement, Aldrich's notes, and
the Agda STLC blog were read in full; their rules are transcribed faithfully. The
exact rendering of PFPL Ch. 28's `k ÷ τ` stack-typing and Wright–Felleisen's typed
evaluation contexts is recalled from the standard literature; the *shape* is
reliable, but transcribe a primary copy before quoting verbatim.

---

## 1. The "well-typed configuration / state" approach

For terms, soundness is the Wright–Felleisen pair: **Progress** `• ⊢ e : τ ⟹ e
value ∨ ∃e'. e → e'`; **Preservation** `Γ ⊢ e : τ ∧ e → e' ⟹ Γ ⊢ e' : τ`.
Together: a well-typed term is never **stuck** (= not a value, no rule applies).

For an **abstract machine** the object that steps is a *configuration* `σ`
(CEK: `Control × Env × Stack`). Once you have a single judgment `⊢ σ ok`
(equivalently `⊢ σ : τ_answer`):

- **Progress (machine):** `⊢ σ ok ⟹ σ final ∨ ∃σ'. σ ↦ σ'`. A *final* CEK state is
  empty stack returning a value: `⟨ return v, ε ⟩`.
- **Preservation (machine):** `⊢ σ ok ∧ σ ↦ σ' ⟹ ⊢ σ' ok` (answer type unchanged).
- **Soundness corollary:** a well-typed `σ` runs forever or reaches `final`; never
  stuck.

The key design decision: **`⊢ σ ok` must mention the stack's type**, because the
remaining work on the stack is what makes a returned value safe to consume.

## 2. Continuation/stack typing as an answer-type transformer (the key piece)

A stack `K` is typed by **two** types: the type `A` it consumes in its hole, and
the **answer** type `B` the whole machine produces. Read as a function on types:

```
K : A ⇒ B        -- "K consumes a hole of type A and yields answer B"
```

(Pfenning writes `A ⊢ K : B`; Harper packages the reified stack as `cont(k) : τ
cont` with `τ` the hole type.)

**Empty stack = identity transformer; frame push = composition:**

```
─────────────  (K-empty)            f frame: hole A ↝ A'   K : A' ⇒ B
ε : A ⇒ A                           ────────────────────────────────  (K-push)
                                    (f ⊳ K) : A ⇒ B
```

A stack is a right fold of frame transformers; the global answer `B` threads
through the bottom. Each frame's type is read off the step rules. Pfenning's
frames (verbatim shape):

```
·⊢ V : A⁺                          x:A⁺ ⊢ N : C⁻
─────────────────────────          ─────────────────────────────────────
A⁺→B⁻ ⊢ cont(_ V) : B⁻            ↑A⁺ ⊢ cont(let val x = _ in N) : C⁻
```

**Configuration rule** (the whole game):

```
control produces type A        K : A ⇒ B
─────────────────────────────────────────   (⊢ σ ok)
⊢ ⟨ control ; K ⟩ : B
```

The invariant: *the type the control will deliver = the hole type the stack is
waiting for*, and the stack composes hole/answer types down to the program answer.

## 3. Environment and closure typing (no substitution)

An environment machine never substitutes; a function value is a **closure**
`⟨λx.e, ρ⟩`. Soundness needs two judgments, **mutually inductive**:

**Closure typing** — type the body against the *captured* env's context, extended
with the parameter:

```
wf-env ρ Γ        (τ₁ ∷ Γ) ⊢ e : τ₂
────────────────────────────────────────   (ty-clo)
⊢ ⟨ λx.e , ρ ⟩ : τ₁ → τ₂
```

**Environment typing** — lock-step, pointwise:

```
─────────────         ⊢ v : τ      ρ : Γ
[] : []               ──────────────────────
                      (v ∷ ρ) : (τ ∷ Γ)
```

Variable lookup is sound by a **lookup lemma**: `ρ : Γ ∧ Γ ∋ x:τ ⟹ ⊢ ρ(x) : τ`.
This replaces the variable case of the substitution lemma. **Partially-applied
primitives** get a value-typing rule recording the residual arrow type (e.g.
`⊢ add₁(n) : nat → nat`); canonical forms then treats them as any arrow value.
(Amin–Rompf: realistic languages "lack a general substitution property," so do
soundness over a definitional interpreter with exactly these relations.)

## 4. Progress via canonical-forms at the machine level

Machine Progress = case split on **(control, top frame)**, each closed by a
canonical-forms lemma about the *value* whose type is known:

- **Control = evaluate `e`:** variable (looked up — total because `ρ : Γ`),
  literal/constructor (returns a value), or eliminator (pushes its frame). Always
  steps.
- **Control = return value `v`, stack = `f ⊳ K`:** inspect `f`. Its hole type is
  known; `⊢ v :` hole type; canonical forms gives `v`'s shape so the reduction
  fires. (apply-frame ⟹ closure or partial prim ⟹ β/builtin; let-frame ⟹ bind;
  handler/resume frame ⟹ delimit/resume rule.)
- **Control = return value, stack = `ε`:** *final*.

No frame can be stuck: stack typing guarantees the returned value's type matches
the frame's hole, and canonical forms converts that type into the syntactic shape
the rule needs.

## 5. Substitution-machine vs environment-machine

| Substitution / contextual machine | Environment (CEK) machine |
|---|---|
| **Substitution lemma** (workhorse, needs weakening + exchange) | **Gone.** Replaced by closure typing + env typing + lookup lemma. β just extends `ρ`. |
| Variable case of Progress vacuous at `•` | Variable case real; discharged by `ρ:Γ` + lookup. |
| α-conversion / capture-avoidance | None — binding is env extension; names are lookup keys. |
| Evaluation-context typing (Wright–Felleisen) | **Stack typing `K : A ⇒ B`** is the reified, defunctionalized evaluation context. |
| — | New lemmas: env weakening/lookup; closure-typing well-foundedness (mutual induction); per-frame inversion; `K-push` preserves the transformer. |

Preservation: each `↦` rule either (i) pushes a frame — old `control:A`, new top
frame `:A⇒A'`, tail unchanged, composite answer preserved; or (ii) pops/consumes a
frame on a return — frame-typing inversion + (for β) closure typing + env
extension to retype the new control.

## 6. Mechanizing machine soundness

1. **Make the step relation a transparent inductive `Step : Config → Config →
   Prop`, not a function.** Preservation is `cases`/`induction` on the `Step`
   derivation — only works if each rule is a separately-invertible constructor. A
   `def step : Config → Option Config` (opaque executable function) blocks
   rule-by-rule case analysis. *If you also want an executable machine, define the
   function separately and prove `stepFn σ = some σ' ↔ Step σ σ'` ("tie the
   knot").* (This is the repo's S5 pattern.)
2. **Four typing judgments as mutually-inductive `Prop`s** (`HasTypeV`, `EnvWf`,
   `StackWf`, `ConfigWf`); `HasTypeV`/`EnvWf` mutually recursive through the
   closure constructor (`mutual … inductive … end`). Prefer structural lock-step
   `EnvWf` over `∀ x, …` for free induction principles.
3. **`StackWf` carries the two type indices** — `inductive StackWf : Stack → Ty →
   Ty → Prop`, `StackWf.nil : StackWf [] A A`, one `cons` per frame. This *is*
   `A ⇒ B`. Then `ConfigWf σ B := ∃ A, ControlWf control A ∧ StackWf stk A B`.
4. **Canonical-forms lemmas as standalone `Prop`s** keyed by value type.
5. **Inversion is the main tool** (`cases`/`rcases`); keep constructors injective
   and non-overlapping.
6. **No fuel needed** for progress+preservation (partial correctness). An
   executable-interpreter soundness (Amin–Rompf style) is a separate fuel-indexed
   corollary — don't entangle.

## Relevance to the EYG Lean proof

Shapes to define, matching CEK state `Control × Env × Stack`:

- **`HasTypeV : Value → Ty → Prop`** mutually inductive with `EnvWf`. Closure rule:
  `EnvWf ρ Γ → HasType (Γ.push (x, τ₁)) body τ₂ → HasTypeV (Value.closure x body ρ)
  (Ty.arrow τ₁ τ₂)`; plus one rule per partially-applied primitive (residual
  arrow). No substitution — captured `ρ` typed by an existentially-recovered `Γ`.
- **`EnvWf : Env → Context → Prop`** lock-step; prove **lookup lemma** `EnvWf ρ Γ →
  Γ.lookup x = some τ → ∃ v, ρ.lookup x = some v ∧ HasTypeV v τ`. Replaces the
  substitution lemma.
- **`StackWf : Stack → Ty → Ty → Prop`** = the answer-type transformer (§2). One
  `cons` per EYG frame (`Arg`/`Apply`/`Assign`/`CallWith`/`Delimit`/`Resume`), each
  consuming hole `A`, exposing answer `A'` for the tail; read its type off the
  matching step rule. The **`Delimit`/handler frame** is the continuation frame
  whose hole is the effect's return type and which discharges an effect from the
  row (cross-ref `algebraic-effects-handlers-soundness.md` §3–4). For `Resume`, the
  resumed continuation value is itself typed `A ⇒ B`; reach for a step-indexed
  logical relation (Ahmed) **only if** handlers can re-invoke continuations with
  circular/recursive effect typing — for a stack-of-frames `resume`, plain mutual
  induction usually suffices.
- **`ConfigWf σ B := ∃ A, ControlWf σ.control σ.env A ∧ StackWf σ.stack A B`**
  (`ControlWf` = `HasType Γ e A` with `EnvWf σ.env Γ` for an expr-control, or
  `HasTypeV v A` for a return-control).
- **Theorems:** `Progress : ConfigWf σ B → Final σ ∨ ∃ σ', Step σ σ'`;
  `Preservation : ConfigWf σ B → Step σ σ' → ConfigWf σ' B`. Keep `Step` a
  transparent inductive; if you have an executable `stepFn`, prove the
  iff separately.

The one invariant to keep front-of-mind: *the type the control will deliver equals
the hole type the stack waits for, and the stack composes those down to the
program's answer.* Define `StackWf` as the two-index transformer and that
invariant **is** `ConfigWf`.
