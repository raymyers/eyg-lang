---
date: 2026-06-18
milestone: T6 — let-generalization (`gen`), declarative keystone
status: keystone DELIVERED (green, axiom-clean); the `let_poly` constructor cascade remains
---

# T6 `gen`: the declarative generalization keystone

## What was delivered

`Eyg/Types/Generalization.lean` (new, additive, green, axioms `propext`/`Quot.sound`):

- `Generalizes (s : Scheme) (Γ : Ctx) (defnTy : Ty) : Prop` — the **declarative**
  generalization predicate: *every* instantiation of `s` is a substitution instance
  `subst σ defnTy` with `σ` **fixing `Γ`** (`substCtx σ Γ = Γ`).
- `substScheme_id` / `substCtx_id` — the identity ambient substitution fixes a scheme /
  context (the quantifier-prefix shift cancels).
- `generalizes_mono` — the monomorphic scheme is the trivial (`arity = 0`) generalization,
  so monomorphic `let` is the degenerate `let_poly`.
- **`generalizes_closure_ready`** (the keystone) — for a value-restricted `let` whose `defn`
  is a `λ`, `Generalizes` discharges *exactly* the `EnvWf.cons` polymorphic-readiness clause
  `∀ args, HasTypeV v (s.instantiate args)`, by composing the predicate with the
  already-delivered `closure_typed_of_lambda_subst` (`Substitution.lean`).

## Why this route (and why it sidesteps the documented blocker)

The earlier scoping note (`2026-06-16-T6-gen-scoping.md`) flagged two obstacles:

1. **Computing a principal `gen`** (re-index generalizable vars to `0..arity-1`, shift
   ambient vars up) — fiddly de Bruijn bookkeeping.
2. **The deepened `MStateWf`-freshness blocker** (`eyg-type-soundness.md` T6 item): the
   value-substitution lemma is false for open rows, and `HasTypeV.closure`'s captured
   context is existential, so `FV(Γcap) ⊆ FV(Γ)` is not recoverable post-hoc — seemingly
   forcing an invasive context-freshness invariant through `MStateWf`.

Both are **avoided**:

- **(1)** The judgment is *declarative* (`HasType.var`/`builtin` already quantify over
  arbitrary instantiation `args`, not principal types). So `let_poly` will quantify over
  *any* `s` with `Generalizes s Γ defnTy`; we never compute `gen`. Producing such a scheme
  is the (separate, T8) inference layer.
- **(2)** The **value restriction** + `closure_typed_of_lambda{,_subst}` types the closure at
  the **known** evaluation context `Γ` from the let site (no existential), and `Generalizes`
  guarantees each instantiation `σ` fixes that same `Γ`. So no `MStateWf` freshness invariant
  is needed for the closure case. (A `λ` reduces to its closure in one step, so the Assign
  frame pops with the let-site `Γ` still in hand.)

## What remains for the full `let_poly` slice (next, atomic)

Adding the rule is the build-breaking, atomic part (a new `HasType` constructor breaks
`hasType_expr_form` + every `induction h` over `HasType` in preservation/progress):

1. `HasType.let_poly` — `HasType Γ defn defnTy ε → IsSyntacticValue defn → Generalizes s Γ
   defnTy → HasType ((x, s) :: Γ) body τ ε → HasType Γ ⟨Let x defn body, a⟩ τ ε`. The value
   restriction is needed because the soundness route is closure-specific (any-`defn`
   monomorphic `let` keeps the existing `HasType.let_`).
2. `inv_let_poly` + extend `hasType_expr_form`'s `Let` disjunct to cover `let_poly`.
3. Preservation: the `Let`-eval-step (push `Assign`) is rule-agnostic; the **`Assign`-pop**
   case for a generalized binding uses `generalizes_closure_ready` to build `EnvWf.cons` for
   `(x, s)`. The `StackWf`/`StackWfB`/`StackSegWf.assign` frame must carry a scheme (currently
   pins `.mono defnTy`) — generalize it (or add a parallel `assignGen` constructor) to an
   arbitrary `s` with the stored `Generalizes` witness. **~20 sites** across the three frame
   typings and their B-mirrors / perform-walk cases — an atomic, all-or-nothing cascade
   comparable in weight to `Handle`.
4. Re-green `progress` (new `let_poly` node case — same reduction as `let_`).
5. A typing `example` exercising polymorphic reuse (e.g. `let id = \x.x in (id 1, id "a")`).

This cascade is the genuine multi-file slice; the keystone above is its hardest *semantic*
lemma (closure polymorphic readiness without a value-substitution lemma), now banked green.

## ⚠ Sharpened finding (surfaced this session) — the `Assign`-frame ↔ control invariant

`generalizes_closure_ready` needs the lambda typed at the **specific** let-site `Γ`
(`HasType Γ ⟨Lambda…⟩ defnTy ε` + `EnvWf fenv Γ`). But at the `Assign`-pop step the incoming
value's typing is only `HasTypeV (Closure x' b' fenv) defnTy`, whose `HasTypeV.closure`
inversion exposes an **existential** captured context `Γcap` (and `EnvWf` is non-unique), so
the keystone is **not** directly applicable from the value typing — this is the same
existential-capture wall the `eyg-type-soundness.md` T6 "deepened finding" named.

### Why the easy route is *provably* impossible (rigorous, this session)

The tempting shortcut is to make the generalized `assign` frame carry poly-readiness as a
**value-agnostic** stored premise, so the `Assign`-pop discharges `EnvWf.cons` directly from
the arriving `HasTypeV v defnTy`:

    (Pready)  ∀ v, HasTypeV v defnTy → ∀ args, HasTypeV v (s.instantiate args)

This is **exactly the false value-substitution lemma** the module header of
`Substitution.lean` records — `Pready` would give `HasTypeV v defnTy → HasTypeV v (subst σ
defnTy)` for the instantiating `σ` — and it is false **even when `defnTy` is an arrow** (the
value-restricted case): `v` may be a `Closure` that *captured* a variable typed at an open row
`{r | β}`; the generalizing `σ` fixes only the variables generalized away from `Γ`, not the
closure's captured `β`, so `subst σ` adds a field the captured value lacks and the re-typing
fails. So `Pready` cannot be a frame premise — the `assign` frame **cannot** soundly carry
poly-readiness without being coupled to *which* value arrives. This is not an incidental
inconvenience; it is forced by the same open-row obstruction that defeats `hasTypeV_subst`.

The corollary: the `Assign`-pop case genuinely only sees "*some* `v` with `HasTypeV v
defnTy`" (it `cases` on the reduction, which is value-agnostic), so it *cannot* know `v` is the
closure built from the let's `λ` without a **machine-level coupling invariant**.

### The forced design (next session, milestone slice — not a mechanical edit)

The generalized/`assignGen` frame must **store the let-site facts** — `Γ`, `EnvWf fenv Γ`, the
lambda typing `HasType Γ ⟨Lambda x' b'⟩ defnTy ε`, the scheme `s`, `Generalizes s Γ defnTy`,
and the body typing under `(x,s)::Γ` — and preservation must carry an **`MStateWf`-level
invariant** linking the frame's stored lambda to the control between push and pop (the
control *is* that lambda until it reduces, deterministically, to `Closure x' b' fenv`, which
is exactly what the frame stores its `fenv`/lambda for). With those stored facts the
existential `Γcap` from the value typing is **bypassed** — `generalizes_closure_ready` is fed
the *stored* `Γ`-typing instead. The value restriction makes the invariant tractable (the
bound `defn` is syntactically a `λ`, so between push and pop the control is in one of exactly
two states: the stored `λ`, or its closure value), but the invariant threads through every
`MStateWf` consumer (the same surface `Handle`/`TauKeepsRow` touched), so it is a focused
milestone slice. The semantic keystone (`generalizes_closure_ready`) makes the payoff a
one-liner once the stored `Γ`-typing is in hand — that hardest *semantic* obligation is banked.

## Verified
- `lake build` 1772 jobs green; `lake exe spec` 104/104; `#print axioms` on the three new
  results → `propext`/`Quot.sound` only; no `sorry`, no new `axiom`s.
