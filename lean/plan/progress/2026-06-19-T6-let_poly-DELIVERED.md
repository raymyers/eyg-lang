---
date: 2026-06-19
milestone: T6 — let-polymorphism (`let_poly`) DELIVERED (full two-engine soundness, green, axiom-clean)
status: DELIVERED
---

# T6 `let_poly` — DELIVERED

The restricted-`let_poly` slice is **complete and green**: `HasType.let_poly` is in the judgment and
`preservation`/`progress`/`soundness*` re-green over **both** preservation engines (the E-world
`MStateWf`/`StackWf` and the base-row B-world `MStateWfB`/`StackWfB`). `lake build` 1772 + `lake exe spec`
104/104; no `sorry`; headline axioms `propext`/`Classical.choice`/`Quot.sound`; **no new `axiom`s**.

## What landed

- **`HasType.let_poly`** (value-restricted: `defn = ⟨.Lambda lx lbody, la⟩`): scheme pinned to the computed
  `Scheme.genAt n defnTy`, with premises `CtxWf n Γ` (context below the level) and **`Tree.Node.noLet
  lbody`** (the generalized body has no internal `let` — the restriction that keeps `hasType_subst`
  arbitrary-σ with vacuous `Let` arms, per the instantiation-vs-`LevelMap` finding). `inv_let` unified to a
  mono/poly disjunction; `hasType_ctxConv`/`hasType_expr_form`/`weakenEff` arms; `hasType_subst` handles it
  (vacuous via `noLet`); readiness keystone `genAt_closure_ready` (green, no `LevelMap` needed).
- **Value-aware stack typing** `StackWfV`/`StackWfE` (+ B-mirror `StackWfVB`/`StackWfEB`): the `Assign` head
  carries the polymorphic **readiness** `∀args, HasTypeV v (sc.instantiate args)`; `StackWfE` carries the
  future closure's readiness (λ-control) and the `sc = .mono defnTy ∨ control-is-λ` invariant (rules out an
  arrow-typed builtin `Partial` on a poly assign). `StackWf.assign` kept **mono-only** (poly assigns are
  transient — created at the let-push, popped one step later — so they never persist in a plain stack),
  which makes `stackWf_toStackWfV`/`_toStackWfE` (and the B-mirrors) **unconditional** — the lever that
  re-greens every frame/effect case producing a value on a reorganized stack.
- **Both engines re-greened**: `MStateWf`/`MStateWfB` value cases use `StackWfV`/`StackWfVB`, E cases use
  `StackWfE`/`StackWfEB`; the let-push builds the poly/mono `StackWfE(B)` Assign frame (poly readiness via
  `genAt_closure_ready`, mono via `closure_typed_of_lambda`); the Assign-pop consumes the carried readiness
  into `EnvWf.cons`; the λ→closure step hands `Rdy` over (`stackWfE(B)_lambda_step`); every other value
  producer wraps via `stackWf_toStackWfV(B)` (mono-trivial or vacuous-by-types).

## Significance

`let_poly` was the last substantive core item of the soundness plan. With it, **the headline soundness
(`progress`/`preservation`/effect-safety/no-bad-crash, value + behaviours, E-world; effect-escape/
divergence, B-world) holds for the full core language including let-polymorphism**, modulo the documented
under-approximations (the `noLet`-body restriction on generalized lambdas — rules out internal `let` inside
a polymorphic function, covering all combinator polymorphism; and the pre-existing pure-builder `fix` pin).

The design arc that got here (multi-session): the de-Bruijn-level algebra (`LevelMap.mono`, `genAt`
substitution-stability), the `CtxWf` free-var metatheory, the **instantiation-vs-`LevelMap` finding** (which
re-scoped to the restricted `noLet` route, sidestepping the level machinery), and the value-aware
`StackWfV`/`StackWfE` coupling with the **mono-only-`StackWf.assign`** insight (poly assigns transient).
