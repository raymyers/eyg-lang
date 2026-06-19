---
date: 2026-06-18
milestone: T6 — `let_poly`: a design-level finding (instantiation ≠ LevelMap) from wiring `hasType_subst`
status: FINDING (corrects the established "generalizesAt_subst suffices" assumption); restricted ship identified
---

# `let_poly` — the readiness substitution is the INSTANTIATION, which is not a `LevelMap`

Continuing the cascade (after the typing layer landed, `2026-06-18-T6-let_poly-cascade-attempt.md`), I
wired `hasType_subst`'s `let_poly` arm and the readiness keystone, and **discovered a real gap the prior
sessions missed**: the substitution the keystone actually feeds to `hasType_subst` is the **instantiation**
witness, and that witness is **not a `LevelMap`** — so the `generalizesAt_subst`/`genAt_substScheme`
infrastructure (built for *ambient* level-map substitutions) does **not** directly serve the keystone.

## The mechanism

Readiness needs `∀ args, HasTypeV (Closure …) ((Scheme.genAt n defnTy).instantiate args)`. By
`genAt_generalizesAt`, `(genAt n defnTy).instantiate args = Ty.subst σ_args defnTy`, and
`closure_typed_of_lambda_subst` re-types the lambda **body** under `σ_args` (via `hasType_subst σ_args`).

Two facts collide:
1. With the `let_poly` constructor present, `hasType_subst` for an **arbitrary** `σ` is **false**
   (`generalizes_subst_false`), so it must be restricted to `LevelMap n σ`.
2. The `genAt_generalizesAt` witness `σ_args` maps `v ≥ n+arity` to `var (v − n − arity)` (a **down-shift**),
   so it is **not** the identity on `[n+arity, ∞)` — hence **not a `LevelMap` at any level**. The
   `LevelMap`-restricted `hasType_subst` therefore **cannot be applied to `σ_args` at all**.

So the keystone cannot re-type a body that contains a **nested `let_poly`** (whose generalized vars `σ_args`
would disturb) — exactly the `generalizes_subst_false` failure, now re-surfacing at the keystone.

## Partial rescue (LevelMap witness) and where it still fails

`FV(defnTy) ⊆ [0, n+arity)` (from `genArity_spec`: free vars `≥ n` satisfy `v − n < arity`). So `σ_args`'s
behaviour on `[n+arity, ∞)` is **free** — choosing the **identity** there gives a witness `σ'` with
`subst σ' defnTy = subst σ_args defnTy` (agree on `FV(defnTy)`) that *is* a `LevelMap (n+arity)` **iff the
instantiation `args` have `FV ⊆ [0, n+arity)`** (the middle band `[n, n+arity) ↦ args` must stay in range).
Then nested generalized vars (`≥ n_inner ≥ n+arity`) are **fixed** by `σ'`, the nested generalization is
preserved, and the `WfLevel` gate (`n+arity ≤ n_inner`) closes the arm.

**But `args` are arbitrary** (the `∀ args` readiness): a polymorphic function used at a **locally-bound**
type (e.g. `\y. id y`, instantiating `id` at `y`'s fresh var `≥ n+arity`) has **high `FV(args)`**, so `σ'`
is **not** a `LevelMap`. The rescue covers only low-args instantiations.

## The decisive split (what is actually shippable)

- **Generalized lambda body has NO nested `let_poly`** → the body's derivation never reaches the
  `let_poly` arm, so `hasType_subst` works for an **arbitrary** `σ` (incl. high-`args` `σ_args`) via the
  *existing* arms — **no `LevelMap`, no gap**. This covers `\x.x`, `\x.\y.x`, `\f.\x. f (f x)`, and **every
  polymorphic function without internal let-generalization** — the vast majority of real let-polymorphism.
- **Generalized lambda body HAS nested `let_poly`** → genuinely hard (the high-`args` × nested-generalized
  interplay above). Rare in practice.

So the **practical ship is the restricted `let_poly`**: forbid nested let-generalization inside a
generalized lambda body, and `hasType_subst` is the *original arbitrary-`σ`* lemma (the `let_poly` arm made
**vacuous** by the restriction). This **sidesteps the `LevelMap`/instantiation gap entirely** and needs
none of the `generalizesAt_subst`/`genAt_substScheme` machinery (which stays committed-green for the future
full version).

### Wiring wrinkle for the restriction

The restriction is "the bound lambda's body derivation has no `let_poly`" (`NoLetPoly`, a derivation
predicate). It **cannot be a `let_poly`-constructor premise** (a cycle — `NoLetPoly` references `HasType`,
which would reference it back). Two clean routes:
- **(a) syntactic over-approximation** `NoLet`/`NoGenLet` on the lambda **body term** (definable *before*
  `HasType`, so it *can* be a constructor premise) — simplest, but a `NoLet` body also forbids *mono* lets
  inside polymorphic functions (a real but tolerable limitation for a first ship).
- **(b) a top-level program well-formedness** `ProgWf` (generalized lambdas have no nested generalization)
  threaded through preservation as the *light, unchanging* invariant — keeps full internal `let` use but
  the engines carry one constant side-hypothesis (same shape as the let-level invariant already planned).

## Recommendation for the next session

1. **Ship restricted `let_poly` first** (route (a) or (b)): the `let_poly` constructor + the original
   arbitrary-`σ` `hasType_subst` (vacuous `let_poly` arm) + `genAt`/`CtxWf` readiness (`genAt_closure_ready`,
   already green) + the value-aware `StackWfV` two-engine coupling (the remaining bulk, unchanged). Delivers
   rank-1 let-polymorphism for all non-nested-generalization programs — essentially the whole language in
   practice.
2. **Defer full nested `let_poly`** to a focused follow-up: it needs readiness **without re-substituting the
   body under instantiation** — e.g. typing closures at *schemes* with lazy/structural instantiation, or a
   genuinely instantiation-stable generalization. The `LevelMap`/`generalizesAt_subst` route does **not**
   close it (this note's core finding) without also solving the high-`args` case.

## State

Tree green at the infra commits (`LevelMap.mono`, `CtxWf` metatheory, `genAt` algebra — all still useful
for the full version). The typing-layer cascade (constructor, `inv_let` disjunction, `hasType_ctxConv`/
`hasType_expr_form` arms) remains valid and is preserved in `2026-06-18-T6-let_poly-cascade-WIP.patch`. The
`hasType_subst`-via-`LevelMap` attempt was reverted — this finding shows it is **not** the right tool for
the keystone; the restricted-ship route (arbitrary-`σ` `hasType_subst`, vacuous `let_poly` arm) is.
`lake build` 1772 + `lake exe spec` 104/104.
