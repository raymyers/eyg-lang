# G2 residual-reachability prove-or-refute — RESOLVED by V8

Date: 2026-07-10. Machine-checked witness `Eyg.Types.G2Validation.v8` (builds clean, axioms
`[propext, Quot.sound]`). Resolves the question left open by
`2026-07-09-G2-routeB-fullRaise-floor-lift-route.md`.

## Question

Is the "interleaving" case — a binding whose `retTy` carries an inner-lambda-binder level `m` *above*
an inner `let_poly` gen level `k` (both `≥` the binding's sublevel), consumed at a colliding
instantiation — reachable by a well-typed program? And if so, is readiness still true there?

## Answer (both parts, machine-checked)

**Yes reachable, and yes readiness still holds.** V8 is the depth-2 chain G16 only suspected
(its note line 114: "a depth-2 chain plausibly can"):

```
closure  \x. (let g = \y.y in \w. g x)     -- type α → (γ → α)
scheme   genAtV 1 (.var 1 0 → (.var 3 0 → .var 1 0))
target   instantiate at [.var 2 0]  ⇒  .var 2 0 → (.var 3 0 → .var 2 0)
```

The *natural* stored derivation generalizes `g` at `b`'s sublevel 2, interleaving with the `retTy`
binder level 3: no threshold `raiseTy t o` can move `g` (needs `t ≤ 2`) while fixing `retTy`'s level 3
(needs `t > 3`). **Yet the value is typeable** — V8 generalizes `g` **fresh at 5**, and the colliding
lookup `g @ [.var 2 0]` no longer captures. `HasTypeV` derivation constructed, compiles.

## Consequences for route B

1. **Route B is NOT refuted** — readiness is *semantically true even in the interleaving case*
   (V1–V8). Unconditional soundness remains achievable in principle. The user's instinct holds.
2. **The threshold raise (`hasType_fullRaise` / floor-lift) alone is INSUFFICIENT** — V8
   machine-confirms the interleaving that blocks it, resolving G16's open suspicion. The
   fullRaise-lifts-the-floor route (previous note) closes only the *non-interleaving* case (all
   combinator polymorphism); V8 is outside it.
3. **The difficulty is purely proof-architectural, not semantic.** A *fixed* stored derivation
   transported by a threshold raise cannot reach the fresh-`g` derivation; a **fresh re-derivation**
   (re-picking inner gen levels above the args) can — that is exactly what V8 does by hand.

## What this means for the next step

Unconditional route B needs one of:

- **(B1) The type-fixed structural relabel** — rename inner `let_poly` gen levels freely (keeping
  types/context fixed), the mechanism that "re-derives fresh". This is G16's *type-fixed two-modes*
  raise, walled at nesting depth ≥ 2 — and V8 is precisely a depth-2 instance, so it is the concrete
  target/obstacle. Now well-motivated and better-equipped (`hasType_substAt_multi` + the full
  `raiseTy`/relabel toolkit). Hard but the honest path to unconditional.
- **(B2) Re-architecture** — store on `HasTypeV.closure` enough to *re-derive* the body fresh per
  instantiation (a generation/principal-typing style witness) rather than a single fixed derivation,
  so readiness is `∀ args` by construction. Larger design change.
- **(A) Fallback** — the per-binding floor promise (route A); soundness for args-disciplined
  derivations. Covers everything V1–V8 *as written* but is conditional.

Recommendation: the decision is now well-posed and evidence-backed. (B1) is the principled path to
the user's unconditional goal; V8 is its minimal test case (a proof of the type-fixed relabel must
handle exactly V8's shape). Suggest tackling the type-fixed relabel against V8 as the concrete
depth-2 target — if it handles V8, it handles the wall.
