---
date: 2026-06-18
milestone: T6 — restricted `let_poly`: the StackWfV/StackWfE coupling design (with edge cases) + StackWf.assign generalized
status: WIP (StackWf.assign generalized green; full V/E coupling design worked out incl. edge cases)
---

# Restricted `let_poly` — the `StackWfV`/`StackWfE` coupling design, edge cases resolved

Continues `2026-06-18-T6-let_poly-restricted-keystone-green.md`. The gen branch + readiness keystone are
green (restricted route). This session generalized **`StackWf.assign` to store a scheme `sc`** (mono
callers infer `sc = .mono defnTy`; `stackWf_assign_inv` now returns `sc`) — green, in the WIP patch — and
worked out the **complete `StackWfV`/`StackWfE` coupling including the edge cases** a naive design misses.

## The two predicates (recursive defs, value-aware only where it matters)

**`StackWfV v k σ ε τ`** (the V-state stack typing — value `v` flows in):
```
| []                       => StackWf [] σ ε τ
| (Trace _,_)::rest        => StackWfV v rest σ ε τ          -- v passes through
| (Assign x body fenv,_)::rest =>
    ∃ Γ sc bodyTy, (∀ args, HasTypeV v (sc.instantiate args))   -- READINESS about THIS v
      ∧ EnvWf fenv Γ ∧ HasType ((x,sc)::Γ) body bodyTy ε ∧ StackWf rest bodyTy ε τ
| k (Arg/Apply/CallWith/Delimit head) => StackWf k σ ε τ    -- head consumes v
```

**`StackWfE e env k σ ε τ`** (the E-state stack typing — control `e`, which will become a value):
```
| (Trace _,_)::rest  => StackWfE e env rest σ ε τ
| (Assign x body fenv,_)::rest =>
    ∃ Γ sc bodyTy, EnvWf fenv Γ ∧ HasType ((x,sc)::Γ) body bodyTy ε ∧ StackWf rest bodyTy ε τ
      ∧ (∀ lx lbody la, e = ⟨.Lambda lx lbody, la⟩ →                       -- IF control is a λ,
           ∀ args, HasTypeV (Closure lx lbody env) (sc.instantiate args))  -- carry its closure's Rdy
      ∧ ((∀ t, sc ≠ .mono t) → ∃ lx lbody la, e = ⟨.Lambda lx lbody, la⟩)  -- poly ⇒ control IS a λ
| k (other head)     => StackWf k σ ε τ
```

`MStateWf` value case → `∃ τin, HasTypeV v τin ∧ StackWfV v k τin ε τ`; E case → `… ∧ StackWfE e env k τin ε τ`.

## The edge cases the second `StackWfE` clause fixes (the non-obvious part)

A value-producing step `E w_term, env, k → V w_val, env, k` must turn `StackWfE` into `StackWfV w_val`.
For an **Assign head** that needs readiness `∀args, HasTypeV w_val (sc.instantiate args)`:
- **`w_term` a literal, `sc` mono** — `sc.instantiate _ = defnTy = τin`, `w_val : τin` ⇒ trivial. ✓
- **`w_term` a literal, `sc` poly** — `sc = genAt (arrow)`, so the frame input `τin = defnTy` is an *arrow*,
  but `HasType Γ literal (arrow)` is **false** ⇒ the pre-state is contradictory ⇒ vacuous. ✓ (types alone)
- **`w_term` a builtin Partial (arrow-typed), `sc` poly** — **NOT** ruled out by types (both arrows!), and
  the readiness `∀args, HasTypeV (Partial …) (genAt.instantiate args)` is **false** (a partial inhabits its
  *one* residual arrow, not a generalization). Semantically impossible (a poly assign's control is the bound
  **lambda**, never a partial), but needs the **second `StackWfE` clause** `poly-sc ⇒ control is a λ` to
  rule it out: a Partial control on a poly assign makes `StackWfE` **False**, so the state never arises. ✓
- **`w_term` the lambda, any `sc`** — the lambda→closure step: `StackWfE` (λ-clause) gives exactly
  `∀args, HasTypeV (Closure …) (sc.instantiate args)`, which IS `StackWfV (Closure …)`'s readiness. ✓

So the **first** `StackWfE` clause carries the closure's `Rdy` across the lambda-step; the **second**
(`poly ⇒ λ`) makes non-lambda controls on a poly assign impossible (closing the builtin-partial gap that
types alone miss). Both are needed; this is the design subtlety beyond the coupling note.

## Where `Rdy` is born (unchanged)

At the **Let-push** (the one coherent point, `env = fenv`, one `Γ`): `inv_let`'s poly branch gives
`hdefn`(λ), `CtxWf n Γ`, `noLet lbody`, `hbody`; `genAt_closure_ready` computes the closed
`Rdy : ∀args, HasTypeV (Closure lx lbody env) ((genAt n defnTy).instantiate args)`. The push builds the
poly Assign frame as a `StackWfE` whose λ-clause stores this `Rdy`; it rides the lambda-step into `StackWfV`.

## Remaining (the grind, both engines)

`StackWfV` + `StackWfE` defs (+ `toStackWf`, head inversions); `MStateWf` value/E cases; re-green
`preservation_E` (Let-push builds the `StackWfE` poly frame; every `.V`-producing arm yields `StackWfV` —
trivial/mono or vacuous-by-types, except the lambda-step which hands over `Rdy`), `preservation_V`
(Assign-pop reads `StackWfV`'s readiness → `EnvWf.cons`), `progress`; **mirror in the B engine**
(`StackWfVB`/`StackWfEB`). `StackWf.assign`-stores-`sc` is done (green, in the patch). No green intermediate.

## Implementation progress (later same day) — predicates + helpers + preservation_E GREEN

- **`StackWfV`/`StackWfE` defined** (Machine.lean, green) with the refined `assign` cases: both carry
  `defnTy` + `TyEquiv σ defnTy` (the input link, so mono readiness `HasTypeV v defnTy` is derivable from
  `v : σ`); `StackWfE` uses `sc = .mono defnTy ∨ control-is-λ`.
- **4 helper lemmas green**: `stackWfV_toStackWf`, `stackWfE_toStackWf`, `stackWfE_lambda_step`
  (λ→closure, hands the carried `Rdy` to `StackWfV`), `stackWfE_value_step` (non-λ control ⇒ mono ⇒
  trivial readiness via `v.conv`). The two step lemmas use `induction k` (structural recursion via
  pattern-`match` hit termination-checker friction; `induction` is robust).
- **`MStateWf` switched**; `mStateWf_E`/`_V` accessors updated; **`vstate_of_value`** helper packages a
  non-λ value-step (gets `m`/the value from the goal's expected type — a bare `have` can't infer them).
- **`preservation_E` FULLY re-greened** (63→43 errors): every literal/data/`Variable`/builtin arm via
  `vstate_of_value`; `Lambda` via `stackWfE_lambda_step`; `Apply` via `stackWfE_toStackWf`; the **`Let`
  crux** builds the `StackWfE` poly/mono Assign frame (mono closure clause via `closure_typed_of_lambda`,
  poly via `genAt_closure_ready (ctxWf_fixed hcw) hnl henv hdefn`). `import Eyg.Types.Generalization`
  added to Soundness.

## ⚠ Remaining subtlety (the 43 errors) — `StackWfV` production in the frame/effect cases

`preservation_V`'s frame cases (and `progress`, B-engine) produce a value `v` on a *reorganized* stack
(e.g. `Resume` → `move acc rest`), needing `StackWfV v k'`. A general `StackWf k' σ ε τ → HasTypeV v σ →
StackWfV v k'` is **false** for a *poly* assign head (readiness about a generic `v` fails). It is true
semantically — a poly assign's head value is only ever the bound λ's closure (produced at the λ-step), so
no other producer sits a value on a poly-assign head — but that needs a per-case argument or a stack-level
invariant. **Next:** either (a) a lemma `stackWf_toStackWfV` conditioned on "head assign is mono", with
each frame case discharging it (the reorganized stacks' heads are mono/non-assign — e.g. via the input
type: a poly assign's input is an arrow, contradicting most flowing values), or (b) strengthen the
stack-typing invariant so poly-assign heads carry their closure readiness intrinsically. Tree green at HEAD;
WIP patch (696 lines) has predicates + helpers + `preservation_E` green.
