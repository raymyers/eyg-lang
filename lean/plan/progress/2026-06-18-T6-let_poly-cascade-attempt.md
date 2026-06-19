---
date: 2026-06-18
milestone: T6 — `let_poly` cascade ATTEMPT: typing layer green; hasType_subst gate + engine coupling remain
status: WIP (typing layer builds; reverted to keep tree green; WIP saved as a patch)
---

# `let_poly` cascade — typing layer done; `hasType_subst` gate + `StackWfV` engines remain

Executed the cascade from `2026-06-18-T6-let_poly-hasType_subst-arm-design-resolved.md`. The **typing
layer landed and builds**; the cascade then hit the two genuinely-heavy remaining pieces. Reverted the
`.lean` edits (no green tree exists until the *whole* slice lands) and saved the working diff as
`2026-06-18-T6-let_poly-cascade-WIP.patch` (224 lines, applies cleanly on `19b482e8`).

## What works (in the WIP patch, builds green per-file through Generation)

- **Def relocation** (the import-ordering resolution): `Ty.genArity`/`Ty.reindexGen`, `Scheme.genAt`/
  `Scheme.genAt_arity`/`Scheme.freeVars`/`Scheme.freeVars_mono` moved into `Scheme.lean`; `CtxWf` into
  `Typing.lean` (after `Ctx`). Generalization.lean keeps all the *lemmas* (they resolve the moved defs by
  name). Builds clean.
- **`HasType.let_poly` constructor** (`Typing.lean`): value-restricted (`defn = ⟨.Lambda lx lbody, la⟩`),
  scheme `Scheme.genAt n defnTy`, premises `hdefn`(lambda) + `CtxWf n Γ` + `hbody`(at the genAt binding).
- **`hasType_ctxConv` `let_poly` arm** + helper **`ctxWf_ctxConv`** (`CtxWf` survives a `TyEquiv`
  binding rewrite, via `Scheme.freeVars_mono` + `Ty.freeVars_tyEquiv`). Builds.
- **`inv_let` unified to a mono/poly disjunction** (`Generation.lean`) — the poly arm exposes
  `lx lbody la defnTy n`, `defn = Lambda`, `hdefn`, `CtxWf n Γ`, `hbody`(at `genAt n defnTy`). (Could not
  use a `Generalizes`-unified form: `Generalizes` lives in `Generalization.lean`, which *imports*
  `Generation` — the disjunction sidesteps the cycle.) **`hasType_expr_form` `let_poly` arm** added.
  Generation builds.

## Blocker 1 — `hasType_subst` `let_poly` arm needs a `WfLevel n` DERIVATION predicate (the gate)

The arm reconstructs `HasType.let_poly` via `genAt_substScheme` + `ctxWf_substCtx`, both requiring
`LevelMap n_node σ` for the node's stored level `n_node`. From the substitution premise `LevelMap n σ`,
`LevelMap.mono` supplies it **iff `n ≤ n_node`**. That gate `n ≤ n_node` holds for every let node
`hasType_subst` *traverses* — crucially, the keystone substitutes the let's **lambda body** (`hdefn`), NOT
the outer let node, so every traversed `let_poly` is *nested deeper* (level `≥ n = n_lp + arity`), giving
`n ≤ n_node`. But `n_node` lives in the **derivation**, not the term (`.Let x defn body` carries no
level), so the gate must be a predicate over the derivation:

```
inductive WfLevel (n : Nat) : ∀ {Γ e τ ε}, HasType Γ e τ ε → Prop   -- one arm per HasType ctor;
  | ... let_poly: n ≤ n_node ∧ WfLevel n hdefn ∧ WfLevel n hbody ; others: ∧ of sub-derivs / True
```

`hasType_subst` re-states with `(hσ : LevelMap n σ) (hwf : WfLevel n h)`, threads `hwf` through every arm
(destructure, pass to IHs), and the `let_poly` arm reads `n ≤ n_node` from it. The keystone
`genAt_closure_ready`/`closure_typed_of_lambda_subst` gain a `WfLevel (n_lp+arity)` premise for the
lambda — supplied at the push from a **light, unchanging program-level let-leveling invariant** (lets are
typed at levels = in-scope type-var count, so nested ≥ enclosing+arity; constant across reduction since
the AST is static). This `WfLevel` inductive (~20 trivial arms) + the `hasType_subst` re-threading is the
genuine remaining gen-branch sub-development. **All the algebra it sits on is already green**
(`genAt_substScheme`, `ctxWf_substCtx`, `LevelMap.mono`, `CtxWf.mono`).

## Blocker 2 — the value-aware `StackWfV` two-engine coupling (unchanged, still the bulk)

Per `2026-06-18-T6-let_poly-coupling-design-sharpened.md`: generalize `StackWf.assign` to store a scheme;
add `StackWfV` (value-aware at the `assign` head, recurse through `trace`, drop to `StackWf` elsewhere) +
`stackWfV_toStackWf`/inversions/`conv`; `MStateWf` value case → `StackWfV`; re-green `preservation_E`/`_V`/
`progress`; **mirror in the B engine** (`StackWfVB`). The push computes the closed readiness `Rdy` via
`genAt_closure_ready` and carries it across the lambda→closure step; the Assign-pop feeds `EnvWf.cons`.
This ripples through *every* `.V`-state construction in both engines (mechanical for non-`assign` heads,
the real work at the lambda-step) and is gated on Blocker 1 (the keystone must compile first).

## Soundness-side touch points already located (from the build)

`weakenEff` (`Soundness.lean:52`) needs a `let_poly` arm; the two `inv_let` consumers
(`Soundness.lean:204`, `:2728`, the E- and B-engine Let-push) must split on the new mono/poly disjunction.

## Conclusion

The typing-layer cascade is done and correct (in the WIP patch). The remaining two blockers — the
`WfLevel` derivation predicate threading `hasType_subst`, and the `StackWfV` two-engine coupling — are
each a focused sub-session; together they are the all-or-nothing remainder (no green intermediate, since
the `let_poly` constructor breaks `hasType_subst`/`weakenEff`/both engines at once). Next session: land
`WfLevel` + the `hasType_subst` arm (unblocks the keystone), then the `StackWfV` engine cascade. Tree
reverted to green at `19b482e8` (the committed infra: `LevelMap.mono`, `CtxWf` metatheory, design).
