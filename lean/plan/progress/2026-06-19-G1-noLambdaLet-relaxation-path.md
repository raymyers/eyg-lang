---
date: 2026-06-19
milestone: G1 (Caveat 5) — let-polymorphism: `noLet` → `noLambdaLet` relaxation DELIVERED (partial gap close)
status: DELIVERED (the relaxation slice) — full nested *generalizable*-let remains the deferred redesign
---

# G1 — `noLet` → `noLambdaLet` relaxation DELIVERED + remaining hard case

## DELIVERED (2026-06-19)

The relaxation slice below **landed green**. `HasType.let_poly` now carries
`Tree.Node.noLambdaLet lbody` instead of `noLet lbody`: a generalized lambda's body may contain
**internal mono `let`s** (bindings whose definition is not a `Lambda`) — e.g.
`\x. (let y = x in y)`, `\x. (let n = int_add(x,1) in n)`. Only a nested *generalizable* `let`
(one binding a `Lambda`) is still excluded. `lake build` 1773 + `lake exe spec` 104/104; headline
`soundness` axioms unchanged (`propext`/`Classical.choice`/`Quot.sound`); no `sorry`.

What changed (the cascade, exactly as scoped):
- `Tree.Node.noLambdaLet` + inversion `Node.noLambdaLet_let` (`Ir/Tree.lean`).
- `HasType.let_poly` premise `noLet → noLambdaLet` (`Typing.lean`); `inv_let` field updated
  (`Generation.lean`).
- `hasType_subst` re-typed at `noLambdaLet`: the **mono `let_` arm is now discharged** (a plain
  congruence via `noLambdaLet_let` + `substCtx_cons`/`substScheme_mono`, same shape as `lam`); the
  `let_poly` arm stays **vacuous** (`noLambdaLet` of a `let`-binding-a-`Lambda` is `False`, so
  `generalizes_subst_false` is not re-triggered). `closure_typed_of_lambda_subst` + the keystones
  `generalizes_closure_ready`/`genAt_closure_ready` thread `noLambdaLet` (`Substitution.lean`,
  `Generalization.lean`).
- Sanity `example` in `Generalization.lean`: `let id' = \x. (let y = x in y) in id' 1 : Integer`
  (a term the old `noLet` rule rejected).

The engines (`Soundness.lean`) needed **no change** — they consume the body restriction only via
`inv_let`, which now hands them `noLambdaLet`.

## Remaining hard case (unchanged): nested *generalizable* let

A body containing `let g = \… in …` (a nested binding that itself generalizes) is still excluded.
That is the genuine crux below — it needs readiness *without re-substituting the body under the
instantiation*, the deferred scheme-typed-closures redesign. Caveat 5 is **narrowed**, not closed.

---

# Original analysis (the obstruction + why the relaxation is sound)

## Where G1 stands (reconfirmed from the code, not just prior notes)

The restricted `let_poly` is DELIVERED (`2026-06-19-T6-let_poly-DELIVERED.md`): the rule carries
`Tree.Node.noLet lbody` (generalized lambda body has **no internal `let` at all**). Full nested
let-generalization is the gap.

The obstruction is crisp and I re-verified it against the source:
`generalizes_closure_ready` (`Generalization.lean:330`) discharges polymorphic readiness via
`closure_typed_of_lambda_subst σ hfix hnl henv hlam`, which re-types the lambda **body** under the
instantiation substitution `σ` using `hasType_subst σ`. That lemma's `let_poly` arm is **false for
an arbitrary `σ`** (`generalizes_subst_false`), so it is only sound when the body never reaches the
`let_poly` arm. The keystone guarantees that today with `noLet` (no `let` nodes ⇒ vacuous arm). The
instantiation `σ` is **not** a `LevelMap` at the inner generalized level (it is a Γ-fixing
down-shift with arbitrary-FV `args`), so the `generalizesAt_subst`/`genAt_substScheme` machinery
does **not** rescue the high-`args` nested case (`2026-06-18-T6-let_poly-instantiation-levelmap-gap.md`).

**Counterexample branch is expected empty:** `let_poly` is value-restricted (only generalizes a
*lambda* binding), and value-restricted HM is sound, so nested let-poly should *prove*, not refute.
No CBV/effect surprise is expected here (unlike G2, which did refute). Full closure therefore needs
the deferred "readiness without re-substituting the body under instantiation" redesign
(scheme-typed closures / structural instantiation) — a multi-session effort, not a single slice.

## New, lower-risk slice: relax `noLet` → `noLambdaLet` (strict fragment expansion)

Reading the keystone surfaced a partial win the prior notes missed. The keystone only needs the
body's derivation to **never use the `let_poly` arm**. `HasType.let_poly` fires **only** when the
bound definition is a `⟨.Lambda …⟩` (value restriction). So a body whose every internal `let` binds
a **non-lambda** can only ever use the mono `HasType.let_` arm — never `let_poly`.

Hence replacing the premise `Tree.Node.noLet lbody` with a syntactic
**`noLambdaLet lbody`** ("no `let` node whose bound value is a `Lambda`") is **strictly more
permissive** and should keep the keystone sound:

- Covers all internal **non-function** `let`s inside a polymorphic function
  (`let x = f(y) in …`, `let n = int_add(a,b) in …`, `let r = {…} in …`) — currently rejected by
  `noLet`. This is a large, common fragment.
- Still excludes the genuinely hard case (a nested **generalizable** `let x = \…`).

### What the slice requires (the cascade, same shape as the original `noLet` work)

1. Define `Tree.Node.noLambdaLet` (term predicate, definable before `HasType`): like `noLet` but the
   `Let` case is `value-is-not-a-Lambda ∧ recurse value ∧ recurse body` instead of `False`.
2. Swap the `let_poly` constructor premise `noLet` → `noLambdaLet`; update `inv_let`,
   `hasType_ctxConv`, `hasType_expr_form`, `genAt_closure_ready`/`generalizes_closure_ready`.
3. **The one genuinely new proof obligation:** `hasType_subst`'s mono `let_` arm is no longer
   vacuous (a `noLambdaLet` body can contain mono `let`s), so it must be discharged for an
   **arbitrary `σ`**. Mono `let` does not generalize, so this is the standard substitution lemma —
   expected to be straightforward, but it is the load-bearing check. The `let_poly` arm stays
   **vacuous** (no lambda-let ⇒ never generalized), so `generalizes_subst_false` is not re-triggered.
4. Re-green both engines (the `StackWfV`/`StackWfE` coupling is unchanged — only the body predicate
   threaded through `genAt_closure_ready` changes). `lake build` + `lake exe spec` 104/104, axioms clean.
5. Sanity `example`: a polymorphic function with an internal **non-lambda** `let`
   (e.g. `let pair = \x. (let y = x in cons y (cons y tail)) in …`) typed at the expected type — a
   term the current `noLet` rule rejects.

Risk: moderate (a constructor-premise cascade across ~8 sites + one substitution arm). It does **not**
fully close Caveat 5 (nested *generalizable* let is still out), but it shrinks the gap to exactly the
hard case and is a clean tested slice. If the mono `let_` arm proves awkward for arbitrary `σ`, bail
to the deferred scheme-typed-closures redesign.
