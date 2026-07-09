---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G13". Attempts the two mutually-recursive raise inductions
  from G12's blueprint; finds a genuine architectural subtlety that supersedes the single-relabel-level
  formulation (the two modes require *distinct*, mutually-incompatible context-raise operations on a
  *shared* context); lands the uniform-relabel primitive `Ty.raiseTy` + the exact bridge lemma
  characterizing when single-level suffices.
status: PARTIAL. One green additive commit to Scheme.lean (`ddaf2e35`). Soundness.lean left exactly as
  found (pre-existing uncommitted 53-line partial migration, untouched). Caveat 5 OPEN. The two
  mutually-recursive raise inductions NOT built — a real obstruction in G12's single-level-`k` blueprint
  found and characterized. Full green NOT reached. No LSP/MCP (canary failed: Read/Grep/Edit +
  `lake env lean` only).
kind: progress
component: lean (Eyg/Types/Scheme.lean)
---

# G1 Phase 6 (Session G13): raiseTy landed; the two raise modes need *distinct* context-raise ops

No LSP/MCP this session (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep/Edit
+ `lake env lean` (~4s clean per-file) only. This session set out to build G12's two mutually-recursive
21-arm raise inductions (`hasType_raise` type-fixed / `hasType_relabel_raise` fresh-level) as a
derivation-structural `mutual` block. Working through the arm recipes concretely surfaced a genuine
subtlety that the G12 blueprint's single-relabel-level formulation does not resolve — exactly the class
of "the blueprint has its own subtlety once you try to build it" this saga keeps hitting. Rather than
force a large mutual induction that cannot be verified arm-by-arm under batch `lake env lean`, this
session pins the obstruction precisely and banks the primitive its resolution needs.

## Landed green (`ddaf2e35`, Scheme.lean, per-file EXIT 0, axioms unchanged, no `sorry`, additive)

- **`Ty.raiseTy t o`** — the *uniform* generalization-level raise on a type: relabel **every** `var l i`
  with `t ≤ l` to `var (l+o) i`, fixing all levels `< t`. (G12's `raiseScheme`/`raiseCtx` relabel a
  scheme body only at its *own* gen level via single-level `substAt k`; `raiseTy` is the multi-level
  counterpart.)
- **`raiseTy_eq_self_of_levels_lt`** — `raiseTy` fixes a type all of whose levels are `< t`.
- **`raiseTy_eq_substAt_of_single`** — the crux bridge: `raiseTy t o d = substAt k (·↦var(k+o)) d`
  **iff-shaped** (proved as the `⇐` a caller uses) exactly when `∀ l ∈ d.levels, t ≤ l → l = k`
  (`t ≤ k`), i.e. the type's *only* `≥ t` level is the designated `k`. This pinpoints the invariant a
  single-relabel-level companion theorem tacitly assumes on every stored scheme body it descends past.

## The obstruction (supersedes G12's single-level-`k` `hasType_relabel_raise`)

G12 stated `hasType_relabel_raise` with a **single** relabel level `k` (conclusion type
`substAt k (·↦var(k+o)) τ`), sharing the mode-independent `raiseCtx t o` with `hasType_raise`. Tracing
the `let_poly` and `var` arms concretely (both engines below reach the same wall):

**(1) `raiseCtx` is mode-independent and single-level-per-binding.** `raiseScheme t o (genAtV k' d) =
genAtV (k'+o) (substAt k' (·↦var(k'+o)) d)` relabels the binding body **only at that binding's own gen
level `k'`** — never at the ambient relabel level `k`. Both modes must use this same `raiseCtx` (the
`let_poly` arm reconstructs the body under `raiseCtx t o ((x, genAtV j defnTy)::Γ)` and the defn under
`raiseCtx t o Γ` — one shared operation).

**(2) A relabel-`k` descent past an inner binding at `k' ≠ k` needs a DOUBLE relabel of that binding's
body, but `raiseCtx` supplies only the `k'` half.** When `hasType_relabel_raise` (relabel level `k`)
descends — through the shared `raiseCtx` — into/past an inner `let_poly` (or looks up an inner context
binding) generalized at `k' ≠ k`, both `≥ t`: the inner binding's stored body `d` may carry **foreign
level-`k` content** (occurrences of the outer relabel-`k` generalization instantiated into the inner
defn — e.g. an inner `\w. a w` using the outer poly `a` at level `k`). The relabel-`k` conclusion
demands that level-`k` content move to `k+o`; but `raiseCtx` relabeled that binding only at `k'`,
leaving its level-`k` content **un-moved**. A var-use that looks the binding up therefore produces a
type with un-relabeled level-`k` content, contradicting `substAt k (·↦var(k+o)) τ`. The binding body
genuinely needs `substAt k' (·↦var(k'+o)) (substAt k (·↦var(k+o)) d)` — a *double* relabel — which the
single-level `raiseScheme` never produces. `raiseTy_eq_substAt_of_single` is exactly the (failing)
hypothesis that would collapse the double back to single.

**(3) This affects the *type-fixed* main raise too, via its `let_poly` arm.** `hasType_raise`'s
`let_poly` arm must re-type the defn to `substAt j (·↦var(j+o)) defnTy` (the body of
`raiseScheme t o (genAtV j defnTy)`, `j` = that node's gen level = ambient) — i.e. it *calls* the
relabel companion at level `j`. So the double-relabel wall is inherited by the main raise. (Confirmed
this session: the main raise's own atomic/`var`/`perform` arms keep the type literally fixed via the
G12 arg-padding `raiseScheme_genAtV_instantiateV` — that half is fine; the entanglement is only through
the `let_poly` arm's delegation to the relabel companion.)

**(4) There is no pure *type-function* formulation — the transformation is inherently
derivation-directed.** At one level value `ℓ ≥ t` a tag can be either a *bound generalization var* (must
MOVE to `ℓ+o`, to track its raised scheme) or a *genuinely-escaped tag realized via an instantiation
arg* (must STAY at `ℓ`, reproduced by arg-padding). These are indistinguishable by tag. In the
*conclusion type* of the type-fixed raise every `≥ t` tag is escaped-and-free → all STAY (type fixed);
in the *relabel* companion's conclusion every `≥ t` tag is a generalization occurrence → all MOVE
(conclusion `= raiseTy t o τ`, **not** single-level `substAt k`). So the two modes genuinely differ in
fate-of-`≥ t`-tags and consequently need **different context-raise operations**: raise = single-level
per binding (current `raiseScheme`, escaped tags stay via padding); relabel = **`raiseTy` per binding**
(all `≥ t` move). They only coincide on bindings all of whose levels are `< t`.

**(5) Why the wrapper is *not* immediately broken.** At the wrapper's top level `t = lvl` and
`CtxWfV lvl Γ` forces every context binding's body levels `< lvl = t` (including its own gen level, which
occurs in the body), so **both** context-raise ops equal the identity there (`raiseCtx_fix` /
`raiseTy_eq_self_of_levels_lt`) — no conflict. The conflict can only surface at nesting depth `≥ 2`
inside the raised body, where the accumulated context carries a binding at level `≥ t` whose defn has
foreign cross-level `≥ t` content. Whether the *specific* residual closure bodies the wrapper feeds
(`lvl' = lvl`, `lvl ∈ retTy.levels ∪ εb.levels`) ever reach that configuration is the open question that
decides whether single-level suffices in practice or the `raiseTy` migration is mandatory.

## Recommended next step (with LSP)

Adopt the **`raiseTy`-uniform relabel** for the relabel companion (option (a)): redefine the relabel
mode's context raise so each binding body uses `raiseTy t o` (multi-level), conclusion type `raiseTy t o
τ`; keep the type-fixed main raise's *var/atomic* arms on the current single-level arg-padding
(`raiseScheme_genAtV_instantiateV`), and have its `let_poly` arm delegate the defn to the `raiseTy`-based
relabel companion. The var-arm lemma the relabel mode then needs is a clean uniform commutation
`raiseTy t o ((genAtV k d).instantiateV args) = (genAtV (k+o) (raiseTy t o d)).instantiateV
(args.map (raiseTy t o))` for `k ≥ t` (note the getD defaults match automatically:
`raiseTy t o (var k i) = var (k+o) i` = the raised scheme's default — **no arg-padding/coverage needed**,
unlike the single-level `raiseScheme_genAtV_instantiateV`). Then reconcile the shared context (5): either
prove the wrapper's residual bodies never nest a foreign-cross-level `let_poly` (so single-level = uniform
throughout, via `raiseTy_eq_substAt_of_single`), or make BOTH modes use the `raiseTy` context raise and
recover the type-fixed raise's "escaped tags stay" as a *derived* fact (the escaped tags in the wrapper's
`retTy`/`εb` are `< t`?? — verify: the residual case has `lvl ∈ retTy.levels`, i.e. level exactly `t`,
which `raiseTy t o` WOULD move — so the type-fixed raise cannot be a `raiseTy` special case; the two
modes are irreducibly distinct). This is the sharp fork the next session resolves; wants live goal-state.

## Tree state at stop

- HEAD `ddaf2e35` (one commit above `e560a2a6`). Per-file green: Scheme.lean (incl. the three new
  decls). Purely additive (new decls only; no existing declaration touched).
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6 partial migration, 53 lines,
  **untouched** this session), uncommitted. Untracked `.claude/`, this note + plan update.
- `grep -rn sorry Eyg/Types/*.lean`: none. Whole-project `lake build` still fails only on
  `Soundness.lean`. Caveat 5 OPEN.
