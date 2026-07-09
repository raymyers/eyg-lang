---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G12". Lands three of G11's four remaining infrastructure
  pieces for the generalization-level raise (LevelsBelow + existence; raiseCtx/raiseScheme; the var-arm
  crux equality), and sharpens the remaining `hasType_raise`/`hasType_relabel_raise` mutual induction
  with a new structural insight: the relabel theorem is *re-entrant on the same-level collision*, so the
  mutual recursion must terminate on the derivation, not any level ordering.
status: PARTIAL. Three green additive commits to Typing.lean (`5413665c`, `fe30f615`, `a9a80052`).
  Soundness.lean left exactly as found (pre-existing uncommitted 53-line partial migration, untouched).
  Caveat 5 OPEN. The two mutually-recursive 21-arm raise inductions NOT proved (the last remaining
  piece). Full green NOT reached. No LSP/MCP (canary failed: Read/Grep/Edit + `lake env lean` only).
kind: progress
component: lean (Eyg/Types/Typing.lean)
---

# G1 Phase 6 (Session G12): LevelsBelow + raiseCtx + var-arm crux landed; relabel re-entrancy found

No LSP/MCP this session (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep/Edit
+ `lake env lean Eyg/Types/Typing.lean` (~3s clean per-file) only.

## Headline

G11 pinned the raise as a two-theorem re-elaboration and enumerated four remaining pieces:
(1) `LevelsBelow`+`∃N`; (2) `raiseCtx`+lemmas; (3) `hasType_raise` (type-fixed); (4)
`hasType_relabel_raise` (fresh-level). This session lands **(1) and (2) in full, plus the concrete
var-arm crux of (3)/(4)** as three green additive commits, and sharpens the shape of (3)/(4) with a
structural correction that matters for whoever writes the `mutual` block.

## Landed green (all in `Typing.lean`, per-file `lake env lean` EXIT 0, axioms unchanged, no `sorry`)

- **`5413665c` — `LevelsBelow N h` + `LevelsBelow.mono` + `exists_levelsBelow`.** A `NoGenAt`-shaped
  inductive (indexed by the `HasType` derivation, 21 arms). Only the `let_poly` arm carries a bound
  (`∀ l ∈ defnTy.levels, l < N`); every arm recurses. `exists_levelsBelow` supplies some `N` for any
  derivation (per-node `max` of sub-`N`s and `defnTy.levels.foldr max 0 + 1`). This is G11's threaded
  global freshness cap: a single offset `o ≥ N` relabels every node's gen level to a genuinely fresh
  `k + o ∉ defnTy.levels`.
- **`fe30f615` — `raiseScheme t o` + `raiseCtx t o` + `raiseCtx_lookup`/`_fix` + `raiseScheme_mono`/
  `_of_level_lt`.** `raiseScheme t o (genAtV k d)` for `k ≥ t` = `genAtV (k+o) (substAt k (·↦var(k+o)) d)`
  — the *exact* input shape of `instantiateV_genAtV_relabel` — and is the identity on any scheme whose
  gen level is `< t` (all `mono` bindings; any outer poly binding generalized below the threshold).
  `raiseCtx_fix` proves the raise fixes a context all of whose bindings generalize below `t`.
- **`a9a80052` — `raiseScheme_genAtV_instantiateV`.** The crux the `hasType_raise` var arm consumes,
  now a *concrete proven lemma* (G11 had it only as prose): for `k ≥ t` and `d.levels < N ≤ o` there is
  an explicit padded arg list `args' = args ++ (List.range extra).map (fun j => var k (args.length+j))`
  (with `extra = (freeVarsAt k d).foldr max 0 + 1`, guaranteeing coverage) under which
  `(raiseScheme t o (genAtV k d)).instantiateV args' = (genAtV k d).instantiateV args`. Composes
  `instantiateV_pad_default` (extend `args` to meet coverage without changing the produced type) with
  `instantiateV_genAtV_relabel` (fresh relabel is instantiation-invariant); freshness `k+o ∉ d.levels`
  falls out of `N ≤ o` (`l ∈ d.levels ⇒ l < N ≤ o ≤ k+o`). This nails the escaped-var/inner-gen
  decoupling concretely: the escaped var (in `args`) stays at level `k`; the scheme body's gen vars move
  to `k+o` via the relabel.

## The remaining piece is the two mutually-recursive raise inductions — and a new structural insight

The only piece left of G11's four is (3)+(4). The precise statements (validated against the arm
structure of `hasType_substAt_le`) the next session should implement:

- `hasType_raise` (type-fixed): `HasType j Γ e τ ε → LevelsBelow N h → N ≤ o → 0 < o → t ≤ j →
  (∀ b ∈ Γ, ∀ l ∈ b.2.body.levels, l < N) → HasType (j+o) (raiseCtx t o Γ) e τ ε`. The context invariant
  is **`CtxLevelsBelow N Γ` (bind-BODY levels < N), NOT `CtxWfV`** — freshness of the relabel target
  `k+o` needs a bound on the looked-up binding's *body* levels, and this threads cleanly (the `let_poly`
  arm's new binding body = `defnTy`, bounded by `LevelsBelow.let_poly`). `t ≤ j` (ambient ≥ threshold)
  is maintained on descent (`lam`/`let_` keep body ≥ j; `let_poly` bumps to j+1). The var arm uses
  `raiseScheme_genAtV_instantiateV` (this session) for a raised (`level ≥ t`) binding, and `args' = args`
  for a fixed (`level < t`) one. The `let_poly` arm delegates the defn to `hasType_relabel_raise` and
  recurses (raise) on the body; the reconstructed stored scheme `genAtV (k+o) (substAt k (·↦var(k+o))
  defnTy)` is *exactly* `raiseScheme t o (genAtV k defnTy)`, so `raiseCtx_cons` lines up the body
  context. Conclusion type `τ`/`ε` **literally fixed** throughout (only ambient index + inner gen levels
  + context move).
- `hasType_relabel_raise` (fresh-level): the same, but at a `let_poly`-defn it re-types the defn's
  *type* under `substAt k (·↦var(k+o))` (relabel level = that node's gen level `k`), because `genAtV`
  ties stored-level = ambient = gen-level; `hasType_subst`/`_substAt_le` provably cannot do this
  (range level `k+o ∉ {0,k}`, G11 refutation). Conclusion `HasType (j+o) (raiseCtx t o Γ) e
  (substAt k (·↦var(k+o)) τ) (substAt k (·↦var(k+o)) ε)`.

**New structural insight (sharpens G7 Finding 3 / G11 (3)): `hasType_relabel_raise` is re-entrant on the
same-level collision.** When `hasType_raise`'s `let_poly` arm calls `hasType_relabel_raise` on the defn
(a lambda at ambient `k`, relabel level `k`), one might hope this is a clean "distinct-level"
(`k <` every inner ambient) induction like `hasType_subst`. It is **not**: if the defn's arg type is
ground, its `lam` body sits at sublevel *exactly* `k`, and may itself contain an inner `let_poly`
generalizing at exactly `k`. There the relabel-at-`k` map `(·↦var(k+o))` collides with that inner
`genAtV k` node — the *same* same-level non-commutation (G7) the whole raise exists to resolve, now one
generalization layer down. So `hasType_relabel_raise`'s `let_poly` arm, when the inner gen level equals
the relabel level, must itself relabel that inner scheme (behaving like the raise) — the two theorems are
not merely mutually recursive but **recursively re-entrant on the collision**. Consequence for
implementation: the `mutual` block's termination must be **structural on the `HasType` derivation** (a
`termination_by`/`decreasing_by` on the derivation size), **not** any level-ordering measure (no level
strictly decreases across the re-entrant call). This is why a single "relabel everything ≥ t in both
type and derivation" theorem cannot subsume both: the conclusion may carry an escaped tag at exactly the
threshold level that must STAY (absorbed via the var arm's arg, not relabeled) while a sibling `let_poly`
at the same level MOVES — the two fates of one tag are decoupled only by the derivation-structural var
arm (`raiseScheme_genAtV_instantiateV`), never by a uniform type-level relabel.

## Wire-in shape (unchanged from G11, restated for the next session)

`genAtV_closure_ready_value_node` (`Substitution.lean:167`) drops its `NoGenAt lvl h` premise: from
`inv_lambda h` take `hbody : HasType lvl' ((x,.mono argTy)::Γ) lbody retTy εb` with `lvl ≤ lvl'`. If
`lvl < lvl'` fire the STRICT keystone `genAtV_instantiate_lam_ready` directly (no raise). If `lvl' = lvl`
(the only residual — e.g. `perform`/escaping `id`), `hasType_raise` the body from ambient `lvl` to
`lvl+o` (`o ≥ N` from `exists_levelsBelow hbody`, threshold `t = lvl`), keeping `retTy`/`εb`/context
fixed, then fire the strict keystone at `lvl < lvl+o`. NB the wrapper will additionally need the context
invariant `∀ b ∈ Γ, b.2.level < lvl` (so `raiseCtx lvl o Γ = Γ`, via `raiseCtx_fix`) — true for runtime
`EnvWf` contexts (poly bindings generalized at outer, lower levels) but not implied by `CtxWfV`; thread
it as an `MStateWf`/wrapper hypothesis. Then the ~90-error two-engine `Soundness.lean` grind + Phase 7.

## Tree state at stop

- HEAD `a9a80052` (three commits above `346a8208`). Per-file green: Typing.lean (incl. the three new
  blocks). All additions purely additive (new decls only; no existing declaration touched).
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6 partial migration, 53 lines,
  **untouched** this session), uncommitted. Untracked `.claude/`, this note + plan update.
- `grep sorry Eyg/Types/*.lean`: none. Whole-project `lake build` still fails only on `Soundness.lean`.
  Caveat 5 OPEN.
