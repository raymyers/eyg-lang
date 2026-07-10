# G2 B1 (type-fixed relabel vs V8) — BLOCKED by the let_poly gen/ambient coupling

Date: 2026-07-10. Machine-checked: `v8`, `v8_moving_g_moves_retTy`,
`v8_fixing_retTy_strands_g` (`G2Validation.lean`, axioms `[propext, Quot.sound]`).

## The structural fact (root cause)

`HasType.let_poly` (Typing.lean:137) generalizes at **exactly** its conclusion ambient `lvl`:
`… → HasType (lvl+1) ((x, genAtV lvl (…)) :: Γ) body … → HasType lvl Γ (Let …) …`. So an inner
`let`'s generalization level is **rigidly determined** by the ambient at which its node is typed — it
is not a free choice within a fixed derivation. To change a gen level you must change ambients, and
the only `HasType`-preserving way to move ambients is the **monotone** `raiseTy`/`hasType_fullRaise`
(a threshold `t`, offset `o`, moving every level `≥ t`).

## Why monotone raise cannot close V8 (machine-checked)

V8's stored derivation interleaves `g`'s gen level (2) *below* `retTy`'s inner-binder level (3). Any
threshold raise faces an impossible constraint:

- `v8_moving_g_moves_retTy`: to move `g` (level 2) needs `t ≤ 2`, but then `t ≤ 3`, so the raise also
  moves `retTy`'s binder level 3 — changing the closure's advertised type.
- `v8_fixing_retTy_strands_g`: any raise fixing level 3 has `t > 3 > 2`, leaving `g` at 2 — where the
  instantiation `[.var 2 0]` still captures.

**No single threshold separates "move `g`" from "fix `retTy`".** And a *non-monotone* relabel (move 2
past 3) is impossible because gen-level = ambient (above): the fresh-`g` derivation V8 exhibits is a
genuinely *different* derivation (different ambient threading), not a transform of the stored one.

## Verdict

**B1 is blocked.** The "type-fixed structural relabel" of a fixed stored derivation does not exist as
a `HasType`-preserving transform — this is the machine-grounded reason G16's type-fixed two-modes
raise walled. Readiness is still semantically true (V8 constructs it fresh), so this is *not* an
unsoundness; it is a hard limit on *transforming a stored derivation*.

## The two real routes to unconditional soundness (route B goal)

- **Rule change (recommended) — decouple gen-level from ambient in `HasType.let_poly`.** Let the rule
  generalize at a *chosen* fresh level `gl` (with the usual freshness `argTy/retTy levels < gl` and
  `lvl < gl`), body under `genAtV gl`. This is the standard Rémy formulation (gen levels chosen fresh
  by the inference, not equal to the ambient counter). It makes the fresh-`g` derivation reachable
  *by construction* (the derivation picks `gl` above the args), so the floor keystone
  (`genAtV_instantiate_lam_ready_floor`, already proven) discharges readiness with no raise. It is a
  **judgment change** — must be weighed: it widens which derivations exist, and every downstream
  lemma (generation, substitution, soundness) must be re-checked. But it is the clean, standard fix,
  and it directly delivers the user's *unconditional* goal.
- **B2 — closure re-architecture.** Store on `HasTypeV.closure` a `∀ args` re-derivable witness
  (principal-typing style) instead of one fixed body derivation. Larger, less standard.

## Recommendation

Pursue the **rule change** (call it B1′): it is the minimal, standard-Rémy adjustment that makes gen
levels a free fresh choice, which is exactly what V8 shows is needed and what the current
ambient-coupled rule forbids. Next concrete step: prototype the decoupled `let_poly` rule in a spike
`HasType`-variant and re-derive V8's program with `g` generalized fresh *from the stored derivation's
shape*, confirming the floor keystone then closes readiness — before committing to migrating the live
judgment. This needs a fresh sign-off (it is a soundness-statement-adjacent judgment change).
