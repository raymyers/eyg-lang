# G2 Phase 3 — the `ClosDisc`-field population gap (corrects Phase-2b "RESOLVED")

Date: 2026-07-11. Compiler-verified against a *migrated* `Runtime.olean` (`HasTypeV.closure`
carrying a `ClosDisc hbody` field). The migration itself was reverted to keep the cone green;
the additive `closDisc_ctxConv` library was committed (`33d507fa`).

## What I did (green, committed)

- `closDisc_ctxConv` / `closDisc_ctxHead_conv` added to `Eyg/Types/ClosDisc.lean` (commit
  `33d507fa`), axioms `[propext, Classical.choice, Quot.sound]`. The `ClosDisc` companion to
  `hasTypeRT_ctxConv`; recurses into lambda/defn bodies. Reusable, independent of the field surgery.
- Spiked the full Runtime migration (add `ClosDisc hbody` field to `HasTypeV.closure`; widen
  `EnvWf.cons` to `l = 0 ∨ s.level ≤ l`; swap `StackSegWf.assign`/`.arg` `HasTypeRT → ClosDisc`).
  Runtime.lean **greened** with those edits + `closDisc_ctxHead_conv`. Then reverted (see below).

## The gap (this is the correction)

`plan/progress/2026-07-10-G2-phase2b-polycapture-RESOLVED.md` claimed the poly-capture readiness
was "RESOLVED" by `closDisc_closure_ready_value_hybrid`. **That lemma was written against the
OLD, field-less `HasTypeV.closure`.** Building Runtime with the new `ClosDisc hbody` field and
recompiling the spike shows (compiler-confirmed, `G2DiscSpike.lean:125` and `:202`):

```
error: Application type mismatch: argument `heq` ... but is expected to have type `ClosDisc hbody'`
  in `HasTypeV.closure ... hbody' heq`
```

Both `closDisc_closure_ready_value` (mono) and `_hybrid` (poly) end with
`inv_lambda hlam` → `HasTypeV.closure ... hbody' heq`, where `hlam` is the closure the readiness
lemma *freshly constructs* via `hasType_fullRaise` (raise) then `genAtV_instantiate_lam_ready_floor`
(which calls `hasType_substAt_multi`, a substitution). The reconstructed body `hbody'` is therefore
a **raise-then-substituted** derivation. Populating the new field needs `ClosDisc hbody'` — i.e.
**`ClosDisc` must be shown preserved through the raise and the substitution.** The Phase-2b spike
never exercised this (no field existed), so "RESOLVED" was premature: the readiness *type* was
proven; the *field population* was not.

## Why it is provable (level arithmetic — TO BE COMPILER-VERIFIED, not trusted)

The concern: substituting a generalized level-`ℓ` var into a *nested* lambda's `retTy` could push a
level up to/over that nested lambda's own sublevel `λ`, breaking its `ClosDisc.lam` bound
`retTy.levels < λ`. The claim it does **not**, because of the readiness lemma's own raise:

- A nested lambda under the closure body (typed at `lvl'`) has sublevel `λ ≥ lvl' > ℓ` (entering a
  λ-body strictly raises the level; `ℓ ≤ lvl'` is the gen level). If `ℓ ∈` its `retTy`, then by its
  discipline `ℓ < λ`.
- `genAtV_ready_polyaware` raises the whole body by `o = argsRaiseOffset args` (dominates every arg
  level): the nested sublevel becomes `λ + o`; its non-`ℓ` levels stay `< λ + o`; `ℓ (< lvl')` is
  untouched by the raise.
- The subsequent `substAt ℓ` replaces `ℓ`-vars with args whose levels are `< lvl' + o ≤ λ + o`.
  Hence the substituted nested `retTy.levels < λ + o` — discipline **preserved** at the raised
  sublevel. The `argsRaiseOffset` domination is exactly what buys this.

**This is a level-relationship argument and must be discharged by the compiler, not by hand** (the
V8 error was an in-head level mistake). The next step verifies it.

## Scope of the real Session-A core (the ClosDisc-carrying re-derivation)

To populate the field, the readiness chain must carry `ClosDisc` end-to-end:

1. `closDisc_fullRaise` — `ClosDisc h → ClosDisc (hasType_fullRaise … h)`. The raise output is built
   constructor-by-constructor, so this mirrors that induction, re-checking each `lam`/`let_poly`
   `hret`/`hεb` bound survives the `+o` relabel (it does: both sides shift by `o`).
2. `closDisc_substAt_multi` — the big one: a `ClosDisc`-bundling companion of `hasType_substAt_multi`
   (~200-line induction over `HasType`). Returns `⟨h', ClosDisc h'⟩` at the substituted type,
   mirroring the existing arm-for-arm construction (same pattern as `hasTypeRT_ctxConv` bundling
   `(h', RT h')`). The `lam`/`let_poly` arms carry the surviving `hret`/`hεb` bounds; `var`/`builtin`
   arms re-establish `l = 0 ∨ s.level ≤ l` on the substituted args (args come from the instantiation,
   levels `≥ ℓ = s.level`, so the `≤` branch holds).
3. Re-thread `closDisc_closure_ready_value` / `_hybrid` / `closDisc_closure_ready_any` /
   `genAtV_ready_polyaware` to thread the ClosDisc through (1)+(2) and hand it to the new field.

Only after (1)–(3) are green (as an additive spike, validated with `lake env lean` against a
migrated `Runtime.olean`) is the entangled Runtime/Substitution/Machine breaking edit worth
landing — otherwise the producers in `Substitution.lean` cannot be re-greened.

## State of the tree

Green everywhere except the pre-existing WIP `Soundness.lean`. Runtime migration reverted;
`closDisc_ctxConv` committed additively. `HasTypeRT` and the old field-less producers are untouched.

## Next

Additive spike for (1)+(2) — `closDisc_fullRaise` and `closDisc_substAt_multi` — validated with
`lake env lean` against a locally-migrated `Runtime.olean`, to compiler-confirm the level argument
above. This is the go/no-go gate for the front-door discipline actually closing; it is the same
substitution-preservation shape as the (avoided) re-derivation keystone, now specialized to the
disciplined instantiation where `argsRaiseOffset` domination makes it go through.
