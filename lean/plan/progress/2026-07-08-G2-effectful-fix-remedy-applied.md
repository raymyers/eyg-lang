---
date: 2026-07-08
kind: soundness-remedy
component: gleam_analysis (type checker)
status: DONE — reference scheme corrected, verified by running the analyzer
---

# G2 / Caveat 4 remedy: pin `fix`'s builder latent to `Empty` in `contextual.gleam`

Follow-up to `2026-06-19-G2-effectful-fix-unsoundness.md`. That note found a
machine-checked counterexample: the reference `fix` scheme left the builder's
construction effect row `q1` free, which is unsound under call-by-value (the runtime
re-runs the builder on every recursive self-application, re-firing its construction
effects outside any handler installed at `fix`-creation). Of the three remedies listed
there, **Option 1 (pin `q1 = ∅` in the reference analyzer)** was applied — the low-risk
move that brings `gleam_analysis` in line with what the Lean model already proves
sound (`HasTypeV.partialFixed`'s pure-builder pin), without touching the interpreter's
operational semantics.

## Change

`packages/gleam_analysis/src/eyg/analysis/inference/levels_j/contextual.gleam:534`:

```gleam
// before (unsound: q1 free)
#("fix", {
  let self = t.Fun(q(0), q(2), q(3))
  t.Fun(t.Fun(self, q(1), self), q(1), self)
}),

// after (sound: builder latent pinned to Empty)
#("fix", {
  let self = t.Fun(q(0), q(2), q(3))
  t.Fun(t.Fun(self, t.Empty, self), t.Empty, self)
}),
```

## Verification

Ran the full `gleam_analysis` suite (`nix shell nixpkgs#gleam nixpkgs#nodejs_22 --command
gleam test`) plus two new tests added to
`test/eyg/analysis/inference/levels_j/contextual_test.gleam`:

- `fix_effectful_builder_rejected_test` — the exact G2 witness program (`handle Log`
  around a `fix` whose builder does `perform Log("building")`) now produces an error
  somewhere in the resolved node list (`MissingRow("Log")`) instead of type-checking
  clean; previously it resolved as pure `Integer`.
- `fix_pure_builder_still_sound_test` — `!fix((self) -> { (n) -> { !int_add(n, 1) } })`
  still infers `(Integer) -> Integer`, pure — real (pure-builder) recursion is
  unaffected.

**Result: 39 passed, no failures** (37 pre-existing + 2 new). No other package under
`packages/` references `fix` directly (`grep -rl "!fix\|builtin(\"fix\")"` outside
`gleam_analysis` is empty), so the change is contained to the type checker.

The Lean side is unchanged (it already had the corresponding pin) — `lake build`
(1773 jobs) and `lake exe spec` (104/104) stay green, axioms unchanged.

## Consequence

- **Caveat 4 in `plan/report/type-soundness-report.md` should be updated**: the
  pure-builder restriction is no longer *only* a Lean-side pin justified by an
  unsoundness in the reference — the reference has now been corrected to match,
  the same way base-type `fix` was corrected for Caveat 3. The Lean model and the
  reference analyzer are back in agreement on `fix`'s scheme.
- `Eyg/Types/CexEffectfulFix.lean` remains valid as a regression witness (it exercises
  the Lean-side `eval`/`evalR`, which were never unsound); it now also documents what
  the *uncorrected* reference used to accept.
