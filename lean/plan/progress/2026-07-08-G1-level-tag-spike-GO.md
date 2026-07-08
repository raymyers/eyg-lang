---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 1–2 spike (level-tagged Ty)
status: GO — the level-tag resolves the nested let_poly wall in an isolated model
kind: research-spike
component: lean (new file, wired into nothing existing)
---

# G1 spike result: level-tagged `Ty.var` resolves the nested-generalization wall — GO

Per `plan/eyg-g1-level-tagged-ty.md` Phases 1–2 (hard go/no-go checkpoint before
committing to the full rewrite). Result: **GO**. `Eyg/Types/LevelTagSpike.lean`
builds green, `#print axioms`-clean (no custom axioms, no `sorry`), wired into
nothing existing (`import Eyg.Types.LevelTagSpike` added to `Eyg.lean` only to get
it built/checked by CI; it imports nothing from `Eyg.Types` itself). `lake build`
1774 jobs (was 1773), `lake exe spec` 104/104 unaffected.

## What was tested

A minimal level-tagged model: `Ty2.var (level idx : Nat)` instead of `Ty.var (idx :
Nat)`. Only `var`/`fn` are modeled — every other `Ty` former is uniform structural
recursion in the real system and plays no role in the mechanics being tested.

- `Ty2.substAt (ℓ : Nat) (σ : Nat → Ty2) : Ty2 → Ty2` — rewrites `var ℓ i` leaves via
  `σ i`; **no shifting anywhere** (contrast `Ty.shift`/`Ty.reindexGen`).
- `Scheme2 := ⟨level, body⟩`; `genAt ℓ d := ⟨ℓ, d⟩` — **the identity on `d`**, no
  `genArity`/`reindexGen` computation (contrast `Scheme.genAt`).
- `instantiate`/`substScheme` defined the obvious way on top of `substAt`.

## The result: `substScheme_genAt`

```
theorem substScheme_genAt (ℓ ℓ' : Nat) (σ : Nat → Ty2) (d : Ty2) :
    Scheme2.substScheme ℓ σ (Scheme2.genAt ℓ' d) = Scheme2.genAt ℓ' (Ty2.substAt ℓ σ d)
```

This is the direct analog of `Generalization.lean`'s `genAt_substScheme`. That
theorem needs a `Ty.LevelMap n σ` hypothesis (an "ambient substitute's free vars
stay below n" magnitude side-condition) — and the obstruction write-up
(`2026-06-19-G1-foundational-wall-confirmed-no-additive-slice.md`) shows the *outer*
let_poly's instantiation witness `σ_args` fails exactly that hypothesis when applied
to a *nested* scheme (it down-shifts `[n+arity,∞)`, which is where the inner
scheme's own fresh region has to live).

**`substScheme_genAt` needs no hypothesis on `ℓ`/`ℓ'` at all** — it holds by `simp
only [Scheme2.substScheme, Scheme2.genAt]`, i.e. essentially definitionally. There
is nothing to verify because `substAt`/`genAt` never inspect index *magnitude* —
only the level *tag* — so a substitution targeting one level structurally cannot
reach a differently-tagged scheme's quantifiers, whatever its numeric value. No
down-shift, no re-levelling, no `LevelMap`-style side condition to fail.

## The original counterexample, re-run

`Generalization.lean`'s `generalizes_subst_false`: the untagged scheme `⟨1, var 0⟩`
generalizing `var 0` away from a context whose only free var is `var 1` breaks under
`σ = [0 ↦ var 1]` — the substitution's target index (`0`) and the context's free
index (`1`) live in the same flat space and can collide.

The file re-runs the exact same shape (scheme `genAt ℓ' (var ℓ' 0)`, context free
var `var ℓctx 1`, substitution `σ = [0 ↦ var ℓctx 1]`) tagged, and it succeeds: the
context is provably untouched (`var ℓctx 1` is unreachable by a level-`ℓ'`
substitution when `ℓctx ≠ ℓ'`) and the instantiation lands exactly where asked. The
bug class `generalizes_subst_false` exhibits — quantified and ambient indices
numerically colliding — is structurally unrepresentable once they're tagged apart
instead of merely numbered apart.

## Decision

**Proceed to Phase 3** (the `level = 0` collapse lemma) per
`plan/eyg-g1-level-tagged-ty.md`. The bet the spike existed to test — does tagging
`var` with an explicit level, rather than relying on index magnitude, actually
dissolve the down-shift/re-level problem for a *second* nested generalization layer
— pays off, and pays off with *simpler* proofs than the untagged system (no
`LevelMap`, no `reindexGen`, no shifting lemmas at all in the core). The blast-radius
estimate in the plan (`Soundness.lean` ≈ 60% of touched lines) stands; nothing in
this spike changes that sizing, since it only tested the `Ty`/`Scheme` core in
isolation, not the downstream re-green cost.

## What is NOT yet shown (the honest caveats)

- This is a 2-constructor toy model (`var`/`fn`). Porting the level tag onto the
  real 12-constructor `Ty` is expected to be mechanical (every other former is
  untouched by the level-tag mechanics — they just carry `var`s recursively) but is
  unverified until done.
- Fresh-level *allocation* discipline (ensuring nested `let_poly`s never reuse a
  level number) was asserted, not formally threaded through a judgment here — this
  is the level-tagged analog of `CtxWf`/the old `n` freshness threading, expected to
  carry over in the same shape (a monotone counter), but not exercised in the spike.
- The real payoff (dropping `noLambdaLet` from `HasType.let_poly` and re-proving
  `hasType_subst`'s `let_poly` arm non-vacuously) has not been attempted — that is
  Phase 4 onward.
