---
date: 2026-06-16
milestone: T7 (BehaviorsR trace-level remainders)
status: DELIVERED (all BehaviorsR shapes covered modulo `fix`)
---

# T7 trace-level remainders — DELIVERED

This session closed the two documented `BehaviorsR` trace-level remainders plus the
observable purity certificates, all green, sorry-free, axioms
`propext`/`Classical.choice`/`Quot.sound`, `lake exe spec` 104/104. Three commits:

1. **`diverges` ω-effect-safety** (`soundness_behaviorsR_diverges`). A divergent
   `BehaviorsR` behaviour is an infinite `reduceLTS.ωTr ss μs`. Effect safety is an
   ordinary `ℕ`-induction (no coinduction), folding the new exact-`ε`
   `preservation_keep_fix` along the execution (`ωTr_all_wf`: every `ss i` stays
   well-typed at `(τ,ε)`), then reading `op ∈ ε` off `preservation_perform` at each
   emitted boundary (`ωTr_effect_safe` + `reduce_perform_inv`). Conditioned on the
   world supplying well-typed replies along the witnessing execution (`ReplyContract`
   per step).

2. **Reply-containing terminating traces** (`soundness_behaviorsR_terminates_value` /
   `_noBadCrash`). The silent-trace soundness goes through `evalR` (which halts at the
   first `perform`), so it only covered `tau`-only traces. An *open* terminating run may
   resume through `reply` steps. Folded directly over the finite `reduceLTS.MTr`
   (`mTr_terminal_wf`) + `terminalR_run`, conditioned on the **trace-level**
   `TraceRepliesOk` (every `Label.reply op v` carries a value inhabiting `op`'s declared
   reply type — the reply value lives in the label, so this is a pure trace predicate).

3. **Observable purity certificates** (`pure_no_suspend_behaviorsR`,
   `pure_no_perform_diverges`, helper `replyContract_empty`). A program typed at the
   empty effect row has no suspended behaviour and emits no `perform` in any divergent
   trace — the `BehaviorsR` analogues of `pure_no_perform_evalR`.

## Key reusable lemma

`preservation_keep_fix` — the **exact-`ε`** preservation variant (`MStateWf s τ ε →
Reduce s μ s' → ReplyContract ε s μ → MStateWf s' τ ε`), valid for the current
pre-`Handle` fragment where every `Reduce` move keeps the ambient row (`tau`/`perform`/
`reply` all return the same `ε`; the `∃ε'` wrapper of `preservation` hides this). Once
`Handle`/`Delimit` lands the row shrinks across a `Delimit` pop, so this exact-`ε` form
no longer holds — the ω/MTr folds would then thread the per-step row (the existential
`preservation`), an easy generalization.

## Remaining work (all milestone-scale, already scoped)

The independently green-able trace-level slices are now exhausted. Every remaining DoD
item is a large coupled/foundational slice with its own scoping note:

- **T5 `Handle`/`Delimit`** — the central novel slice; a *coupled* cascade
  (`StackWf.conv` constructor + per-frame inversion lemmas + `∃ε'` restatement +
  `delimit` frame + `Resume` segment typing + the dispatch lemma) with **no safe green
  intermediate** (confirmed again this session: the inversion lemmas cannot be stated
  with row slack before `conv` exists — unprovable — and without slack they don't
  insulate the four theorems from `conv`). See `2026-06-16-T5-handle-design.md`.
- **T6 `fix`** — blocked on **effect weakening / row subsumption** (Open Question #3),
  a `StackWf`-touching foundational change comparable to `Handle`. See
  `2026-06-16-T6b-fix-scoping.md` finding 3.
- **T6 `gen`** (let-polymorphism) — needs the de Bruijn type-substitution infrastructure
  (`Ty.shift` + `substScheme` + instantiate-commutes-with-subst + the mutual
  substitution lemma) and a type-variable convention decision. Additive (theorems, no
  `cases`-site breakage) but milestone-scale. See `2026-06-16-T6-gen-scoping.md`.

Each is a dedicated focused session; none can be reliably landed green incrementally
within a shared session alongside other work.
