---
date: 2026-06-18
milestone: T5 (Handle/Delimit) — discharging the last HandlerObligation (`perform`)
status: HANDOFF — `perform` is 2 compiler errors from green; full WIP captured as a patch
---

# T5 `perform` discharge — handoff (2 errors from green)

The final handler obligation, `HandlerObligations.perform` (the `doPerformR` stack-walk
dispatch), is **2 compiler errors away from fully discharged**. An execution pass got
steps 1–3 committed and the walk+discharge in progress before dying on a transient API
rate-limit. Everything is captured in a re-appliable patch on `main`.

## How to resume (do this first)

```sh
# from the repo root, on a fresh worktree/branch based on this HEAD:
git apply lean/plan/progress/2026-06-17-perform-wip.patch
cd lean && lake build Eyg.Types.Soundness   # → exactly 2 errors (see below)
```

The patch (`2026-06-17-perform-wip.patch`, ~427 lines, touches
`lean/Eyg/Types/{Machine,Runtime,Soundness,Generation,Substitution}.lean`) re-applies the
entire in-progress `perform` discharge. It is `git apply`-clean against this HEAD
(`9075ad91`). Then close the 2 errors and the obligation is done.

## What the patch contains (steps 1–3, solid; step 4, 2 errors)

Built on the now-settled "generalized `nil`" route (no mutual recursor — see
`2026-06-17-handle-perform.md`):

1. **`StackSegWf.nil` generalized** to carry endpoint `TyEquiv`s
   (`nil : TyEquiv σ σ' → TyEquiv ε ε' → StackSegWf [] σ ε σ' ε'`); old `nil` = the
   `refl/refl` instance. All `nil` use-sites fixed.
2. **`hasType_ctxConv`** — the standard context-head type-conversion lemma
   (`HasType ((x,.mono σ)::Γ) e τ ε → TyEquiv σ σ' → HasType ((x,.mono σ')::Γ) e τ ε`),
   by induction on the `HasType` derivation. Needed by the `assign` frame case.
3. **`stackSeg_conv_input` + `stackSeg_conv_output`** — segment endpoint conversion, by
   ordinary `induction seg + cases hseg` (the generalized `nil` makes the base case close
   by `trans`; this is what removed the need for the impractical `StackSegWf.conv`
   constructor). `stackSeg_append`/`stackSeg_toStackWf` re-greened.
4. **The walk + `perform` discharge** (in progress) — `induction hK` on `StackWf K σ ε τ`
   with the decoupled invariant (accumulated `StackSegWf` at concrete endpoints + `TyEquiv`
   to walk indices + `EffContains ε op …`); membership-based `StackSegWf.delimit` handles
   the row slack, `stackSeg_conv_input` the type slack at `callwith`/`assign`. Bottoms out
   at the matching `Delimit op`, builds the captured `StackSegWf acc'.reverse`, concludes
   the successor (handler at `handlerTy` applied to `arg : lift` then `resume : kontTy` via
   `partialResume`+`resume_preserves`).

## The 2 remaining errors

```
Eyg/Types/Soundness.lean:729  rewrite failed: did not find an occurrence of the pattern
Eyg/Types/Soundness.lean:787  application type mismatch (an argument)
```

Both are in step 4 (the walk/discharge), almost certainly a `TyEquiv`-orientation /
endpoint-shape mismatch where the wrong `conv` direction or a `.symm` is needed, or the
`stackSeg_conv_{input,output}` instance isn't applied at the right endpoint. They are
local tactic fixes, not design problems — the route has no unknowns. Once green: prove the
`perform` field, **remove `perform` from `HandlerObligations`** (it becomes the empty
structure — drop it and pass `⟨⟩`/simplify the `hho` params), have `preservation_V`'s
handled-`perform` case call the lemma directly, then `lake build` + `lake exe spec` 104/104
+ `#print axioms`.

## After `perform` lands — remaining for the complete-language soundness

- **`TauKeepsRow → RowEvolves`** (T7): the parallel follow-up — rework
  `soundnessR_effect`/`ωTr_all_wf`/`mTr_terminal_wf` to thread a row-only-shrinks relation
  (downward `EffContains` reflection across `Delimit` discharges) instead of the
  `TauKeepsRow` gate, making the effect-escape/divergence results unconditional. The
  membership-based `delimit` + the conv infra from this patch are the enabling pieces.
- **effectful-`fix`** (`Fix*` for `q1 ≠ ∅`) — general row subsumption (Open Q3).
- **`gen`/let-poly** — the `MStateWf` context-freshness invariant.

The `ε`-free value + no-bad-crash soundness is already **unconditional for the full
language including `Handle`** (modulo `Fix*`); these follow-ups only concern the
row-dependent effect/divergence claims and polymorphism.

## Provenance
WIP commits live on branch `handle-perform6b` (`ed13d9fe`, in the now-defunct worktree);
the patch on `main` is the durable copy. `main` (`9075ad91`) is green and untouched by
this WIP.
