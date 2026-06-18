---
date: 2026-06-17
milestone: T5 (Handle) — discharge `resume` (DONE) + `perform` (scoped)
status: `resume` DISCHARGED (green); `HandlerObligations` shrunk to `{perform}`
---

# `resume` discharged via quantified `partialResume` + generalized `StackSegWf.delimit`

The prior pass pinned the `resume` wall (the `EffWeaken` `εf ≈ ∅` disjunct — an escaping
pure-tail continuation invoked at a larger ambient). This pass **cracks it**.
`HandlerObligations` is now `{perform}` (was `{perform, install, resume}`); `lake build`
1771 jobs, `lake exe spec` 104/104, axioms `propext`/`Classical.choice`/`Quot.sound`, no
new `axiom`s, no `sorry`.

## The fix (clean, not a wedge)

The wall was "re-type the captured segment **upward** at the larger ambient". My analysis
first showed the naive *weakened composition* `StackSegWf … → StackWf k σmid ε τ →
EffWeaken εmid ε → StackWf (seg++k) …` is **false as a general lemma** — a row-constant
non-`delimit` segment (e.g. a lone `trace`/`callwith`) cannot absorb the weaken; it would
need its frames re-typed up, which the `nil` base case can't do. The resume case only
works because, for a **deep** handler, the captured `acc.reverse` **ends in the re-pushed
`Delimit`**, and *that* frame is the row-bridge.

So the right move is to push the freedom into the data:

1. **`StackSegWf.delimit` generalized** (Runtime.lean) — now carries `Ty.EffWeaken tail
   εBelow` and types the below-part at any `εBelow ⊇ tail`, exactly mirroring the
   already-generalized `StackWf.delimit`. Threaded through `stackSeg_append` and
   `stackSeg_toStackWf` (the `delimit` case passes the carried weaken instead of `refl`).
2. **`partialResume` quantified over the discharge row** (Runtime.lean):
   ```
   partialResume : (∀ εBelow, Ty.EffWeaken tail εBelow →
                     StackSegWf acc.reverse reply εtop ret εBelow) →
                   Ty.TyEquiv (kontTy reply tail ret) τ → HasTypeV (Resume acc iEnv []) τ
   ```
   Sound because the captured prefix runs at the **fixed** handled row `εtop`; only the
   re-pushed final `Delimit`'s discharge varies, so the witness is uniform in `εBelow`.
3. **`resume_preserves`** (Soundness.lean, replaces `resume_preserves_exact`) — general, no
   exact-row hypothesis: from the frame's `EffWeaken εf ε` and `tail ≈ εf` derive
   `EffWeaken tail ε`, instantiate the stored segment at `εBelow := ε`, and compose onto
   `rest` (still at `ε`) with `stackWf_resume`. The `resume` field is **removed** from
   `HandlerObligations`; `preservation_V`'s two `partialResume` arms call `resume_preserves`
   directly.

## Remaining: `perform` (the one hard dispatch, design §5)

`HandlerObligations.perform` is the last field. `doPerformR` walks the stack to the nearest
matching `Delimit label`, re-pushes it into `acc`, builds `resume = Resume acc iEnv []`, and
installs `CallWith arg :: CallWith resume :: rest` running the handler `h`. Typing the
successor needs a **`StackWf`-prefix → `StackSegWf` walk lemma**: by induction on
`StackWf rest σ ε τ`, walking past non-matching `Delimit l'` (`l' ≠ label`, where the row
reasoning carries `label` across each discharge via `EffContains.tail`), produce
(a) the matching `Delimit`'s `HasTypeV h (handlerTy lift reply tail ret)`, (b) the captured
prefix as `StackSegWf acc.reverse reply εtop ret tail` — now in the **quantified** form
this pass introduced (the walk builds it uniformly in `εBelow`, with the re-pushed `Delimit`
as the final frame carrying `EffWeaken tail εBelow`), and (c) the below-stack
`StackWf rest' ret ε τ`. Then the successor types as
`callwith (h_arg : arg:lift) (EffWeaken ∅ ε) (callwith (resume:kontTy) (EffWeaken tail ε)
(rest' at ret))` with control `h : handlerTy …`. The lift/reply matching (`perform`'s
`argTy = lift`, `replyTy = reply`) comes from the ambient-row membership (`ε ⊇ label:(lift,
reply)`, and the perform's row `⟨label:(argTy,replyTy)|μ⟩ ≈ ε`), the existing effect-safety
machinery. This is the substance of handler soundness; the quantified-`partialResume`
foundation it needs is now in place. Budget it as its own focused pass.

`TauKeepsRow → RowEvolves` (the T7 row-evolution for the effect-escape/divergence results)
remains the separate follow-up, unblocked on the `Delimit` side.
