---
date: 2026-06-17
milestone: T5 (Handle) — discharge `perform` (the last HandlerObligations field)
status: NOT discharged — the conv-free redirect is INSUFFICIENT (new finding); two viable fixes scoped; tree green
---

# `perform` dispatch — the row-conv at `Delimit` frames is unavoidable

`HandlerObligations.perform` is the last field. Foundation in place: generalized
`StackWf.delimit`/`StackSegWf.delimit` (both carry `EffWeaken tail ε`), quantified
`partialResume`, `resume_preserves`, `install_preserves`, the six `stackWf_*_inv`
inversion lemmas, and `EffWeaken` on `StackSegWf.{arg,applyf,callwith}` (obstacle 1, banked).

## The proof structure (validated; the successor types GIVEN the segment)

`reduceCall (Perform label []) v ann fenv rest = .tau cfg'` iff `doPerformR label v fenv rest [] = .ok (c,e,k')`, with the matching deep `Delimit label h e`:
```
cfg' = (.V h, e, (CallWith v e) :: (CallWith resume e) :: rest'),  resume = Partial (Resume acc' iEnv) [],  acc' = (Delimit label h e false) :: acc
```
Pick `ε' := εInner` (the row `rest'` runs at, from `stackWf_delimit_inv`). The successor types:
- control `h : handlerTy lift reply tail ret = lift →⟨∅⟩ (kontTy reply tail ret →⟨tail⟩ ret)`;
- `CallWith v` frame: incoming `h`; `v : lift` (from `hv : v:argTy` + effect-safety `argTy ≈ lift`), `EffWeaken ∅ ε'`, continuation feeds `h v : kontTy→⟨tail⟩ret`;
- `CallWith resume` frame: incoming `h v`; needs `resume : kontTy reply tail ret`, `EffWeaken tail ε'` (= the Delimit's `EffWeaken tail εInner`), continuation `StackWf rest' ret ε' τ` (from `stackWf_delimit_inv`);
- `resume : kontTy reply tail ret` via `partialResume` with `reply := retTy` then a leaf `HasTypeV.conv` (`retTy ≈ reply` by effect-safety) — this much IS conv-free at the value level, as the prior redirect hoped.

**The one missing piece** is the quantified segment `∀ εBelow, EffWeaken tail εBelow → StackSegWf acc'.reverse retTy ε ret εBelow`, where `acc'.reverse = acc.reverse ++ [Delimit_match]`, built by a stack-walk induction over `rest`.

## ⚠ NEW finding: the conv-free walk is INSUFFICIENT — `Delimit` frames need a row-conv

The right walk is `induction hK` on `StackWf K σ ε τ` (StackWf is NOT in the `HasTypeV`
mutual block, so `induction` is allowed), threading the **decoupled** invariant:
> segment at *concrete* endpoints `(σ0, εcur0)` + `TyEquiv σ σ0` + `TyEquiv ε εcur0`, plus
> `EffContains εcur0 label argTy replyTy` (label's binding, from effect-safety).

This handles the `conv` case **cleanly** (the conclusion `∃ε', MStateWf (.run cfg') τ ε'`
is σ/ε-free; the segment stays put, just compose the `TyEquiv`s) and the non-`Delimit`
frame cases (extend the segment, `HasTypeV.conv` the frame *value*'s domain to align the
type — the redirect's value-conv idea works **here**).

**But it breaks at every `Delimit` frame** (both the matching one and each walked-past
`l' ≠ label`). To append a `StackSegWf.delimit` (which discharges the **head** label of an
**exact** `.effectExtend l lift reply tail` input row) onto the running segment, the
segment's concrete output row `εcur0` must *equal* that head-shaped row. But the induction
only gives `TyEquiv ε εcur0` with `ε` the exact constructor row — so `εcur0 ≈ head-shaped`,
**not** `=`. Earlier `conv` frames in the prefix inject a genuine `TyEquiv` (row reordering
is allowed by `StackWf.conv`), so `εcur0` can be a *reordering* of the head-shaped row
(label/`l'` not syntactically at the head). `StackSegWf.delimit` cannot consume it.

So the value-conv that absorbs the *type* mismatch has **no row analogue** in `StackSegWf` —
exactly the `StackSegWf.conv` gap, and it bites at *every* `Delimit`, not just non-`Delimit`
runs. **The prior "rows need no conv" claim is wrong** (it holds only between consecutive
non-`Delimit` frames; the `Delimit` boundary is where the row-conv is needed).

## Two viable fixes (next pass)

1. **Membership-based `StackSegWf.delimit`** — let the frame discharge `l` from a row that
   merely *contains* `l` (`EffContains εin l lift reply`, with the below-part related to
   "εin minus l" up to `TyEquiv`), instead of requiring the syntactic head
   `.effectExtend l …`. Then `εcur0 ≈ head-shaped` suffices (membership is `TyEquiv`-stable
   via `tyEquiv_effContains`). Ripple: `stackSeg_toStackWf`'s `delimit` case must bridge to
   the head-based `StackWf.delimit` (needs a row-reorder/`StackWf.conv` on the base — which
   *is* available at that composition point). Likely the cleanest.
2. **`StackSegWf.conv` after all, via `@StackSegWf.rec` with trivial motives** — the prior
   pass rejected the recursor as "impractical (spans all 4 mutual members)", but the motives
   for `HasTypeV`/`EnvWf`/`BuiltinPartialWf` can be set to `fun _ _ => True` (trivial minor
   premises), leaving only the `StackSegWf` constructors to discharge. Re-prove
   `stackSeg_append`/`stackSeg_toStackWf` that way with a `conv` case. Worth re-evaluating —
   it may be quite tractable and is the most uniform fix.

Either unblocks the walk; the successor-typing half above is ready. Recommend trying (1)
first (smaller surface), falling back to (2). The `perform` field stays isolated in
`HandlerObligations` until then; the ε-free value/no-bad-crash soundness is unconditional
regardless. Tree green (no code change this pass; obstacle-1 `EffWeaken`-on-segment-frames
remains banked from the prior pass).

## ⚠ Update (next pass): fix (1) DELIVERED green; fix (2) is ALSO required (sharper finding)

**Fix (1) — membership-based `StackSegWf.delimit` — DELIVERED** (commit `9542b082`,
green, `lake build` 1771 jobs + spec 104/104). Implemented as `TyEquiv εin
(.effectExtend l lift reply tail)` carried on the frame (input row up to reorder), the
`StackSegWf.delimit` indexed by a free `εin`. `stackSeg_append` threads the equiv;
`stackSeg_toStackWf`'s `delimit` case bridges to the head-based `StackWf.delimit` via
`StackWf.conv (.delimit …) (.refl _) he.symm`. This resolves the **row-slack at
`Delimit` boundaries** (the `εcur ≈ head-shaped` mismatch).

**But tracing the full walk shows fix (2) is unavoidable too** — the membership-`delimit`
only fixes the *row* slack; there is an independent **type slack at the segment frame
junctions** that `value-conv` cannot fully absorb:

- The walk is `induction` on the stack list, using the `stackWf_*_inv` lemmas (they fold
  `conv`, giving each frame's data with `TyEquiv σ <frame-input>` + `TyEquiv ε ε0`).
  Extending the captured segment `acc.reverse` by the next frame requires the junction
  type to match **syntactically** (`stackSeg_append` middle endpoints), but inversion only
  gives `TyEquiv`.
- **`applyf`/`arg`/`delimit`** frames absorb the slack via **`HasTypeV.conv` on the frame
  *value*** (convert the function value's *domain* `argTy → σ` with `.congrFun`; the frame
  input then *is* `σ`). The row slack is absorbed by `StackWf.conv` on the tail (rows are
  constant across non-`delimit` frames) and, at `delimit`, by membership (fix 1).
- **`callwith` (and `assign`) CANNOT.** A `StackSegWf.callwith` frame's input is
  structurally `.fun argTy εf retTy` (resp. `assign`'s `defnTy`); the walk only gives
  `TyEquiv σ (.fun argTy εf retTy)`, and `σ` need not be *syntactically* an arrow (an
  earlier `conv` frame can have reordered/renamed it). Value-conv lives on the stored value,
  not the segment's *input endpoint*, so it cannot move `σ`→arrow there. This is exactly a
  **segment input-endpoint `conv`**, i.e. fix (2).

**Conclusion:** the walk needs BOTH — membership-`delimit` (done) for the row slack, and a
**`StackSegWf` endpoint type-conv** for the `callwith`/`assign` junction slack. Fix (2) is
the mutual-recursor re-architecture (`@StackSegWf.rec` with `True` motives for the other 3
members, re-proving `stackSeg_append`/`stackSeg_toStackWf` with a `conv` case) — a real
metatheory slice, the genuine remaining obstacle. The successor-typing half (handler applied
to `arg`/`resume`, lift/reply via `EffContains` determinism) is still ready. Membership-
`delimit` is banked and green regardless; `perform` stays the lone isolated
`HandlerObligations` field. ε-free value/no-bad-crash soundness unconditional throughout.
