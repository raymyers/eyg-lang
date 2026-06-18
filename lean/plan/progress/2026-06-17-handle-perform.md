---
date: 2026-06-17
milestone: T5 (Handle) — discharge `perform` (the last HandlerObligations field)
status: NOT discharged — two concrete StackSegWf generalizations identified (compiler-pinned); reverted to green
---

# `perform` dispatch — the obstacle is precise: `StackSegWf` must be generalized to mirror `StackWf`

`HandlerObligations.perform` is the last field. I worked out the full proof structure and
hit a **genuine, compiler-confirmed** obstacle: the captured-prefix segment cannot be
*built* from the call-site `StackWf` because `StackSegWf` is strictly less flexible than
`StackWf`. Two generalizations are needed; the second has a structural wrinkle. Tree
reverted to green (no code change).

## The proof structure (validated on paper, ready once the foundation is in)

`reduceCall (Perform label []) v ann fenv rest = .tau cfg'` happens iff
`doPerformR label v fenv rest [] = .ok (c,e,k')`, with the matching deep `Delimit label h e`:
```
cfg' = (.V h, e, (CallWith v e, mt) :: (CallWith resume e, mt) :: rest')
resume = .Partial (.Resume acc' iEnv) [],  acc' = (Delimit label h e false) :: acc
```
Pick `ε' := εInner` (the row `rest'` runs at). The successor types as:
- control `h : handlerTy lift reply tail ret`;
- `CallWith v` frame: `v : lift` (`hv` + effect-safety `argTy ≈ lift`), `EffWeaken ∅ ε'`;
- `CallWith resume` frame: `resume : kontTy reply tail ret`, `EffWeaken tail ε'` (from the
  Delimit's `EffWeaken tail εInner`), continuation `StackWf rest' ret ε' τ` (from
  `stackWf_delimit_inv`);
- `resume` typed via `partialResume`: needs
  `∀ εBelow, EffWeaken tail εBelow → StackSegWf acc'.reverse retTy ε ret εBelow`
  (use `reply := retTy`, then `HasTypeV.conv` the resume to the handler's `reply`-arg type,
  since `retTy ≈ reply` by effect-safety — avoids needing a `reply`-exact segment).

The lift/reply types come from effect-safety: the perform's latent `εf = ⟨label:(argTy,
replyTy)|μ⟩` and `EffWeaken εf ε` force `TyEquiv εf ε` (a non-empty effectExtend ≉ ∅), so
`ε ≈ ⟨label:(lift,reply)|tail⟩` matches the matching `Delimit`'s row — giving `lift ≈ argTy`,
`reply ≈ replyTy ≈ retTy`.

**The one missing piece** is the segment `StackSegWf acc'.reverse retTy ε ret εBelow`, built
by a **stack-walk induction**: walk `rest` (= `prefix ++ [Delimit_match] ++ rest'`),
maintaining `StackSegWf acc.reverse retTy ε σ εcur` (acc.reverse is the captured prefix as a
segment; `(σ,εcur)` = current `StackWf` walk point). Peel each frame via the `stackWf_*_inv`
inversion lemmas, extend the segment by the matching `StackSegWf` frame, recurse; at the
matching `Delimit` append `[Delimit_match]` (a `StackSegWf.delimit`, quantified in `εBelow`).

## Obstacle 1 — `StackSegWf` frames lack `EffWeaken` (compiler-confirmed)

`StackWf.{arg,applyf,callwith}` carry `Ty.EffWeaken εf ε` (a *pure* function applied under
an effectful ambient — the foundation delivered earlier this session). `StackSegWf.{arg,
applyf,callwith}` do **not** — they pin the function's latent to the segment row `εin`
exactly:
```
StackSegWf.applyf : HasTypeV f (.fun argTy εin retTy) → StackSegWf rest retTy εin … → …
```
So a captured prefix containing a pure-fn-under-effectful application (e.g.
`perform Log x; pureFn (…)`) has a `StackWf.applyf` with `εf = ∅, ε ≠ ∅` that **no**
`StackSegWf.applyf` can represent. **Fix (mechanical):** add `Ty.EffWeaken εf εin` to
`StackSegWf.{arg,applyf,callwith}` (mirror `StackWf`); thread it through `stackSeg_append`
and `stackSeg_toStackWf`'s frame cases (each currently passes `effWeaken_refl`; pass the
carried weaken instead). Verified: this part type-checks structurally — the build errors at
`stackSeg_append` are exactly the three frame cases needing the extra arg.

## Obstacle 2 — `StackSegWf` needs `conv`, which breaks the composition lemmas' induction

The frame inversion lemmas (`stackWf_applyf_inv` etc.) expose the frame's input/row only up
to `TyEquiv` (`TyEquiv σ argTy`, `TyEquiv ε ε0`), because they fold `StackWf.conv`. So while
walking, the running segment's hole `(σout,εout)` matches the next frame's exact endpoints
only up to `TyEquiv` — the segment needs a `conv` to reconcile. A `StackSegWf.conv` (convert
all four endpoints up to `TyEquiv`) is the natural mirror of `StackWf.conv` and is **not
derivable** (it can't be a lemma — `StackSegWf.nil` pins `σin=σout`, `εin=εout`, so conv of
`nil` to unequal endpoints is not `nil`-shaped). So it must be a constructor.

**But adding it breaks `stackSeg_append`/`stackSeg_toStackWf`** (compiler-confirmed: "Alternative
`conv` has not been provided"). Those are proved by `induction seg` (the list) `+ cases hseg`;
the `conv` case wraps the **same** list, so the list-induction IH (for the tail) does not
apply, and mutual inductives forbid `induction hseg`. **Fix (the real work):** re-architect
the two composition lemmas to handle `conv` — options:
- prove them via the mutual recursor `@StackSegWf.rec` (or `Nat`-fueled on segment length)
  rather than `induction seg + cases hseg`, so the `conv` case can recurse on the wrapped
  derivation; the `conv` case of `append` is: peel the conv, `StackWf.conv` the base stack
  `hk` to the inner endpoints, recurse, then `StackWf.conv` the result back — sound, just not
  expressible with the current `induction seg` skeleton;
- OR avoid `StackSegWf.conv` by threading exact types in the walk: before extracting each
  frame, `StackWf.conv` the *stack* to align σ/ε with the inversion's `argTy`/`ε0`, so the
  segment is always built at exact types. This keeps `StackSegWf` conv-free but needs care
  that the walk's running types stay syntactically aligned (the inversion still gives
  `TyEquiv`, so some conv must absorb it — likely still forces a segment-level conv at the
  `nil` base / first frame). The recursor route is cleaner.

## Recipe for the next pass (no remaining design unknowns)
1. Generalize `StackSegWf.{arg,applyf,callwith}` with `EffWeaken εf εin`; re-green
   `stackSeg_append`/`stackSeg_toStackWf` frame cases (mechanical).
2. Add `StackSegWf.conv`; re-prove `stackSeg_append`/`stackSeg_toStackWf` via the mutual
   recursor (the `conv` case threads `StackWf.conv` on the base stack). Re-green
   `resume_preserves` (unaffected — it consumes a given segment).
3. Prove `stackWf_segment_of_walk` (the induction above) and feed it + `stackWf_delimit_inv`
   into a `perform_preserves` theorem; remove `perform` from `HandlerObligations` (→ fully
   discharged, `{}`) and call it from `preservation_V`'s `partialPerformNil` handled arm
   (currently routed through `hho.perform`).

This is the genuine continuation-typing core (design §5); the effect-safety half is already
done (the unhandled escape in `progress`/`preservation_perform`). With `StackSegWf`
generalized to mirror `StackWf`, the walk closes. Budget it as its own pass — it is a real
metatheory slice (the `conv`-in-mutual-block re-architecture), not a mechanical grind.

---

## Update (pass 2): obstacle 1 DONE (green); obstacle 2's recursor is impractical — use a conv-free walk

**Obstacle 1 — DELIVERED green** (commit `a3690d24` on `handle-perform2`): `EffWeaken εf εin`
added to `StackSegWf.{arg,applyf,callwith}` (mirrors `StackWf`); `stackSeg_append`/
`stackSeg_toStackWf` frame cases pass the carried weaken. `lake build` 1771 jobs. This is
the segment analog of the earlier `StackWf` effect-weakening; reusable regardless of how
obstacle 2 is solved.

**Obstacle 2 — the `StackSegWf.conv` route is BLOCKED harder than the note said.** I added
`StackSegWf.conv` (all four endpoints) and tried to re-prove the two composition lemmas by
`induction hseg`. The compiler rejects it outright:
```
error: The `induction` tactic does not support the type `StackSegWf` because it is
       mutually inductive
```
`StackSegWf` is genuinely mutual with `HasTypeV` (cycle: `HasTypeV.partialResume` →
`StackSegWf` → `StackSegWf.delimit`'s handler → `HasTypeV`). The only derivation-recursion
tool is `@StackSegWf.rec`, whose motives/minor-premises cover **all four** block members
(`HasTypeV` alone has 25+ constructors) — impractical to discharge by hand. And `induction
seg`/`cases hseg` cannot handle the `conv` case (it wraps the **same** list, so the
list-IH/structural recursion does not apply). So **`StackSegWf.conv` as a constructor is a
dead end** without re-architecting the mutual block.

**The way forward — a conv-FREE walk (do this next):** do NOT add `StackSegWf.conv`. Build
the captured segment during the `doPerformR` walk by converting the **frame values** with
the already-available `HasTypeV.conv` instead of converting the segment:
- The per-frame inversion (`stackWf_applyf_inv` etc.) yields `TyEquiv σ argTy` and the
  `rest'` typed at the **exact** `(retTy, ε0)`. Continue the walk at exact types.
- To append a frame to the running segment whose output is `σ_prev` while the frame's
  natural input is `argTy` (with `TyEquiv σ_prev argTy`), `HasTypeV.conv` the frame's
  stored value (`.congrFun` on the domain) so the `StackSegWf.{applyf,callwith}` frame's
  input becomes `σ_prev` exactly — no segment-level conv needed.
- **Rows need no conv across non-`Delimit` runs:** consecutive non-`Delimit` `StackWf`
  frames share the *same* exact ambient `ε0` (each `applyf`/… keeps `rest` at the same
  `ε`), so the segment row is constant between `Delimit`s; only `Delimit` changes it, and
  `StackSegWf.delimit` already carries the `EffWeaken` for that.
This keeps `StackSegWf` conv-free (composition lemmas stay as the working `induction seg +
cases hseg`), and value-conv is leaf-level (always available). The remaining work is then
the walk induction itself + the effect-safety threading (the perform label stays in the row
across non-matching `Delimit l'`: `label ∈ ⟨l':(..)|t'⟩` with `l' ≠ label` ⇒ `label ∈ t'`,
and `EffWeaken t' εInner` with `label ∈ t'` rules out the `t' ≈ ∅` disjunct ⇒ `label ∈
εInner`). Budget the walk as the next pass; obstacle 1 is banked and the conv-free design
removes the mutual-recursor blocker.
