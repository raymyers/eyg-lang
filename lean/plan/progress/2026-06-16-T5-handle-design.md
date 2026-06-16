# T5 — Typing `Handle`: Delimit / Resume frame typing (design)

**Status:** design. Prereqs done: T5a (`EffRow`), T5b (`doPerformR`), T5c (`Perform`
+ effect safety, `wait` typing, `ReplyContract`, the effect-escape `progress`). This
is the **last** T5 piece and the fork's *direct frame typing* route (no published
precedent — the genuinely novel obligation). The transparent `doPerformR` (T5b) is
what makes it tractable at the kernel level.

## The handler scheme (`contextual.gleam` `handle`, lines 501-516)

```
handle(label) =
  Fun( handler, Empty,
    Fun( exec, tail, return))
where
  lift   = q0   reply = q1   tail = q2   return = q3
  kont    = Fun(reply, tail, return)                       -- the resumption
  handler = Fun(lift, Empty, Fun(kont, tail, return))      -- gets lift value + resume
  exec    = Fun(Record Empty, EffectExtend(label,(lift,reply),tail), return)
```

`handle(label) handler exec` runs `exec ()` under a fresh handler for `label`; an
`exec` `perform label v` (`v : lift`) invokes `handler v resume`, where `resume :
reply → tail → return` is the delimited continuation. The handled computation's row
drops from `EffectExtend(label,(lift,reply),tail)` (inside `exec`) to `tail`
(the result of `handle`). **`label` is discharged.**

## The dynamics (already in `Reduction.lean` / `State.lean`, transparent except as noted)

- `reduceDeep label handler exec` ⇒ `.tau (.V unit, env, Apply exec :: Delimit label
  handler env false :: k)` — push the `Delimit` frame, then run `exec ()`.
- `Delimit` met by a **value** (`reduceApply`): `.Delimit _ _ _ _ => .tau (.V val, env,
  rest)` — pass-through. So when `exec` returns normally with `v : return`, the
  `Delimit` is popped and `v : return` flows on. (No "return clause" — exec's normal
  result *is* the handle result.)
- `Delimit` met by a **perform** (`doPerformR`, the handled branch): walk to the
  nearest `Delimit` whose label matches; build `resume = Partial (Resume acc iEnv) []`
  (`acc` = the frames traversed, **with the matching `Delimit` re-pushed** for a deep
  handler — `shallow=false`), then install `CallWith arg :: CallWith resume :: rest`
  and run the handler `h` (`.ok (.V h, e, k)`). So `h` is applied to `arg : lift` then
  to `resume`.
- `Resume` met (`reduceCall`): `.Resume frames capturedEnv, [] => .tau (.V arg,
  capturedEnv, move frames k)` — re-push the captured `frames` onto the current stack
  and feed the reply `arg : reply` in. `move` just reverses the frames on (total def).

## Typing obligations (the novel part)

### 1. `HasType.handle` (Typing.lean)
Transcribe the scheme. `handle(label)` is a value (resting partial chain), typeable
at any ambient `ε`:
```
| handle {Γ l lift reply tail ret ε ann} :
    HasType Γ ⟨.Handle l, ann⟩
      (.fun (handlerTy l lift reply tail ret) .empty
        (.fun (execTy l lift reply tail ret) tail ret)) ε
```
with `kontTy = .fun reply tail ret`, `handlerTy = .fun lift .empty (.fun kontTy tail
ret)`, `execTy = .fun (.record .empty) (.effectExtend l lift reply tail) ret`. Plus
`inv_handle` and the `hasType_expr_form` arm (+ extend every `rcases` over it by one,
as for `Perform`).

### 2. Runtime partials (Runtime.lean) — `HasTypeV`
`Handle l` accumulates two args (`handler`, then `exec`) before `reduceDeep` fires:
- `partialHandleNil` : at the full `handle(l)` arrow.
- `partialHandleOne handler` : `exec` not yet supplied; carries `HasTypeV handler
  (handlerTy …)`, typed at `Fun(execTy, tail, ret)`.
Plus `canonical_arrow` + `conv` cases. (`reduceDeep` runs only at the 2nd arg, so
there is no `partialHandleTwo` resting value.)

### 3. The `Delimit` frame in `StackWf` (Machine.lean) — **the answer-type transformer**
A `Delimit l handler henv false` frame **discharges `l`**: the computation *above* it
runs under `EffectExtend(l,(lift,reply),tail)`; the frame's *output* (and everything
below) runs under `tail`.
```
| delimit {a l handler henv Γ lift reply tail ret ε τout rest} :
    EnvWf henv Γ →
    HasTypeV handler (handlerTy l lift reply tail ret) →
    StackWf rest ret tail τout →                      -- below: row is `tail`, in-type `ret`
    StackWf ((Kontinue.Delimit l handler henv false, a) :: rest)
            ret (.effectExtend l lift reply tail) τout
```
Note: input type `ret` (exec's normal result passes through), input row
`EffectExtend(l,…,tail)` (what the handled code performs), and `rest` is typed at the
**discharged** row `tail`. The value-pass-through reduction
(`reduceApply … Delimit => .V val, rest`) is then preservation-sound: `ret` in,
`StackWf rest ret tail τout` carries it — **but** the ambient row changes from
`EffectExtend(l,…)` to `tail` across the frame, so `MStateWf`/preservation must allow
the row to *shrink* at a `Delimit` pop. ⚠ This is the one place the ambient `ε` is not
invariant across a step — see "row-change subtlety" below.

### 4. `Resume` partial typing — the reified continuation
**⚠ CORRECTION (found by attempting the impl).** The T5d shortcut "`StackWf` *is* the
segment typing" holds **only while every frame keeps the ambient row constant** — true
for the 6 pre-`Handle` frames, but **`StackWf.delimit` changes the row** (discharges
`l`: `EffectExtend(l,…,tail) → tail`). `stackWf_append`/`stackWf_move` are proved with a
*uniform* `ε` for `seg` and `k`; once `seg` may contain a `delimit`, its bottom row (at
the nil/hole, where `k` splices in) differs from its top row, and `StackWf`'s single
`ε` index does not expose that bottom row — so the uniform-`ε` append lemma cannot even
be *stated* to match `k`'s row. And the captured `acc` for a **deep** handler always
re-pushes the matching `Delimit`, so `acc.reverse` *does* contain a `delimit`. Hence:
- `stackWf_append`/`stackWf_move` (T5d) stay valid **only for delimit-free segments**
  (still useful — most captured prefixes between a `perform` and its handler are
  delimit-free *except* the final re-pushed `Delimit`).
- The higher-order "segment transformer" alternative (`partialResume` storing a
  `∀ k, StackWf k … → StackWf (move acc k) …` function) is **illegal**: `StackWf` left
  of `→` inside a constructor is a non-positive occurrence in the mutual block.
- **Fix:** a dedicated first-order `StackSegWf seg σin εin σout εout` inductive
  (mirror the 7 `StackWf` frames, but track **both** endpoint type+row; `delimit`'s
  output row is `tail`), in the `HasTypeV`/`EnvWf` mutual block (it references
  `HasTypeV`). Then `stackSeg_append : StackSegWf seg σin εin σmid εmid → StackWf k σmid
  εmid τ → StackWf (seg ++ k) σin εin τ` and the `move` corollary. `partialResume`
  stores `StackSegWf acc.reverse reply εtop ret tail`; the `Resume` successor types via
  the corollary with the handler's continuation `k` at row `tail`.

This is the single remaining hard design point. Everything else (rules, `partialHandle*`,
`StackWf.delimit`, the per-site `delimit` cases, the dispatch lemma §5) is mechanical
once `StackSegWf` exists. Original (superseded) sketch:
`resume = Partial (Resume acc iEnv) []` must type as `Fun(reply, tail, ret)` (the
`kontTy`). When called with `r : reply`, it does `.V r, capturedEnv, move acc k`. So
`acc` is a captured stack segment that takes a `reply`-value, under row `tail`, to…
the answer. Typing `Resume` means typing the captured frames `acc` as a
`StackWf`-segment:
```
| partialResume {acc iEnv reply tail ret τ} :
    (∀ k below, StackWf k ret tail below → StackWf (move acc k) reply tail below) →   -- segment transformer
    TyEquiv (.fun reply tail ret) τ →
    HasTypeV (.Partial (.Resume acc iEnv) []) τ
```
i.e. `acc` is a **stack-segment transformer** `reply ⇒ ret` (prepend it and it turns a
`ret`-consumer into a `reply`-consumer), capturing the delimited context between the
`perform` and its `Delimit`. The deep re-push of the `Delimit` into `acc` means the
resumed continuation is *itself* delimited (handles further performs) — the segment
transformer must reflect that (it ends in a `delimit` frame). This higher-order
"segment transformer" formulation is the crux and the riskiest piece; an alternative
is to reify `acc` concretely and prove a `move`-append `StackWf` lemma
(`stackWf_move : StackWf-seg acc reply tail ret → StackWf k ret tail b → StackWf (move
acc k) reply tail b`) and store the segment typing directly.

### 5. Generalize `stackWf_doPerformR_unhandled` — ⚠ THE HARDEST PROOF (do last)
**This is the novel core of handler soundness and the one genuinely hard proof left.**
The T5e `∃ε'` preservation foundation is committed; `stackWf_move` (Resume) and all the
typing infrastructure are easy by comparison. The dispatch lemma replaces the current
"typed stack ⇒ no `Delimit` ⇒ always unhandled" with a walk that may pass
**effect-discharging `Delimit` frames for *other* labels**:

> `stackWf_doPerformR_dispatch`: for `StackWf k σ ε τ`, `doPerformR op arg env k acc`
> either (handled) returns `.ok (.V handler, henv, CallWith arg :: CallWith resume ::
> rest)` where the nearest `Delimit op …` frame's handler types the successor (handler
> applied to `arg : lift` and `resume : kontTy`, the latter via `stackWf_move` on the
> captured `acc`); or (escape) returns `.error (.UnhandledEffect op arg)` **and `op ∈
> ε`** — the residual bottom row still carries `op` because every `Delimit` walked past
> discharged a *different* label (`l' ≠ op`), so by `StackWf.delimit`'s row relation the
> row above each is `EffectExtend(l', …, rowbelow)` with `op` preserved into `rowbelow`.

The effect-safety half is the subtle part: prove by induction on `StackWf` that walking
past a `Delimit l' …` (with `l' ≠ op`, the only way `doPerformR` continues) keeps `op`
in the row, because that frame's input row is `EffectExtend(l', lift', reply', rowbelow)`
and `op ≠ l'` ⇒ `EffContains` of `op` transfers from the row-below to the row-above
(`EffContains.tail`). The `acc` threading for `resume`'s typing must track that the
captured prefix is a `StackWf`-segment `reply ⇒ ret` (use `stackWf_move`; the deep
re-push of the matching `Delimit` into `acc` keeps the resumption delimited).

Mechanical generalization (below) of the original sketch:
Currently (T5c) a typed stack has *no* `Delimit`, so every perform escapes. With the
`delimit` frame, the lemma splits:
- **walk past non-`Delimit` frames** (as now), and past `Delimit l' …` with `l' ≠ l`
  (accumulating into `acc`), until
- the nearest `Delimit l …` (match): `doPerformR` returns `.ok (.V handler, henv,
  CallWith arg :: CallWith resume :: rest)` — a **`.tau`** (handled, resumes), and the
  successor is well-typed (handler applied to `arg : lift` and `resume : kont`).
- or `[]`: unhandled, escapes (effect safety: `op ∈ ε`, the residual row after all
  the discharges still carries `op`).
So `preservation_perform` becomes a *case split*: handled ⇒ the `.tau` successor types
(handler call); unhandled ⇒ the `wait` (as in T5c). And the `progress` perform-partial
case likewise: a typed stack with a matching `Delimit` ⇒ the perform `.tau`-steps
(handled), else escapes with `op ∈ ε`.

### Row-change subtlety — ⚠ SHARPENED FINDING (resolve first, next session)
The ambient `ε` is **not invariant** across a `Delimit` pop (it shrinks `EffectExtend
l … tail → tail`) or a `perform`-into-handler (the handler runs under `tail`, the
performed label discharged). On closer analysis this is **more than bookkeeping**: it
*breaks the current `preservation` statement*

```
preservation : MStateWf s τ ε → Reduce s μ s' → ReplyContract ε s μ → MStateWf s' τ ε
```

because the **same `ε`** appears in hypothesis and conclusion. Concretely, the
`Delimit`-value-pop step `( .V v, env, Delimit l h e :: rest )  ⟶  ( .V v, env, rest )`
takes a state well-typed at `ε = EffectExtend l (lift,reply) tail` to a successor
well-typed only at `ε' = tail` (the `StackWf.delimit` constructor types `rest` at
`tail`). So `MStateWf s' τ ε` is **false**; only `MStateWf s' τ tail` holds.

`StackWf.delimit` itself fits the **existing** `StackWf` signature with no change — the
ε index is just "the ambient row at the top of this segment", and the constructor
recurses `StackWf rest ret tail τout` at a *different* row than its own input
`EffectExtend l lift reply tail` (the other 6 frames keep the row constant; only
`delimit` changes it). The problem is purely in the **theorem statements**, not the
judgments.

**Decision for next session — make the row an output, not an invariant:**
restate preservation as `MStateWf s τ ε → Reduce s μ s' → … → ∃ ε', MStateWf s' τ ε'`
(the successor is well-typed at *some* row — the same one except a `Delimit` pop /
handled `perform`, which yield `tail`). This is sound and sufficient: the headline
`soundness_value` only concludes `HasTypeV v τ`, which is **ε-free**, so the existential
row never obstructs it; the `progress` effect-escape clause already names its own `op`/
`ε` witnesses per state. The `ReplyContract`/`EffContains` reasoning is unaffected.
Alternative (heavier, rejected): keep `ε` fixed and carry a "the run's row only ever
shrinks" relation — needless for the value/no-crash result. *Resolve this restatement
first; then the `Delimit`/`Resume`/handled-`perform` cases are mechanical (the keystone
`stackWf_move` already types `Resume`).* Note every existing `cases hst` site
(`preservation_V`, `reduce1Run_done_value_typed`, `progress`, `preservation_perform`)
gains a `delimit` frame case under this restatement.

## ✅ Implementation findings (from a full dry-run of the cascade)

A complete attempt built **all the infrastructure green** (then reverted to keep the
tree green, the `Soundness.lean` cascade being too large for one pass). Known-correct:
- `Typing.handle` + `handleTy`/`handlerTy`/`execTy`/`kontTy` abbrevs; `inv_handle`;
  the `hasType_expr_form` `Handle` arm (`iterate 18`), `Perform` arm → `Or.inl ⟨_,rfl⟩`.
- `StackWf.delimit` (Machine) — **must NOT carry `EnvWf henv Γ`.** The frame's stored
  env is never used for typing (the handler is a self-contained value), and at
  `reduceDeep` the frame env is arbitrary, so requiring `EnvWf` makes it *unprovable*.
  Drop it. Same for `StackSegWf.delimit`.
- `StackSegWf` joins the `HasTypeV`/`EnvWf` **mutual block**; `stackSeg_append` /
  `stackSeg_toStackWf` re-prove by `induction seg generalizing σin εin` + `cases hseg`
  (mutual inductives forbid `induction hseg`). `stackWf_resume` (= `stackSeg_toStackWf`
  after `move_eq`) types `Resume`'s `move acc k`.
- `HasTypeV.partialHandleNil` (`handleTy …`), `partialHandleOne handler`
  (`HasTypeV handler (handlerTy …)`, typed at `Fun(execTy,tail,ret)`), `partialResume`
  (`StackSegWf acc.reverse reply εtop ret tail` + `TyEquiv (kontTy reply tail ret) τ`).
  Plus their `HasTypeV.conv` and `canonical_arrow` cases (`Or.inr ⟨_,_,rfl⟩`). The old
  uniform `stackWf_append`/`stackWf_move` are **deleted** (unprovable once `delimit`).

Site-by-site strategy for the remaining `Soundness.lean` cascade:
- **`stackWf_doPerformR_unhandled` is now false — delete it;** rework its 4 uses to
  `cases hdp : doPerformR op arg env rest []` (`.error` → escape as T5c, `.ok` →
  handled `.tau`).
- **`reduce1Run_done_value_typed`**: every new case is a *contradiction* (the
  reductions are `.tau`/`.perform`, never `.done (.value _)`).
- **`progress`**: every new case just *exhibits a step* (`Or.inl`); escape → the 4th
  (effect-escape) disjunct; plus the `Handle` eval case + `rcases`/`expr_form` `+1`.
- **`preservation_perform`**: new cases are contradictions; `partialPerformNil`
  case-splits `doPerformR` (escape = the wait, as T5c).
- **`preservation_V`** (the real work): `delimit`-pop (value → `.tau (.V v, env, rest)`,
  types at row `tail`, `∃ε'`); `partialHandleNil` → accumulate to `partialHandleOne`;
  `partialHandleOne` → `reduceDeep` (`Apply exec :: Delimit :: rest`, via `StackWf.applyf`
  + `StackWf.delimit` at row `EffectExtend(l,…,tail)`, `∃ε'`); `partialResume` →
  `stackWf_resume`; **handled-`partialPerformNil` → the ONE isolated obligation**
  (`HandledPerformPreserves`, threaded like `BuiltinAppPreserves` — the dispatch §5).

Only the handled-`perform` dispatch need be isolated; all else is mechanical. The
dry-run confirms the design is sound; the ~40-edit volume is the only obstacle.

## Concrete execution order
1. Helpers `handlerTy`/`kontTy`/`execTy` (abbrevs) in Typing/Runtime.
2. `HasType.handle` + `inv_handle` + `hasType_expr_form` arm + `rcases` bumps.
3. `HasTypeV.partialHandleNil`/`partialHandleOne`/`partialResume` + `conv` +
   `canonical_arrow`.
4. `StackWf.delimit` frame; decide row-change handling (recommend (a)).
5. `stackWf_move` (the `move`-append segment lemma) — pure list induction.
6. Generalize `stackWf_doPerformR_unhandled` → `stackWf_doPerformR_dispatch`
   (handled `.tau` vs unhandled escape), by induction on `StackWf` tracking `acc`.
7. `reduceDeep` preservation (push `Delimit`, run exec); `Delimit`-value pop
   preservation; the handled-`perform` preservation (handler call); `Resume`
   preservation (`move acc k`, feed reply). Re-green `preservation`/`progress`/
   `soundness_value`; keep `ReplyContract` (still only `runR` replies).
8. `#print axioms`; `lake exe spec` (dynamics unchanged ⇒ still 104/104); sanity
   `example` typing `handle("Abort") h (\_. perform "Abort" x) : … ! tail`.

## Risk
Highest of the project (continuation typing, no precedent). The fallback remains fork
(b) — a typed contextual semantics + a `Reduce`-simulates-it proof — if `Resume`'s
segment-transformer typing stalls. T5c already gives the full effect-safety result for
the *unhandled* fragment, so even partial `Handle` progress is a real strengthening.
