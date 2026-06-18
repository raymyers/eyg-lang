---
date: 2026-06-17
milestone: T5 (Handle) — discharge `resume`/`perform`
status: SCOPED (compiler-grounded) — both remain isolated; resume wall pinned exactly, no code change
---

# `resume`/`perform` discharge attempt — outcome: precise wall, banked baseline green

Goal: discharge the remaining two `HandlerObligations` fields (`resume`, then `perform`).
Result: **both are genuine research-grade continuation-typing problems beyond a single
pass**; the `resume` wall is now **pinned by the compiler** (not just argued). No code
changed — the baseline (`lake build` 1779 jobs, `lake exe spec` 104/104) stays green.

## `resume` — the wall is the `EffWeaken` disjunct `εf ≈ ∅` (escaping pure-tail continuation)

`resume_preserves_exact` (banked) proves the `Resume` dispatch under `hexact : εf ≈ ε`.
The general field carries `hw : Ty.EffWeaken εf ε := TyEquiv εf ε ∨ TyEquiv εf .empty`.
From the resume's type `kontTy reply tail ret = reply →⟨tail⟩ ret`,
`tyEquiv_fun_components` gives `heff : tail ≈ εf`. The proof must convert the base stack
`hrest : StackWf rest retTy ε τ` to the segment's output endpoint `(ret, tail)` (so
`stackWf_resume` can compose `acc.reverse` onto it). That needs `TyEquiv ε tail`:

- **Disjunct 1** (`εf ≈ ε`): `heff.trans hexact : tail ≈ ε` ⇒ `StackWf.conv` works. ✔
- **Disjunct 2** (`εf ≈ ∅`): `heff.trans hempty : tail ≈ ∅`, giving only `TyEquiv ∅ tail`.
  `StackWf.conv` then demands `TyEquiv ε tail` but is handed `TyEquiv ∅ tail` — **compiler
  error** (`has type ∅.TyEquiv tail but expected ε.TyEquiv tail`, verified by inserting
  the general lemma and building `Eyg.Types.Soundness`). ✘

**Why disjunct 2 is sound-but-unprovable-as-structured, and reachable.** `εf ≈ ∅` means
the resume's tail (its post-continuation row) is empty — a **pure-tail continuation** —
*applied at a non-empty ambient `ε`*. That is exactly an **escaping continuation**: a
handler that returns its `resume` (`handle l (\x \k. k) exec`), later invoked in a more
effectful context. Discharging it requires **re-typing the captured segment `acc` upward
at the larger ambient `ε`** — NOT lowering `rest` from `ε` to `∅` (which is *unsound*: a
`StackWf` whose frames have non-pure latent cannot retype at `∅`; that is the very thing
the compiler error blocks, correctly).

**What it actually needs (next pass):** the **subrow segment composition** — generalize
`StackSegWf`'s frames (`arg`/`applyf`/`callwith`/`delimit`) to carry an `EffWeaken`
(mirroring the already-generalized `StackWf` frames), and a `stackSeg_toStackWf` variant
that re-types the segment at any ambient `⊇` its internal rows. Then a pure-tail (`∅`)
segment composes onto `rest` at `ε`. Note the **deep-handler subtlety**: `acc` for a deep
handler re-pushes the matching `Delimit`, so `acc.reverse` ends in a `delimit` frame; with
the *generalized* `StackWf.delimit` (already in, discharges from the ambient with
`tail ⊑ ε`) that frame is the natural row-bridge between the segment (run at `εtop`) and
`rest` (run at `ε`) — so `partialResume`'s stored output endpoint likely wants to be the
*ambient*, not a fixed `tail`, with the re-pushed `Delimit` carrying the `EffWeaken`. This
is the real continuation-typing design step; it is a dedicated slice (≈ the size of the
original `StackWf.conv`/inversion infra), not a wedge-in.

## `perform` — the stack-walk dispatch (design §5), independent, also dedicated

`doPerformR` walks `rest` to the nearest matching `Delimit l`, captures the walked prefix
as `acc`, builds `resume = Partial (Resume acc iEnv) []`, installs
`CallWith arg :: CallWith resume :: rest'` and runs the handler `h`. Typing the successor
needs: (1) a **`StackWf`-prefix → `StackSegWf`** conversion for the walked frames (induction
on the walk, past non-matching `Delimit l'`, `l' ≠ l`, with `EffContains` of the performed
`op` reflecting across each), to type the freshly-built `resume` via `partialResume`; and
(2) the handler call `h arg resume : ret`. Step (1) is the substance of handler soundness
and shares the generalized-`StackSegWf` machinery `resume` needs, so the two are best done
together. Unlike `resume`, the perform step builds the resume as a *value* (not applied),
so it does not itself hit the disjunct-2 wall — but it does need the `StackWf→StackSegWf`
walk lemma.

## Recommendation for the next pass
Do the **generalized `StackSegWf` (EffWeaken-carrying frames) + subrow `stackSeg_toStackWf`**
first (the shared foundation), then discharge `resume` (disjunct 2 via the re-typed
segment) and `perform` (the walk → `StackSegWf` lemma) together. Budget it as a dedicated
slice comparable to the `StackWf.conv` infra. The `ε`-free value/no-bad-crash soundness is
unaffected throughout (it never inspects these fields' rows). `TauKeepsRow` is the separate
T7 follow-up (unblocked on the `Delimit` side).

## Verification
No `Eyg/` code changed (a probe lemma was inserted to pin the wall, then reverted).
Baseline `lake build` green (1779 jobs); `HandlerObligations` unchanged at `{perform, resume}`.
