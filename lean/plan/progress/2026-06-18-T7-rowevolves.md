---
date: 2026-06-18
milestone: T7 — discharge `TauKeepsRow` (the row-evolution effect-safety)
status: SCOPED — design settled + key facts verified; full discharge is a bottom-row-tracking slice
---

# Discharging `TauKeepsRow` → row-evolution effect safety (scoping)

`TauKeepsRow` ("a `.tau` keeps the ambient row `ε` exactly") is **false** once `Handle`/
`Delimit` lands and is the last gate (besides `Fix*`) on the row-dependent results
(`soundnessR_effect`, `ωTr_*`/`soundness_behaviorsR_diverges`, `mTr_*`/`_terminates_*`,
`soundness_behaviorsR_suspended`, `pure_*`, and `soundness`). The `ε`-free value/no-bad-crash
results don't use it. This note settles the design; the discharge itself is a contained but
non-trivial slice (akin to the `perform` dispatch — a new structural index + a preservation
re-thread).

## The true statement & why it holds

The row-dependent results all reduce to: **an escaping `perform op` has `op ∈ ε_init`** (the
program's *declared* row). Currently they fake this by keeping `ε = ε_init` exactly via
`hkeep`. The honest argument:

- At any reachable state the control runs at row `ε_cur` (the **top** row), and the stack
  `k` discharges down to the program's declared row `ε_init` at its base. Verified shape of
  the generalized `StackWf.delimit` (Machine.lean):
  - top (frame input) row = `effectExtend l lift reply tail` (where the delimited code runs);
  - `rest` (below) runs at some `εInner` with **`Ty.EffWeaken tail εInner`** (row subsumption);
  - every non-`delimit` frame keeps the row.
- A `perform op` **escapes** (reaches `reduce1Run = .perform`) iff `doPerformR` finds no
  matching `Delimit op` — i.e. `op` is none of the in-scope handled labels.
- **Single-delimit transfer (the inductive step, verified sound):** `op ∈ effectExtend l
  lift reply tail` with `op ≠ l` gives `op ∈ tail` (`EffContains.tail`); then `EffWeaken tail
  εInner` gives `op ∈ εInner` — the `tail ≈ εInner` disjunct transfers it; the `tail ≈ ∅`
  disjunct makes `op ∈ tail = ∅` impossible. So membership of an *unhandled* `op` transfers
  **down** across each delimit. Non-delimit frames keep the row. ⇒ `op ∈ ε_bot` (the base
  row), and `ε_bot = ε_init` is a run invariant (no reduction ever discharges the base).

## The obstacle (why it's not a quick edit)

To use "`op ∈ ε_bot` and `ε_bot = ε_init`" we must **track the bottom row**. But:
- `StackWf` is a `Prop`, so we **cannot** define `bottomRow : StackWf … → Ty` (no large
  elimination Prop→Ty).
- `StackWf`'s `ε` index is the **top** row only; the base row is implicit and *changes* at
  each `delimit` (to `εInner ⊇ tail`), so it isn't recoverable from `ε_cur` alone.

## Recommended design (settled)

Add the base row as an explicit index via a companion relation, then re-thread:

1. **`StackWfB k σ ε εbot τ`** — `StackWf` with a 5th index `εbot` (the base row). Mirror the
   7 constructors: `nil` sets `εbot := ε`; the six non-`delimit` frames pass `εbot` through;
   `delimit` recurses on `rest` at `(εInner, εbot)` (so `εbot` is the row at the very base).
   Plus `stackWfB_toStackWf` (forget `εbot`) and `stackWf_toStackWfB` (∃ εbot).
2. **`stackWfB_escape`** — by induction on `StackWfB`: if `op ∈ ε` and `op` is unhandled in
   `k` (no matching `Delimit op` — the hypothesis `doPerformR … = UnhandledEffect op` supplies
   this; thread it as "for every `Delimit l` frame, `l ≠ op`"), then `op ∈ εbot`. The delimit
   case is the single-delimit transfer above; non-delimit cases are immediate.
3. **`MStateWfB s τ ε εbot`** (or thread `StackWfB` inside a strengthened invariant) baking in
   the base row; `mStateWf_initial` gives `εbot = ε_init` (empty stack ⇒ `εbot = ε = ε_init`).
4. **Preservation of the base row.** The crux re-thread: show every `.tau`/`.perform`/`.reply`
   step keeps `εbot` (pushing/popping frames and `reduceDeep`/`Delimit`-pop all preserve the
   base — a `Delimit` push adds a frame whose `rest` is the old stack at the old top row, so
   the base is unchanged; a `Delimit`-pop removes the topmost handler, base unchanged). This
   mirrors the existing `preservation` case analysis with the extra `εbot` index carried
   through (the bulk of the work — comparable to one pass of the perform grind).
5. **Re-thread the consumers.** Replace `TauKeepsRow`/`hkeep` in `preservation_keep_fix`,
   `soundnessR_effect`, `ωTr_all_wf`, `mTr_terminal_wf` (and the wrappers) with the
   `StackWfB`/`εbot=ε_init` invariant; at the escape, `stackWfB_escape` reads `op ∈ ε_init`
   directly. Remove `TauKeepsRow` + `hkeep` params (like `HandlerObligations` was removed).

## Simpler interim option (if a full re-thread is too large for one pass)

`soundnessR_effect` is the keystone (the others route through it / share the pattern).
Discharging *just* it — by strengthening its fuel-induction invariant to carry `StackWfB …
ε_init` and using `stackWfB_escape` at the boundary — already makes effect-escape soundness
unconditional, and the `ωTr`/`mTr` variants follow the same template. Bank `StackWfB` +
`stackWfB_escape` first (self-contained, no preservation needed), then the preservation
re-thread, then the consumers — monotonic, like the perform grind (which converged
45→14→6→2→0 over passes once the route was fixed).

## Verified this pass
- Baseline green in the worktree (`lake build` 1764 jobs; `TauKeepsRow`/`Fix*` the only
  isolated hypotheses; `HandlerObligations` already removed).
- The `StackWf.delimit` shape (`EffWeaken tail εInner` below-row) and the single-delimit
  membership transfer (the inductive core of `stackWfB_escape`) are confirmed sound against
  the current definitions and the `EffContains`/`EffWeaken` API (`EffContains.tail` +
  `effWeaken` disjunction).

No code committed (the discharge is a multi-step slice; this note settles its design so the
next pass executes rather than re-discovers). `Fix*` remains orthogonal.
