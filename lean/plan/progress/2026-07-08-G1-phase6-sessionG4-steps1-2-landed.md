---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 6 "Session G4". Steps 1 (hasTypeRT_ctxConv linchpin) and 2
  (frame-RT threading through StackSegWf/StackWf) BOTH LANDED + committed per-file green. Step 3
  (Soundness grind) assessed and the gap-2 NoGenAt/PolyAboveFV/lvl≠0 provenance precisely pinned;
  full green not reachable blind this session.
status: PARTIAL. Two green additive commits (4d232f7b Typing.lean; c223c4c1 Runtime.lean+Machine.lean).
  Soundness.lean left exactly as found (uncommitted partial migration, untouched — only Read).
kind: progress
component: lean (Eyg/Types/{Typing,Runtime,Machine}.lean)
---

# G1 Phase 6 (Session G4): steps 1 + 2 landed; step 3 gap-2 provenance pinned

No LSP/MCP this session (canary failed: Read/Grep/Edit + `lake build` only).

## Landed + committed

### Commit `4d232f7b` — step 1: `hasTypeRT_ctxConv` (+ `hasTypeRT_ctxHead_conv`) in `Typing.lean`
The RT-indexed companion to `hasType_ctxConv` — the one non-mechanical linchpin Session G3 isolated.
Key design decision: it is **NOT** stated as `HasTypeRT (hasType_ctxConv h …)`, because `HasTypeRT`
is indexed by the *specific* derivation and `hasType_ctxConv`'s output is an opaque `HasType.rec`
application whose `var` arm case-splits on the runtime `Δ.lookup y` (so it will not reduce/match a
target RT constructor). Instead it is **bundled**:
```
hasTypeRT_ctxConv (hrt : HasTypeRT h) :
  ∀ Δ Γ x σ σ', Γ₀ = Δ ++ (x,.mono σ)::Γ → TyEquiv σ' σ →
    ∃ h' : HasType lvl (Δ ++ (x,.mono σ')::Γ) e τ ε, HasTypeRT h'
```
Proved by `induction hrt` (21 arms), rebuilding a fresh converted derivation + its RT arm-for-arm.
`stackSeg_input_conv` destructures both. Subtleties: the leaf arms and `lam`/`let_poly`-defn subterms
reuse the *plain* `hasType_ctxConv` (their RT is not needed by `HasTypeRT.lam`/`.let_poly`); the
`var` conv-subcase (`y == x`, binder-type swapped) transports the args-level side-condition verbatim
because `(Scheme.mono σ).level = (Scheme.mono σ').level = 0` (mono = ⟨0,0,_⟩); several constructors
needed their implicit HasType fields supplied explicitly (`hbody`/`hw`/`hdefn`/`hcw`) so the ∃-witness
and its RT proof unify.

### Commit `c223c4c1` — step 2: frame-RT threading (`Runtime.lean` + `Machine.lean`)
Added a `HasTypeRT hbody` / `HasTypeRT harg` field to the `assign`/`arg` constructors of **both**
`StackSegWf` (Runtime, in the `HasTypeV` mutual block) and `StackWf` (Machine). The HasType field was
named so the RT field can index it. Threaded through every consumer:
- Runtime: `stackSeg_conv_output`, `stackSeg_input_conv` (assign via `hasTypeRT_ctxHead_conv`; arg via
  `HasTypeRT.conv`), `stackSeg_append`.
- Machine: `stackSeg_toStackWf`, `stackWf_assign_inv`/`_arg_inv` (now surface the RT existentially,
  `∃ hbody, HasTypeRT hbody ∧ StackWf …`), the `StackWfV`/`StackWfE` Assign heads, and
  `stackWf_toStackWfV`/`_toStackWfE`, `stackWfE_toStackWf`/`_lambda_step`/`_value_step`.
`MStateWf.E` already carried `HasTypeRT` (Session G2). All of Typing/Runtime/Machine/Substitution/
Scheme/Generation/Generalization build per-file green; no `sorry`; axioms unchanged.

## Working-tree Soundness.lean — re-characterized (corrects Session G3's note)
Session G3 called the B-engine "structurally mangled" with an "unknown `StackWfB`" and a "pre-existing
uncommitted `sorry` at :2880". **Both are inaccurate against the current working tree:**
- `StackWfB` **IS defined** (`Soundness.lean:2443`, the T7 row-evolution groundwork) — not unknown.
- `grep sorry Eyg/Types/Soundness.lean` is **empty** — there is no `sorry` anywhere.
- `git diff` of Soundness.lean is only **53 lines** (27 ins / 26 del) — a *legit, incomplete*
  level-tag migration of the A-engine (`mStateWf_E`/`weakenEff`/`preservation_E`), not mangled residue.
- `lake build Eyg.Types.Soundness`: **103 errors**, starting at `:34` (`mStateWf_E` still returns the
  old `HasType Γ …`/no-RT shape, out of sync with the RT-carrying `MStateWf.E`).

## Step 3/4 remaining + gap-2 provenance (the sharp blocker), precisely pinned
The Soundness grind is (a) migrate every use site to level-tagged `HasType lvl` + destructure the new
`hrt` from `mStateWf_E`, (b) supply RT to each `StackWf.arg`/`.assign`/`StackWfE`-head construction
(from `inv_app_rt`/`inv_let_rt`), (c) re-prove the two `let_poly` cases via
`genAtV_closure_ready_value_node`. Blocker (c) needs three facts the runtime site lacks:
1. `hℓ : lvl ≠ 0` — **solvable:** run `soundness`/`soundness_evalR` at a fixed ambient `lvl ≥ 1`,
   threaded through `MStateWf` (the plan already flags "set ambient level nonzero if needed").
2. `hΓpa : PolyAboveFV lvl Γ ⟨.Lambda lx lbody, la⟩` — candidate: derive from `CtxWfV`/`PolyAbove`
   (see `polyAboveFV_of_polyAbove`, `Typing.lean:304`), else thread as an `MStateWf` invariant.
3. `hng : NoGenAt lvl hdefn` — **the gap-2 linchpin**, the analog of gap-1's `HasTypeRT`. A let_poly-
   bound lambda whose defn derivation generalizes again at *exactly* `lvl` cannot be discharged from
   HasType alone. Most promising: make it an `MStateWf.E` invariant — either a standalone `NoGenAt`
   witness on the control, or **strengthen the already-wired `HasTypeRT` control witness to also carry
   `NoGenAt`** (discharging gaps 1 and 2 together). This is a genuine multi-session design task.

## Recommended next-session order (WITH LSP ideally)
1. Resolve gap-2 design: decide whether to extend `HasTypeRT` to carry `NoGenAt` (re-touches steps 1-2
   arms) or add a separate `MStateWf.E` `NoGenAt` invariant. Prototype the let_poly discharge first.
2. Fix `mStateWf_E` to surface `hrt`; migrate `preservation_E` `.E` app/let cases (inv_app_rt/inv_let_rt
   + RT into StackWf.arg / StackWfE assign head), set ambient `lvl ≥ 1`.
3. Grind the rest of the A-engine, then the B-engine (mirror), to green. Only commit Soundness.lean
   fully green (no red-commit exception).

## Tree state at stop
- HEAD `c223c4c1` (two commits above `e5338a2a`). Per-file green: Typing, Runtime, Machine, Substitution,
  Scheme, Generation, Generalization.
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6 partial migration, **untouched**
  this session — only Read), uncommitted. Untracked `.claude/`, and this note + plan update.
- `grep sorry Eyg/Types/*.lean`: none (committed HEAD *and* working tree). Whole-project `lake build`
  still fails only on `Soundness.lean`. Caveat 5 remains OPEN.
