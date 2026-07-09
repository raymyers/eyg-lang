---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 6 "Session G3". Step 2 (the `genAtV_closure_ready_value_node`
  wrapper) LANDED + committed. Step 1 (frame-RT threading) precisely mapped to its true multi-file
  cascade, with the one non-mechanical linchpin isolated (`hasTypeRT_ctxConv`); deferred (no LSP,
  cannot be validated end-to-end while step 3 is unreachable). Step 3 (Soundness grind) confirmed
  not one-session-reachable blind: the working-tree B-engine is structurally mangled.
status: PARTIAL. One green additive commit (`cb598ce0`, `Substitution.lean`). Soundness.lean left
  exactly as found (pre-existing uncommitted mess, untouched — only Read).
kind: progress
component: lean (Eyg/Types/Substitution.lean)
---

# G1 Phase 6 (Session G3): wrapper landed (step 2); step-1 frame-RT cascade fully mapped

No LSP/MCP this session (canary failed: Read/Grep/Edit + `lake build`/`lake env lean` only).

## What landed (commit `cb598ce0`, per-file green, no `sorry`, no new axioms)

**Step 2 — `genAtV_closure_ready_value_node`** (`Substitution.lean`, additive after
`instantiateV_genAtV_tyEquiv`). From a lambda-**node** derivation
`h : HasType lvl Γ ⟨.Lambda x lbody, la⟩ defnTy ε` (the shape `inv_let`'s poly branch yields — NOT
the decomposed `lam` components) plus `NoGenAt lvl h`, `PolyAboveFV lvl Γ ⟨.Lambda x lbody, la⟩`,
`CtxWfV lvl Γ`, `EnvWf env Γ`, it produces the `EnvWf.cons`/`StackWfV`-Assign readiness
`∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = lvl) → HasTypeV (Value.Closure x lbody env)
((Scheme.genAtV lvl defnTy).instantiateV args)`. Composition:
`inv_lambda_noGenAt hng` → body derivation + its `NoGenAt` + `lvl ≤ lvl'` + `argTy` levels bound;
`genAtV_instantiate_lam_ready_le` (Session-G1 non-strict keystone; handles the `lvl' = lvl` case,
i.e. Session-F's `\x. perform "op" x` witness, via the `NoGenAt lvl` side condition — hence NoGenAt
is a genuine premise, not optional); `inv_lambda` on the result then `HasTypeV.closure`, converting
the reconstructed arrow back to `defnTy` under `instantiateV` via
`instantiateV_genAtV_tyEquiv lvl heq args`.

**Signature note (pinned against the A-engine call site, `Soundness.lean:243`).** The working-tree
call `genAtV_closure_ready_value_node hlvl0 hdefn hΓpa hcw henv args hargs` (ℓ = the ambient `lvl`,
generalization at exactly `lvl`) is from the *incomplete* partial migration: it does **not** pass a
`NoGenAt` argument. But `NoGenAt lvl` is genuinely required (the non-strict `lvl'=lvl` `perform`
branch cannot be discharged without it — HasType.lam only guarantees `lvl ≤ lvl'`, not strict). So
step 3 must additionally *supply* `NoGenAt lvl hdefn` at that call site. **Whether that `NoGenAt` is
dischargeable at runtime is the open question step 3 must answer** (see "step-1/3 entanglement"
below) — it is the gap-2 analog of gap-1's runtime-groundness `HasTypeRT`.

## Step 1 (frame-RT threading) — fully mapped, deliberately deferred

The design (from Session G2) is correct and I confirmed it is **dischargeable in Soundness**: at the
`.E` app case (`Soundness.lean:220`) `inv_app_rt hrt` yields `HasTypeRT` of both `hf` and `harg`; at
the `.E` let case `inv_let_rt hrt` yields `HasTypeRT hbody`. So the frame *can* be handed the RT
witness it must carry. But the frames that store terms-that-become-controls are `StackWf.assign`
(body) and `StackWf.arg` (arg), and threading `HasTypeRT` into them **cascades**:

1. **`Machine.lean`** — add `HasTypeRT` field to `StackWf.assign`/`.arg`; thread through the 6
   inversion lemmas (`stackWf_assign_inv`/`arg_inv` extract it, `conv` folds via `HasTypeRT.conv`),
   `stackSeg_toStackWf`, `stackWf_toStackWfV`/`_toStackWfE`, `stackWfE_lambda_step`,
   `stackWfE_value_step`; add the RT witness to the `StackWfV`/`StackWfE` **Assign** heads (the
   `StackWfV`/`StackWfE` **Arg** head is plain `StackWf.arg`, so its RT rides on the inductive
   field); fix the 2 sanity examples (supply the closure-arg RT). All **mechanical**.
2. **`Runtime.lean`** — the cascade forces `StackSegWf.assign`/`.arg` to carry `HasTypeRT` too
   (because `stackSeg_toStackWf` builds `StackWf.assign`/`.arg` from them, and RT of a general
   body/arg is *not* re-derivable). `StackSegWf` is in the **mutual block with `HasTypeV`**. Thread
   through `stackSeg_conv_output` (RT rides unchanged — easy) and `stackSeg_append` (easy). **The one
   non-mechanical piece:** `stackSeg_input_conv` (`Runtime.lean:355`) rebuilds the stored assign body
   via `hasType_ctxHead_conv hbody hσ` (the incoming-value type changed ⇒ the bound var's type in the
   body's context changes), so it needs **`HasTypeRT (hasType_ctxHead_conv hbody hσ)`** — a new
   companion lemma. `hasType_ctxHead_conv` bottoms out in `hasType_ctxConv` (`Typing.lean:985`), a
   full ~24-arm derivation-**rebuilding** induction. The RT companion `hasTypeRT_ctxConv` is
   therefore a 24-arm derivation-indexed induction that must construct *exactly* the `HasTypeRT`
   witness for each rebuilt arm (`var` case-splits on the looked-up binder; args are untouched so the
   RT args-bound is preserved, but the term must match). **This is the linchpin and the reason step 1
   was deferred** — it is derivation-indexed-induction proof engineering that genuinely needs live
   goal-state; blind it is high-risk, and the `.arg` case of `stackSeg_input_conv` (line 363, a plain
   `harg.conv`) threads via `HasTypeRT.conv` trivially by contrast.
3. **`Soundness.lean`** — supply RT at each `StackWf.arg`/`.assign`/`StackSegWf.*` construction (from
   `inv_app_rt`/`inv_let_rt`), part of step 3.

### Recommended next-session order (WITH LSP)
1. Land `hasTypeRT_ctxConv` (+ `hasTypeRT_ctxHead_conv` corollary) in `Typing.lean` — self-contained,
   additive, commit independently. This is the only *non-mechanical* piece of step 1.
2. Thread RT into `StackSegWf` (`Runtime.lean`) using it — commit per-file green.
3. Thread RT into `StackWf`/`StackWfV`/`StackWfE` (`Machine.lean`) — commit per-file green.
4. Only then the step-3 Soundness grind.

## Step 3 (Soundness grind) — confirmed NOT one-session-reachable blind

`lake build Eyg.Types.Soundness`: **103 errors** at HEAD (unchanged). The working-tree B-engine
(`reduceEvalR`/`soundness_evalR`, ~lines 2392–3237) is **structurally mangled** by the prior partial
migration — not "mechanical grind" residue: unknown identifiers `StackWfB` / `stackWfB_assign_inv`
(references to a renamed/removed predicate), a cascade of "Function expected at" (~lines 2490–2691,
a broken destructure), and **a pre-existing `sorry` at `Soundness.lean:2880`** (in the uncommitted
working tree — NOT committed anywhere; the committed HEAD has no `sorry`). Re-greening this needs the
B-engine's mangled section reconstructed *and* step 1 complete *and* the `NoGenAt`-at-call-site
question answered — multi-session, LSP-dependent.

## step-1/3 entanglement: the `NoGenAt`-at-runtime open question

The wrapper (step 2) needs `NoGenAt lvl hdefn` for the let_poly-bound lambda's defn derivation. At the
preservation call site this is a *runtime* fact (like gap-1's `HasTypeRT`): a let_poly-bound lambda
body typed at `lvl' ≥ lvl` contains a `let_poly` generalizing at *exactly* `lvl` only when `lvl' =
lvl` and it sits at the body's top. Whether that state is reachable/excludable at runtime — or must
be threaded as a `NoGenAt`-flavored `MStateWf` invariant analogous to `HasTypeRT` — is the sharpest
remaining design question. Flag for the next session: check whether `HasTypeRT` (already wired into
`MStateWf.E`) can be *strengthened* to also carry `NoGenAt` of the control, discharging both at once.

## Tree state at stop
- HEAD `cb598ce0` (this session's single commit, on top of `ac92be1f`). Per-file green:
  `Substitution` (and its deps `Typing`/`Scheme`/`Generation`/`Runtime`/`Machine`).
- Working tree: `Eyg/Types/Soundness.lean` modified (pre-existing Phase-6-arc uncommitted state,
  **untouched** this session — only Read), uncommitted. Untracked `.claude/`.
- `grep sorry Eyg/Types/*.lean` (committed HEAD): none. (The working-tree Soundness.lean has one
  pre-existing uncommitted `sorry` at :2880, from a prior session's partial migration — not
  introduced or touched here.) Whole-project `lake build` still fails only on `Soundness.lean`.
  Caveat 5 remains OPEN.
