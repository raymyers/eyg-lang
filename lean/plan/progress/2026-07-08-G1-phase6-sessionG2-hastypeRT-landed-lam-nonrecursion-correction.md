---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 6 "Session G2". Gap 1 (var-preservation runtime groundness) is
  DESIGNED and LANDED: the runtime-restricted judgment `HasTypeRT` + its var-preservation discharge
  lemma `inv_var_rt` + supporting RT-inversions, wired into `MStateWf.E`. A design correction over
  Session D's sketch (the `lam` arm must NOT recurse into the body) was found and validated. Frame-RT
  threading + the Soundness grind remain for the next (LSP) session.
status: LANDED, per-file green, three additive commits (`379c4d62`, `020e28ff`, `4d5fe793`). Gap 1's
  judgment + discharge lemma + MStateWf.E wiring done. Soundness.lean left exactly as found
  (pre-existing uncommitted mess, untouched).
kind: progress
component: lean (Eyg/Types/Typing.lean, Eyg/Types/Machine.lean)
---

# G1 Phase 6 (Session G2): `HasTypeRT` landed; the `lam`-non-recursion design correction

No LSP/MCP tools this session (canary failed: only Read/Grep/Edit + `lake build`/`lake env lean`).
Despite the no-LSP constraint that redirected several prior sessions away from `HasTypeRT`, this
session landed it — because the derivation-indexed formulation (à la the previously-landed `NoGenAt`)
turned out to be tractable with batch builds, and the interesting content localizes to a handful of
lemmas rather than a 24-constructor mirror + full RT plumbing.

## What landed (three commits, all per-file green, axioms `[propext]`, no `sorry`)

### Commit 1 (`379c4d62`) — `HasTypeRT` + the discharge lemma (`Typing.lean`)

`HasTypeRT (h : HasType lvl Γ e τ ε) : Prop`, an inductive predicate **indexed by the derivation**
(exactly the `NoGenAt` shape — reuses all `HasType` machinery instead of re-deriving typing at RT
level). Its `var`/`builtin` arms additionally carry the args side-condition
`∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level`. `inv_var_rt` extracts it: from a `HasTypeRT`
control derivation on a bare `⟨.Variable x⟩` node it returns exactly `inv_var`'s `(s, args, lookup,
TyEquiv)` **plus** the args bound — the single fact gap 1 was missing, letting the var-preservation
site apply `envwf_lookup`'s conditional readiness `hvty args` directly. `inv_builtin_rt` is the
builtin analog.

**The design correction (found + validated while building).** Session D's sketch said "every arm
other than `var`/`builtin` is a verbatim structural copy of `HasType`." That is **wrong for the `lam`
arm** (and `let_poly`'s lambda-defn): they must **not** recurse into the lambda body. Reason, checked
against the existing green `Typing.lean` examples:

- `hbody_ref` (a legitimate static derivation) types `\w. a w`'s body with the referenced `a`
  instantiated at the **non-ground** arg `[.var 2 0]` (level 2 ≠ `a.level` = 1). The whole referencing
  program `let a = \x.x in (let c = \w. a w in c)` type-checks at `HasType 1 []`.
- A lambda body is never evaluated *as a control* until its closure is **applied**, at which point the
  keystone (`genAtV_instantiate_lam_ready`/`..._le`) re-types it via `substAt` with **ground** args.
  So the buried non-ground var arg is never a runtime control's own instantiation.
- Therefore, had `lam`/`let_poly` recursed into the body, that whole legitimate program would fail to
  be `HasTypeRT` — contradicting "running controls are `HasTypeRT`". By **stopping at lambda bodies**,
  `HasTypeRT` (a) admits the program and (b) still forces every var node *actually reachable as a
  control* (never under an un-applied lambda) to carry the args bound. `app`/`let_` recurse (both
  sub-terms become controls); `conv` recurses; literals/atomics are leaves.

Validated **non-vacuously**: `HasTypeRT` of a lambda whose body is exactly `hbody_ref` holds via
`HasTypeRT.lam` — which takes **no** premise on `hbody` (the `@`-fully-applied form; term-mode
`HasTypeRT.lam _ _` runs into an elaboration-ordering quirk, see "friction" below).

### Commit 2 (`020e28ff`) — RT-inversions for preservation (`Typing.lean`)

- `hasTypeRT_lambda`: **any** lambda-node derivation is `HasTypeRT` (peels `conv` down to `lam`).
  Used to re-establish RT of a lam-control / `let_poly`-defn control freshly.
- `inv_app_rt`: RT analog of `inv_app` — returns the conv-adjusted `hf`/`harg` **with** their RT
  witnesses (function becomes the control, arg is stored in the `Arg` frame — both need RT).
- `inv_let_rt`: RT analog of `inv_let` — mono branch gives RT of both `defn` and `body`; poly branch
  gives RT of `body` only (the lambda-`defn` control's RT is rebuilt via `hasTypeRT_lambda`).

### Commit 3 (`4d5fe793`) — wire into `MStateWf.E` (`Machine.lean`)

`MStateWf`'s `.run (.E e, env, k)` case now carries `∃ hty : HasType lvl Γ e τin ε, HasTypeRT hty ∧
StackWfE …`. `mStateWf_initial` gains a `HasTypeRT h` premise. Blast radius **within Machine.lean is
exactly** `mStateWf_initial` + the one sanity example (every `MStateWf.E` destructor lives in
`Soundness.lean`), so this is cleanly additive and per-file green.

## The genuine finding: "runtime args are always ground" is a THREADED property, not universal

Session D flagged (correctly) "verify this claim carefully — trace how `EnvWf`/`StackWf` produce their
args, don't just assume." Doing so this session:

- **The initial program is NOT universally `HasTypeRT`.** An open-result program such as
  `let id = \x.x in id id` types with `f : ?a → ?a` where `?a` is a non-ground `.var lvl i`; its
  top-level `id` var nodes then carry non-ground args, so its control derivation is legitimately
  **not** RT. This is why `mStateWf_initial` takes a `HasTypeRT h` **premise** rather than proving RT
  from `HasType` — the invariant is an *entry-point hypothesis*, discharged by the soundness statement
  for the programs it actually runs (closed, ground result type — e.g. `let id = \x.x in id 5`, whose
  top-level `id` instantiates at the ground `[integer]`, **is** RT). This refines Session D's
  hypothesis: the invariant holds, but as a runtime property established at init **for ground-typed
  closed programs** and preserved forward, not as a theorem about arbitrary well-typed terms.
- **Preservation must re-establish RT at each step.** When a closure is applied its body becomes a
  control; its RT comes from the keystone's `substAt`-grounding (ground args ⇒ RT var nodes). When an
  `Arg`/`Assign` frame pops, the stored expression becomes a control and needs RT — which must be
  **carried in the frame**. Hence the next piece (below).

## Still open for the next (LSP) session

1. **StackWf / StackWfE / StackWfV frame-RT threading.** `Arg`/`Assign` frames store expressions that
   later become controls; for preservation to re-establish `MStateWf.E`'s RT across a frame pop, those
   frames must carry `HasTypeRT` of their stored derivation. This is a pervasive but mechanical change
   to `StackWf`(`.arg`/`.assign`) + `StackWfE`/`StackWfV` + their inversions/constructors + the
   refinement lemmas (`stackWf_toStackWfV`/`_toStackWfE`, `stackSeg_toStackWf`, …). It is **entangled
   with the Soundness preservation proof** (whose app/let cases construct these frames and would supply
   the RT), so it is best done **with** that proof, in live goal-state — deliberately deferred rather
   than landed blind.
2. **Wire `genAtV_closure_ready_value_node`** (`Substitution.lean`, still untouched) to call the
   Session-G1 keystone `genAtV_instantiate_lam_ready_le` + `inv_lambda_noGenAt` (gap 2's loose end).
3. **The ~90-error two-engine `Soundness.lean` grind.** Var-preservation now discharges via
   `inv_var_rt` (both engines: A ~215-219, B ~2942-2945); `inv_app_rt`/`inv_let_rt`/`hasTypeRT_lambda`
   are ready for the app/let preservation cases; migrate the B-engine residual `sc.instantiate` sites.
4. `soundness`/`soundness_evalR` ambient level ≥ 1; then Phase 7 (sanity example + Caveat 5 report).

## Elaboration friction (recorded for reuse)

Constructing a value of a **derivation-indexed** inductive (`HasTypeRT`) via its constructors against a
concrete goal repeatedly hit "don't know how to synthesize implicit argument" — `exact`/`refine`
/`apply HasTypeRT.app`/`.lam`/`.let_poly` do **not** reliably unify the constructor's `HasType …`
index with a concrete goal index. Two robust workarounds used:
- **`@`-fully-applied** constructor with all implicits (proof-irrelevance handles duplicated `hle`/
  `hfv`/`hw` proofs) — used for the `hbody_ref`-lambda validation.
- **Feed sub-proofs of concrete type** so their types pin the implicits: `HasTypeRT.app (hw := …)
  (hasTypeRT_lambda hlam) HasTypeRT.int` with `hlam` a named `have` — used for the `MStateWf.E` sanity
  example.
*Elimination* (`induction hrt` / `cases`) works fine, so all the `inv_*_rt` lemmas were straightforward.

## Tree state at stop
- HEAD `4d5fe793`. Three commits this session (`379c4d62`, `020e28ff`, `4d5fe793`), each per-file
  green, axioms `[propext]`, no `sorry`, no new custom axioms, no rule/statement change.
- Working tree: `Eyg/Types/Soundness.lean` modified (the pre-existing Phase-6-arc uncommitted state,
  **untouched** this session — only Read), uncommitted. Untracked `.claude/`.
- `grep sorry Eyg/Types/*.lean`: none (only prose "admit"/"admits"). Per-file green on every touched
  file and their dependencies; whole-project `lake build` still fails **only** on `Soundness.lean`.
  Caveat 5 remains OPEN.
