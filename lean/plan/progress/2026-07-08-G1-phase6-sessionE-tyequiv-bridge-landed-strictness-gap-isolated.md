---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 6 "Session E". The TyEquiv-bridge deliverable
  (`instantiateV_genAtV_tyEquiv`, Session D's designed additive lemma) is IMPLEMENTED and
  builds clean per-file — one green additive commit to `Substitution.lean`. The
  `genAtV_closure_ready_value_node` wrapper's residual strictness subtlety is now precisely
  isolated as genuinely undischargeable from `inv_lambda` alone (not merely "small design"):
  it is entangled with the runtime-groundness invariant / a levels-bound metatheorem. Full
  green NOT reached; `HasTypeRT` (step 2) not attempted (see "Why not further" below).
status: LANDED (one commit — the bridge lemma). Working tree: `Soundness.lean` still
  uncommitted (as-found Session-D partial migration, unchanged this session). Every other file
  green per-file.
kind: progress
component: lean (Types.Substitution — landed; Types.Soundness — untouched analysis)
---

# G1 Phase 6 (Session E): TyEquiv bridge landed; wrapper strictness gap precisely isolated

No LSP/MCP tools were available this session (script fallback only: Read/Grep + `lake env lean`).
Per the plan's guidance, this constrained the session to the one self-contained additive piece that
compiles in isolation, plus a sharpened characterization of the two blockers.

## Landed: `instantiateV_genAtV_tyEquiv` (Substitution.lean) — the TyEquiv bridge

Session D designed this lemma (its statement + proof sketch); this session implemented it and
verified it builds clean per-file (`lake env lean Eyg/Types/Substitution.lean`, zero errors):

```
theorem instantiateV_genAtV_tyEquiv (ℓ : Nat) {d₁ d₂ : Ty} (h : Ty.TyEquiv d₁ d₂) (args : List Ty) :
    Ty.TyEquiv ((Scheme.genAtV ℓ d₁).instantiateV args) ((Scheme.genAtV ℓ d₂).instantiateV args)
```

Proof exactly as designed: a helper `hlen d : ((levels d).filter (·=ℓ)).length = 0 ↔ ℓ ∉ levels d`
(via `List.length_eq_zero_iff` + `List.eq_nil_iff_forall_not_mem` + `List.mem_filter`), then
`Ty.levels_tyEquiv` makes the `arity = 0` branch selection agree across the `TyEquiv`, and the two
branches close by `h` (arity-0) / `Ty.substAt_tyEquiv ℓ σ h` (else, same `σ` since both schemes have
`level = ℓ`). Purely additive, axiom-clean.

This is the validated math the Session-D note called "the TyEquiv bridge SOLVED" — now a real,
compiling lemma the wrapper (and any future re-typing under `instantiateV`) consumes.

## Isolated (not landed): the `genAtV_closure_ready_value_node` wrapper strictness gap

The wrapper's intended body: `by_cases` on `(genAtV lvl defnTy).arity = 0`:
- **arity = 0** — `instantiateV args = defnTy`; discharge via `closure_typed_of_lambda henv hdefn`.
  **No strictness needed.** This half is clean.
- **arity ≠ 0** — `lvl ∈ defnTy.levels`; apply the existing `genAtV_closure_ready_value` and
  convert its conclusion with `instantiateV_genAtV_tyEquiv lvl heq args`. This needs
  `genAtV_closure_ready_value`'s `hlt : lvl < lvl'` (**strict**), but `inv_lambda hdefn` yields only
  `hle : lvl ≤ lvl'`.

**The gap is genuinely undischargeable from `inv_lambda` alone — sharper than Session D framed it.**
`arity ≠ 0` gives `lvl ∈ defnTy.levels`, hence (via `heq : TyEquiv (.fun argTy εb retTy) defnTy` +
`levels_tyEquiv`) `lvl ∈ (argTy.levels ++ εb.levels ++ retTy.levels)`. Session D's option (a)
(arity-0 short-circuit) is confirmed clean. Option (b) ("`lvl ∈ defnTy.levels ⇒ lvl < lvl'`") splits:
- if `lvl ∈ argTy.levels`: `hfv` gives `lvl < lvl'` directly. ✓
- if `lvl ∈ εb.levels ∪ retTy.levels` **and** `lvl ∉ argTy.levels` (possible with `lvl' = lvl`):
  **no bound is available.** `inv_lambda`/`HasType.lam` record `∀ l ∈ argTy.levels, l < lvl'` only —
  nothing bounds the *result*/*effect* row levels. So strictness genuinely fails here.

This is not "small proof design"; it needs one of:
1. a **levels-bound metatheorem** `HasType lvl' Γ e τ ε → CtxWfV lvl' Γ → ∀ l ∈ τ.levels ∪ ε.levels,
   l < lvl'` (a full ~24-case induction over `HasType`), or
2. strengthening `HasType.lam` (a **statement/rule change**, header-fence — would force re-proving
   every `lam`-introduction incl. `Typing.lean`'s `section Examples`), or
3. the **runtime-groundness invariant itself**: `hasType_subst` needs `ℓ < lvl'` precisely because
   substituting at `ℓ` in a body typed *at* `ℓ` would touch the body's own quantified region — i.e.
   the `lvl' = lvl ∧ lvl ∈ retTy.levels` case is exactly a state that must be excluded by the runtime
   invariant, not by `inv_lambda`. So the wrapper's strictness and the var-preservation groundness
   blocker are **the same obstruction**, and both are resolved together by Session D's `HasTypeRT`
   design — the wrapper is not independently closable.

Recommendation for Session F: land the wrapper as part of introducing `HasTypeRT` (step 2), not
before — its arity≠0 branch's `hlt` should come from the runtime-restricted derivation, not
`inv_lambda`.

## Why not further this session (`HasTypeRT` / the ~90-error grind)

- `HasTypeRT` (step 2, option 1) is a 24-constructor mirror of `HasType` plus a full RT-inversion
  set, and its value only materializes once wired into `MStateWf`/`StackWfE`/`StackWfV`
  (`Machine.lean`) — which requires the whole Soundness re-green. Landing it as a *standalone*
  additive prototype (the way `HasTypeAt`/`HasTypeAtV`/`HasTypeVAt` were landed in Phase 3b) is
  possible but is ~a full session of careful hand-transcription of 24 constructors + inductive
  inversion proofs, which without LSP goal-state is high-risk for silent shape mismatch against what
  the wiring will actually need. Deferred rather than land a speculative, possibly-wrong-shaped mirror.
- The ~90-error two-engine `Soundness.lean` grind was explicitly flagged (every prior session) as
  needing live goal-state; batch `lake env lean` iteration on a 4278-line file is impractical, and
  every fix depends on `HasTypeRT` being wired first anyway.
- Touching `Soundness.lean` further (which is already red at HEAD and in the working tree) risks the
  "work evaporates uncommitted" failure mode; it was left exactly as-found.

## Tree state at stop
- Committed: `Substitution.lean` (the bridge lemma) + this note + plan Phase-6 update.
- Working tree: `Eyg/Types/Soundness.lean` modified (as-found Session-D partial migration, unchanged),
  uncommitted. `lake env lean Eyg/Types/Soundness.lean`: 103 errors (unchanged two-engine map from
  Session D). Note: the *committed* `Soundness.lean` at HEAD is itself already red (101 errors) — the
  tree has been red across the whole Phase-6 arc; committing the additive `Substitution.lean` bridge
  introduces no new breakage.
- Every other per-file target green; `grep sorry Eyg/Types/*.lean`: none.
- No axioms added, no `sorry`, no statement weakened. Caveat 5 remains OPEN.

## Recommended Session F order (needs LSP)
1. Introduce `HasTypeRT` (Session D's option 1) + RT-inversion lemmas, and land the
   `genAtV_closure_ready_value_node` wrapper with its arity≠0 `hlt` supplied by the runtime-restricted
   derivation (resolving both the var-preservation groundness blocker AND the wrapper strictness gap
   together — they are the same obstruction, per this session's analysis).
2. Wire `HasTypeRT` into `MStateWf`/`StackWfE`/`StackWfV` (`Machine.lean`); establish the top-level
   `Γ = []` ground base case + the keystone-produces-ground-args preservation step.
3. Grind the ~90 mechanical two-engine `Soundness.lean` errors; migrate the B-engine's residual
   `sc.instantiate` sites (130/1908/2700-2711/3775 — re-grep, lines drift).
4. Set `soundness`/`soundness_evalR` ambient level ≥ 1 (so `lvl ≠ 0` is available at the let_poly
   preservation site — also the `hlvl0` the wrapper call at Soundness:243 needs).
5. Phase 7 (sanity example + `type-soundness-report.md` Caveat 5).
