---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G28". Execution attempt on the G27 applyf-frame threading.
  No code landed (correctly). Two concrete results: (1) a MACHINE-CHECKED refutation of the natural
  `closureReady` match-def carrier for (C1)-(C3) (Prop proof-irrelevance / large-elimination blocks
  `cases hf` from reducing it), and (2) identification of a source-of-readiness gap the G27 design
  glossed — (C3) `RTSubstReady lvl' hbody` is not available at the Arg->applyf creation site and must be
  threaded forward from the Apply node's function-RT onto the persistent `StackWf.arg` frame.
status: PARTIAL (design advance via refutation; no commit). Soundness.lean byte-identical to G26
  (backed up to /tmp/Soundness.G26.backup.lean, `diff`-verified IDENTICAL; A-engine red at exactly the
  2 closure-apply RT sites 874-877 / 1036-1039; B-engine un-migrated past 2460). No `sorry` anywhere.
  HEAD `0c0b6951`. Caveat 5 OPEN.
kind: progress
component: lean
---

# G1 Phase 6 (Session G28): the `closureReady` carrier is refuted by proof-irrelevance; the (C3) source is the real open gap

No LSP/MCP (canary failed). Read/Grep + `lake env lean`. HEAD `0c0b6951`. NO source edits — the G26
near-green working tree is preserved byte-identical (backup `/tmp/Soundness.G26.backup.lean`, `diff -q`
IDENTICAL). `grep -rn sorry Eyg/Types/*.lean` empty.

## Confirmed error state (unchanged from G26/G27)

`lake env lean -DmaxErrors=40 Soundness.lean`: A-engine errors ONLY at 874-877 and 1036-1039 (the two
closure-apply RT sites: `cases hf with | closure henvc hbody heqc` binds 3 of the migrated 5 fields
`hlvl henv hfv hbody heq`; the `.E` `refine` misses the `HasTypeRT hty` slot), plus the deliberately
un-migrated B-engine (2460 `HasType` arg mismatch, 2501/2573 `StackWfB` unknown). No regressions.

## Task: execute G27's applyf-frame threading. What I actually found.

G27 concluded (C1) `CtxWfV lvl' Γ`, (C2) `retTy'`/`εb'` levels `< lvl'`, (C3) `RTSubstReady lvl' hbody`
must ride the `applyf` frame (not `HasTypeV.closure`), consumed at the apply site by `cases hf` + one
`hasTypeRT_subst` grounding at `lvl'`. Executing this needs a CARRIER: a Prop, threaded on the frame,
that `cases hf` turns into "(C1)∧(C2)∧(C3) about *this* closure's `lvl'`/`hbody`". The obvious carrier is
a match-def over the closure derivation.

### RESULT 1 — the `closureReady` match-def carrier is REFUTED (machine-checked in scratch)

Compiles as a definition:
```lean
def HasTypeV.closureReady {f : Value m} {argTy εf retTy : Ty}
    (hf : HasTypeV f (.fun argTy εf retTy)) : Prop :=
  match hf with
  | .closure (lvl' := lvl') (Γ := Γ) (retTy := retTy') (εb := εb') _ _ _ hbody _ =>
      CtxWfV lvl' Γ ∧ (∀ l ∈ retTy'.levels, l < lvl') ∧
        (∀ l ∈ εb'.levels, l < lvl') ∧ RTSubstReady lvl' hbody
  | _ => True
```
Consuming it fails:
```lean
example (hf : HasTypeV f (.fun argTy εf retTy)) (hcr : hf.closureReady) : True := by
  cases hf with
  | closure hlvl henv hfv hbody heq => simp only [HasTypeV.closureReady] at hcr; ...
```
=> `Tactic `cases` failed: recursor `HasTypeV.casesOn` can only eliminate into `Prop``, motive into
`Sort ?u`. `HasTypeV : Prop`, so its eliminator only large-eliminates into `Prop`; `cases hf` must revert
the hf-dependent `hcr : closureReady hf`, and generalizing a `match`-on-`hf` hypothesis forces a
`Sort`-polymorphic motive the eliminator cannot inhabit. Proof-irrelevance blocks recovering the closure
existentials (`lvl'`, `hbody`) from the proof term `hf` in a `cases`-alignable form. **Conclusion:
(C1)-(C3) cannot be carried as a match-def over the closure derivation and destructured by `cases hf`.**
(This is why G27's "pull (C1)-(C3) at the apply site" step had no concrete carrier — the natural one does
not exist.)

Corollary on the alternatives:
- Extra FIELDS on `HasTypeV.closure`: already refuted by G27 (breaks the non-ground `EnvWf.cons` clause).
- A SEPARATE readiness inductive indexed by value+arrow (not the proof), inverted at the apply site: its
  closure decomposition yields fresh `lvl'_2`/`hbody_2`, but (C3) is needed about `cases hf`'s `hbody_1`;
  `hbody_1 = hbody_2` only by proof-irrelevance IF both share `lvl'`/`Γ`/`retTy'`/`εb'`, which the value
  `.Closure x body cenv` does not pin. Alignment is not free.
- The workable carrier is a two-constructor frame inductive REPLACING `applyf`'s `HasTypeV f arr` premise
  (`closureApplied` carrying `x body cenv`, the decomposition, AND (C1)-(C3) as real fields; `partialApplied`
  carrying `HasTypeV f arr` + a not-a-closure witness). `cases` on THAT exposes aligned fields directly —
  but relocates the difficulty to the construction site (below).

### RESULT 2 — the real open gap: the (C3) SOURCE at the Arg->applyf creation site

Whatever the carrier, (C3) `RTSubstReady lvl' hbody` must be SUPPLIED where the `applyf` frame is created:
Soundness 862, Arg-frame case of `preservation_V`:
```lean
| Arg arg fenv =>
    obtain ⟨Γ, argTy, εf, retTy, ε0, lvl, hlvl, hσ, hε, henvc, harg, hrt, hw, hrest⟩ := stackWf_arg_inv hst
    ... exact ⟨…, StackWf.applyf (hv.conv hσ) hw hrest⟩
```
In scope: the function VALUE `hv : HasTypeV v (.fun argTy εf retTy)` and the ARGUMENT's `harg`/`hrt`
(`HasTypeRT harg`). NOT the function's RT: the Apply node's `rf : HasTypeRT hf` (`inv_app_rt`, Soundness
224) was consumed while `f` evaluated to value `v`, and `HasTypeV` carries no RT companion. So (C3) about
the closure `v` is genuinely unavailable at 862.

The two closure-creation paths:
- **variable-lookup path** (closure fetched from `env`): G27's step-1 `EnvWf.cons` ground-args-only
  readiness clause can produce a ready closure — addressable as G27 sketched.
- **direct-lambda-in-function-position path** (`(\w. body) arg`, `f` a literal lambda): closure built by
  `closure_typed_of_lambda` / `preservation_E` Lambda case (211-215) from the lambda node's `hbody` (via
  `inv_lambda`), whose only RT witness is the body-premise-free `HasTypeRT.lam` — strengthening which G27
  already proved unsound. So (C3) is NOT recoverable for this path from anything currently threaded.

Implied fix (larger than G27's "3 fields on applyf"): the persistent `StackWf.arg` frame must carry a
FORWARD readiness obligation about its eventual function value — the analogue of how `StackWfE`'s `Assign`
frame carries "future closure's readiness when `e` is a lambda" (Machine.lean 281-283), but for the arg
frame's function slot — discharged from the Apply node's `rf` at frame-creation and consumed when `f`
reduces to the closure value. Touches `StackWf.arg`/`StackSegWf.arg` (Runtime+Machine) + the value-state
machinery (`StackWfV`/`StackWfE`) + both Soundness engines.

## Why nothing was committed / edited

Everything is entangled in the red `Soundness.lean`. Any field added to `applyf`/`arg`/`EnvWf.cons` breaks
Runtime.lean (`stackSeg_toStackWf`), Machine.lean (`StackWf`/`StackWfV`/`StackWfE`), and both Soundness
engines at once — none per-file green, none committable under the no-red-commit rule until the whole thing
is green. Remaining work: (a) two-constructor frame carrier, (b) forward-readiness field on `StackWf.arg`,
(c) `EnvWf.cons` ground-args clause, (d) `hasTypeRT_weakenEff` (~25-arm `weakenEffAux` mirror,
Soundness-local), (e) wiring the 4 A/B apply sites, (f) B-engine migration past 2460. Speculatively landing
any subset only deepens the near-green tree's breakage with no committable checkpoint — so, as in G27, the
correct low-risk outcome is this refutation + the newly-scoped source-of-readiness gap, G26 tree and G25
infra preserved.

## Definitively known for the next session

- The discharge (single `hasTypeRT_subst` grounding at `lvl'` under (C1)-(C3)) is correct, unchanged.
- The carrier CANNOT be a match-def / plain field over the closure PROOF (proof-irrelevance; scratch-checked).
- The carrier MUST be a two-constructor inductive replacing `applyf`'s function premise (aligned fields).
- (C3)'s SOURCE requires a forward-readiness obligation on `StackWf.arg` fed by the Apply node's `rf` —
  the genuinely new, larger piece G27 under-scoped. `EnvWf.cons` ground-clause covers only the var-lookup path.

## Tree state at stop

- No commit. `Soundness.lean` byte-identical to G26 (verified). `plan.md` gains a Session-G28 entry; this
  note added. `grep -rn sorry` empty; HEAD `0c0b6951`. Caveat 5 OPEN. Substitution infra COMPLETE (G25);
  carrier mechanism narrowed (match-def refuted -> two-constructor frame inductive); (C3)-source gap
  (forward arg-frame readiness) newly identified.
