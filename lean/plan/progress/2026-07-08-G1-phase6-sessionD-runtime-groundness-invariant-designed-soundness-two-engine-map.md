---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 6 "Session D". The non-mechanical var-preservation obstruction is
  DESIGNED and validated (the "runtime groundness" invariant), the `genAtV_closure_ready_value_node`
  wrapper is designed (TyEquiv bridge solved, one residual strictness subtlety identified), and the
  Soundness.lean error map is corrected to its TRUE two-engine shape. Full green NOT reached; nothing
  committed (the invariant is inherently entangled with red `Soundness.lean`, so no additive slice
  builds clean in isolation this session).
status: LANDED (design only) — no commits. Working tree: `Soundness.lean` still uncommitted, with one
  correct de-masking edit applied (line 1560, 5-tuple→6-tuple `mStateWf_E` destructure) that revealed
  the true error scope. Every other file unchanged, per-file green at HEAD `7797b28d`.
kind: progress
component: lean (Types.Soundness — analysis; design for Types.Runtime/Machine/Substitution)
---

# G1 Phase 6 (Session D): runtime-groundness invariant designed; Soundness two-engine map corrected

No LSP/MCP tools were available this session (script fallback only: Read/Grep + `lake build`/
`lake env lean`). This constrained iteration to batch builds, so the ~90-error mechanical grind across
two mirror engines was not attempted (it needs live goal-state). Instead the session settled the two
genuinely non-mechanical pieces at the DESIGN level and corrected the error map.

## Corrected Soundness.lean error map — it is a TWO-ENGINE migration

Session C's note reported "103 errors" but 66 of them were a single spurious `<;> simp` combinator
error at line 1592, repeated 66×, which **masked the entire second half of the file**. The real cause
at 1592 is a one-line destructure bug: `mStateWf_E` now returns a **6-tuple** `⟨Γ, τin, lvl, henv, hty,
hst⟩` (the `lvl` was added when `HasType` became level-parameterized), but line 1560 destructured it
into a **5-tuple** `⟨Γ, τin, henv, hty, hst⟩`, so `henv` bound to `lvl : Nat`, `hty` to `EnvWf`, etc.
— cascading 66 downstream `simp`/application errors in the `progress_or_perform` lemma.

**Fix applied this session (line 1560):** `⟨Γ, τin, _, henv, hty, hst⟩`. This is correct and
de-masking. Headline count stays 103 only by coincidence — the 66 spurious repeats vanished and ~66
REAL errors in the second engine (`evalR`/`soundness_evalR`, lines 2392-3237) became visible. The file
is now in a strictly more accurate state for Session E.

The two engines and their (now-visible) error clusters:

**A-engine (`reduceEval`/`preservation_E`, lines ~69-1030) — MORE migrated:**
- **69, 90** — `weakenEffAux` `app`/`conv` arms: `HasType` minor-premise arg-shape / `ih`-arity drift.
- **218, 219** — the var-preservation blocker (below): `(hvty args).conv` fails because `hvty` is now
  `(∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) → HasTypeV v (s.instantiateV args)` — a function
  awaiting the args side-condition, not a `HasTypeV`.
- **223** — `app` case: `StackWf.arg henv harg hw …` — the `arg` frame constructor now takes an `lvl`;
  the `HasType.app`/`StackWf.arg` shapes shifted.
- **243** — `genAtV_closure_ready_value_node` referenced but undefined (wrapper — designed below).
- **247** — stale `s.instantiate args` → `s.instantiateV args` (a `rw`/`simp` target).

**B-engine (`reduceEvalR`/`soundness_evalR`, lines ~2392-3237) — LESS migrated:**
- Mirrors every A-engine cluster (its own `weakenEffAux`, var-preservation at **2943-2945**
  `(hvty args).conv heq` via `vstate_of_value_B`, let_poly at ~2967, etc.).
- **Additionally still on the OLD magnitude machinery in places:** lines **2700-2711** define a
  `StackWfV`/`StackWfE`-analog readiness using `sc.instantiate` UNCONDITIONALLY
  (`∀ args, HasTypeV v (sc.instantiate args)`), not the level-native `instantiateV` + side-condition.
  Lines **130, 1908, 3775** still call `s.instantiate` (magnitude). These need the same
  `instantiate`→`instantiateV` + `l=0∨l=s.level` side-condition refactor the A-engine already got.

Net: ~25 A-engine + ~66 B-engine ≈ 90 mechanical errors, plus the var-preservation blocker appearing
in BOTH engines (218-219 and 2943-2945), plus the missing wrapper (243, and its B-mirror).

## The non-mechanical piece — the "runtime groundness" invariant (DESIGNED + VALIDATED)

**Statement of the problem.** At the var-preservation site the control is `HasType lvl Γ ⟨.Variable x⟩
(s.instantiateV args) ε`; `envwf_lookup henv hlookup` gives `v` with
`hvty : ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) → HasTypeV v (s.instantiateV args)`.
We need `hvty args` for the SPECIFIC `args` that `inv_var` extracted from the derivation. `HasType.var`
records no constraint on `args`, so the side-condition is not locally available — and must NOT be added
to `HasType.var` (it would reject legitimate typing-time instantiations; see `hbody_ref`).

**The invariant (validated against `hbody_ref`).** In a *running, well-typed* machine state, the
control's `HasType` derivation has all its `var`/`builtin` instantiation args **ground** — every level
in every arg is `0` (hence trivially `l = 0 ∨ l = s.level`). This is TRUE and consistent with
`hbody_ref` precisely because `hbody_ref`'s non-ground arg (`a : genAtV 1 defnA` instantiated at
`[var 2 0]`, level 2) is a *static* subderivation INSIDE the level-2 generalization of `c = \w.cRefBody`.
That subderivation never becomes a runtime control as-is: when the closure `c` is applied, the keystone
`genAtV_instantiate_lam_ready`/`genAtV_closure_ready_value` re-types `c`'s body via `substAt 2 [ground
arg]`, which rewrites the `a`-instantiation-arg `var 2 0` into a GROUND type (e.g. `integer`) before it
is ever the control. `Typing.lean`'s `section Examples` (lines 703-730) machine-witnesses exactly this:
`hbody_ref` at args `[var 2 0]` statically, keystone fires at args `[integer]` (ground), grounding the
inner `a`-arg. So the invariant simultaneously (a) ALLOWS the legitimate static `hbody_ref` and (b)
guarantees runtime controls have ground args. The pre-tightened `l = 0 ∨ l = s.level` bound (Session C)
is even weaker than pure `l = 0`, so the discharge is a fortiori available.

**Why groundness of the goal type alone is NOT enough (a subtlety Session E must not trip on).** One is
tempted to only strengthen `MStateWf` to require `τin` ground and derive the args bound from
`s.instantiateV args = τin` ground. This FAILS: `instantiateV` ignores args at positions beyond the
scheme body's level-`s.level` variables (they are `getD`-padded), so a derivation could pick a
non-ground *irrelevant* arg that does not affect `τin` yet violates the blanket
`∀ t ∈ args, …` bound. The bound quantifies over ALL list elements. Hence the invariant must constrain
the DERIVATION's chosen args, not just the resulting type.

**Threading options for Session E (in order of preference):**
1. **Runtime-restricted judgment `HasTypeRT lvl Γ e τ ε`** — a mirror of `HasType` whose `var`/`builtin`
   arms additionally carry `∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level`; every other arm is a
   verbatim copy. `MStateWf`'s `.E` case uses `HasTypeRT` for the control; `StackWfE`/`StackWfV` assign
   readiness likewise. Inversion lemmas get RT-variants (the var one now yields the bound directly;
   243's wrapper and 216-219 discharge trivially). Preservation re-establishes `HasTypeRT` at each step:
   the top-level program under `Γ=[]` is ground (no free type vars ⇒ every arg it can pick is ground),
   and each push either re-uses a stored RT-derivation or produces one via the keystone's `substAt`
   re-typing (which grounds args). Cost: ~21-constructor duplicate + RT-inversion set, but purely
   additive and each arm is a mechanical copy except `var`/`builtin`.
2. **Groundness side-predicate on the stored derivation.** Instead of a full judgment, carry a
   `DerivArgsGround` proof alongside `HasType` in `MStateWf`. Harder to state cleanly (it is a property
   of the derivation tree, not the term), and every inversion lemma must thread it — likely messier than
   option 1.
3. (Rejected) premise on `HasType.var`/`.builtin` — wrongly rejects `hbody_ref`; header-fence anyway.

Recommendation: **option 1**. It localizes the metatheory (the interesting content is only the `var`/
`builtin` arms and the keystone-produces-ground-args preservation lemma), keeps `HasType` itself
untouched (no header-fence), and the ~90 mechanical Soundness errors then re-green against `HasTypeRT`
uniformly. Note the two engines both need it (A: 216-219; B: 2943-2945).

## The `genAtV_closure_ready_value_node` wrapper (DESIGNED; one residual subtlety)

Call site (A-engine, line 243; B-mirror near 2967):
`genAtV_closure_ready_value_node hlvl0 hdefn hΓpa hcw henv args hargs`, needing
`HasTypeV (Value.Closure lx lbody env) ((Scheme.genAtV lvl defnTy).instantiateV args)` from
`hdefn : HasType lvl Γ ⟨.Lambda lx lbody, la⟩ defnTy ε`, `hcw : CtxWfV lvl Γ`, `henv : EnvWf env Γ`,
and (to be brought into scope at the call site) `hlvl0 : lvl ≠ 0` and
`hΓpa : PolyAboveFV lvl Γ ⟨.Lambda lx lbody, la⟩`.

Intended body: `obtain ⟨lvl', argTy, εb, retTy, hle, hfv, hbody, heq⟩ := inv_lambda hdefn`, then apply
`genAtV_closure_ready_value` (Substitution.lean:103) and convert.

**Solved: the TyEquiv bridge.** `inv_lambda` yields `heq : Ty.TyEquiv (.fun argTy εb retTy) defnTy`, so
the keystone concludes about `genAtV lvl (.fun argTy εb retTy)` but the call site wants `genAtV lvl
defnTy`. Bridge lemma (provable, additive — put in Substitution.lean above the wrapper):
```
theorem instantiateV_genAtV_tyEquiv (ℓ : Nat) {d₁ d₂ : Ty} (h : Ty.TyEquiv d₁ d₂) (args : List Ty) :
    Ty.TyEquiv ((Scheme.genAtV ℓ d₁).instantiateV args) ((Scheme.genAtV ℓ d₂).instantiateV args)
```
Proof: `genAtV ℓ d` has `.level = ℓ`, `.body = d`, `.arity = (d.levels.filter (·=ℓ)).length`. The
`instantiateV` `if arity = 0` branch agrees across the TyEquiv because `arity = 0 ↔ ℓ ∉ d.levels`, and
`Ty.levels_tyEquiv` (Typing.lean:57) preserves the level SET (so membership of `ℓ` agrees). In the
`arity=0` branch both sides reduce to `d₁`/`d₂` — closed by `h`. In the `else` branch both are
`Ty.substAt ℓ (fun i => args.getD i (.var ℓ i)) dᵢ` with the SAME `σ` (level is `ℓ` for both), closed
by `Ty.substAt_tyEquiv ℓ σ h` (Scheme.lean:909). Then wrapper finishes with `HasTypeV.conv … (this)`.

**Residual subtlety (Session E must resolve):** `genAtV_closure_ready_value` requires `hlt : ℓ < lvl'`
(STRICT), but `inv_lambda` only gives `hle : lvl ≤ lvl'`. When `argTy` mentions level `lvl` the strict
bound follows from `hfv : ∀ l ∈ argTy.levels, l < lvl'`; but if only `retTy`/`εb` mention `lvl` (or
nothing does, i.e. `genAtV lvl defnTy` has arity 0) the strictness is not immediate. For the arity-0
case the wrapper should short-circuit via `closure_typed_of_lambda` (Substitution.lean:86) + the
TyEquiv bridge (no keystone, no strictness needed, since `instantiateV` returns the body). For the
arity≠0 case one must show `lvl ∈ defnTy.levels ⇒ lvl < lvl'` — likely by strengthening `inv_lambda`
(or `HasType.lam`) to also record `∀ l ∈ retTy.levels, l ≤ …` OR by observing that a genAtV-at-`lvl`
binding only arises in `let_poly` where the body is typed at `lvl+1`, forcing the relevant sublevel
strictly above `lvl`. This is real (small) proof design, best done with LSP; it is why the wrapper was
"referenced but not defined" rather than a trivial stub.

## Tree state at stop
- HEAD `7797b28d` (unchanged — NOTHING committed this session).
- Working tree: `Eyg/Types/Soundness.lean` modified (the as-found Session-C partial migration PLUS the
  single correct line-1560 de-masking edit), uncommitted. `lake build Eyg.Types.Soundness`: 103 errors,
  now of the TRUE two-engine composition mapped above (no longer masked). Untracked `.claude/`.
- Every other per-file target green at `7797b28d`; `grep sorry Eyg/Types/*.lean`: none.
- No axioms added, no `sorry`, no statement weakened. Caveat 5 remains OPEN.

## Recommended Session E order (needs LSP)
1. Add `instantiateV_genAtV_tyEquiv` + `genAtV_closure_ready_value_node` (Substitution.lean), resolving
   the arity-0/strictness split — additive, verify per-file green on Substitution.
2. Introduce `HasTypeRT` (option 1) + RT-inversion lemmas + wire into `MStateWf`/`StackWfE`/`StackWfV`
   (Machine.lean) — verify per-file green on Machine/Runtime.
3. Grind the ~90 mechanical Soundness errors across BOTH engines (var-preservation now discharges from
   `HasTypeRT.var`; migrate the B-engine's residual `sc.instantiate` sites at 130/1908/2700-2711/3775
   to `instantiateV` + side-condition), with live goal-state.
4. Set `soundness`/`soundness_evalR` ambient level to a nonzero constant (≥1) so top-level `let_poly`
   generalizes at `s.level ≥ 1`.
5. Then Phase 7 (sanity example + `type-soundness-report.md` Caveat 5).
