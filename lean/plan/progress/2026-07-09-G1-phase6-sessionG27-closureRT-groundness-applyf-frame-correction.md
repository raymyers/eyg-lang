---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G27". Design session on the last open item (closure-body-RT
  groundness). No code landed (correctly — the remaining threading is large, multi-file, and
  un-validatable without LSP in-budget; the near-green Soundness.lean was preserved intact). Key
  RESULT: a definitive correction to the G24-G26 standing recommendation — the groundness invariant
  CANNOT live on `HasTypeV.closure`/`HasTypeRT.lam` (proven by concrete reachable witnesses); it must
  thread through the `applyf` frame (`StackWf.applyf`/`StackSegWf.applyf`) + the `EnvWf.cons`
  ground-readiness clause. The exact discharge (single grounding at ℓ=lvl' via the already-landed
  `hasTypeRT_subst`, under 3 "ground-enough" side conditions) is worked out.
status: PARTIAL (design advance + correction; no commit). Soundness.lean unchanged from G26
  (uncommitted-red, A-engine at exactly the 2 closure-apply RT sites 874-877 / 1036-1039). No `sorry`
  anywhere. HEAD `471de13a`. Caveat 5 OPEN.
kind: progress
component: lean
---

# G1 Phase 6 (Session G27): closure-RT groundness — the invariant belongs on the `applyf` frame, not the closure

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake env lean`.
HEAD `471de13a`; `grep -rn sorry Eyg/Types/*.lean` empty throughout. Made NO edits to source — the
G26 durable working tree (`Soundness.lean` A-engine at the 2 crux sites) is preserved exactly.

## Confirmed current error state (exact)

`lake env lean -DmaxErrors=8 Soundness.lean` → errors ONLY at 874-877 and 1036-1039 (+ the deliberately
un-migrated B-engine past 2460). Root cause at each site: `cases hf with | closure henvc hbody heqc`
binds only 3 names, but migrated `HasTypeV.closure` has 5 fields (`hlvl henv hfv hbody heq`), so the
binders are misassigned (`henvc`:=`1≤lvl'`, `hbody`:=`EnvWf`, `heqc`:=`hfv`); AND the `.E` `refine`
tuple is missing the `lvl`, `1≤lvl`, and — the real gap — the `HasTypeRT hty` slot for
`hty = weakenEff (HasType.conv hbody hR (.refl _)) …`. So the crux is: **produce `HasTypeRT` of the
applied closure body.**

## The load-bearing result: it is NOT a `HasTypeV.closure` field (G24–G26 recommendation corrected)

G24/G26 recommended threading groundness into `HasTypeV.closure` (+ `EnvWf.cons`) — candidate
`CtxGround ℓ Γ`/`EnvGround`. **This session proves that framing is subtly wrong** via two concrete,
reachable witnesses:

1. **Stored closures are legitimately non-RT-ready even at their own level.** Program
   `let f = (\u. \w. a u) in …` (a : ∀α.α→α outer, level ℓ_a): the inner `\w. a u` is typed with
   `u : .var L1 0` (L1 = f's generalization level), so its body `a u` instantiates `a` at `[.var L1 0]`
   — a var-node arg at level `L1 ≠ lvl'`(=inner level `L2`)`, ≠ 0, ≠ ℓ_a`. Hence the inner body is
   **not** `RTSubstReady L2` (which only admits the extra disjunct `L2`, not `L1`). So NO uniform
   body-indexed field (`HasTypeRT hbody`, `RTSubstReady lvl' hbody`, `HasTypeRTAt lvl' hbody`) can be a
   `HasTypeV.closure` constructor field: the `EnvWf.cons` polymorphic-readiness clause
   (`∀ args, levels⊆{0,ℓ} → HasTypeV v (s.instantiateV args)`) must build `HasTypeV.closure` even for
   **non-ground** args (level = ℓ), producing exactly these non-ready bodies.
2. **The direct-lambda creation site (`closure_typed_of_lambda`, Soundness 214) genuinely cannot
   supply it.** There `hty : HasType lvl Γ (lambda x body) τ ε` with `hrt : HasTypeRT hty`, and
   `HasTypeRT.lam` carries no body premise by design — a control lambda `\w. a w` with a non-ground
   body arg `[.var lvl' 0]` must stay `HasTypeRT` (else the whole referencing program is rejected;
   see the machine-checked example at Typing.lean 2295). Strengthening `HasTypeRT.lam` to carry
   `RTSubstReady lvl' hbody` was evaluated and **rejected**: it admits `\w. a w` (arg level `lvl'` is
   allowed) BUT rejects witness (1)'s `\w. a u` (arg level `L1 ≠ lvl'`), so it would make that
   legitimate closed program non-RT at `mStateWf_initial` — unsound.

**Conclusion (the correction): stored closures can be non-RT; only APPLIED closures are ground-enough
to be RT.** The distinction stored-vs-applied is exactly env-binding vs `applyf`-frame. So the invariant
must live on the **`applyf` frame** (`StackWf.applyf` / `StackSegWf.applyf`, where the function value is
about to be applied at a concrete arrow), NOT on `HasTypeV.closure`.

## The discharge is clean once the frame carries 3 "ground-enough" side conditions (single grounding —
no iteration)

Give the applyf frame (function value `hf : HasTypeV f (.fun argTy εf retTy)`) enough that, when `f`
is a closure with internals `lvl' x body cenv argTy' εb' retTy' Γ` (via `cases`/`heqc`), we can run the
**already-landed** `hasTypeRT_subst` (G25) once, at `ℓ = lvl'`, with ANY ground `σ`:
`hasTypeRT_subst (hℓ:lvl'≠0) σ (hσ ground) (hr : RTSubstReady lvl' hbody) (le_refl lvl')
(hpa : PolyAboveFV lvl' Γnew body)` yields `∃ h', HasType lvl' (substCtxAt lvl' σ Γnew) body
(substAt lvl' σ retTy') (substAt lvl' σ εb') , HasTypeRT h'`. This equals the required judgment iff
`substAt/substCtxAt` are identity, i.e. **`lvl' ∉` the level sets of `Γnew`, `retTy'`, `εb'`** (argTy'
already `< lvl'` via the closure's `hfv`). So the 3 conditions the applied closure must satisfy:
  (C1) `CtxWfV lvl' Γ` (captured context ground-below-`lvl'`) — plus `argTy' < lvl'` gives `CtxWfV lvl'
       Γnew`, hence `substCtxAt lvl' σ Γnew = Γnew` (`substCtxAt_fix`) AND `PolyAboveFV`
       (`polyAboveFV_of_ctxPolyBd` + `ctxPolyBd_of_envWf henv`);
  (C2) `∀ l ∈ retTy'.levels, l < lvl'` and `∀ l ∈ εb'.levels, l < lvl'` (result/latent ground-below-
       `lvl'`) — so `substAt lvl' σ` fixes them;
  (C3) `RTSubstReady lvl' hbody` (the body's var/builtin args ⊆ `{0, lvl', s.level}`, with the carried
       `NoGenAt` witnesses — all dischargeable via `noGenAt_of_lt` since everything is `< lvl'` at the
       strict boundary).
Under (C1)+(C2), grounding at the SINGLE level `lvl'` suffices — **the G24/G26 "iterated multi-level
grounding" worry dissolves**: (C2)+`hfv`+(C1) force every exposed level `< lvl'`, and (C3) confines the
only non-RT body-arg level to exactly `lvl'`, so one `hasTypeRT_subst` pass closes it. `σ` can be a
ground constant (e.g. `fun _ => .empty`, `levels = []`).

## Why the frame CAN supply (C1)–(C3): the construction chain (next-session target)

The applyf frame is created in the **`Arg`-frame preservation case** (Soundness 858-862:
`StackWf.applyf (hv.conv hσ) hw hrest`), where `hv : HasTypeV f (.fun argTy εf retTy)` is the function
value and `argTy`/`εf`/`retTy` come from the well-typed `Apply` node (`inv_app_rt`, which ALSO hands us
`rf : HasTypeRT hf`, `rarg : HasTypeRT harg`). At that point the arrow `argTy→retTy` is the type at
which the program actually applies `f`; for a closed running program this arrow is ground-enough
(C2-satisfying) because the surrounding derivation forced the function's polymorphism to concrete types.
The captured-context groundness (C1) and body-readiness (C3) must be carried on the closure value from
its creation, but — crucially — only need to hold **relative to a ground application arrow**, which is
the frame's job to guarantee. Concretely the next session should:
  1. Add (C1)+(C3)-style ground-readiness to the `EnvWf.cons` clause **for ground args only**
     (`∀ args, (levels⊆{0}) → …RT-ready…`), leaving the existing non-ground clause untouched — so
     non-ground instantiations (which produce non-ready bodies) are unaffected, and the var-use site
     (`inv_var_rt`'s `hargs` bounds by `{0,s.level}`; the applyf path pins `s.level` ground) draws the
     ready version.
  2. Add (C2) (ground arrow) to `StackWf.applyf`/`StackSegWf.applyf`, discharged at the Arg-frame
     creation from the applied arrow's groundness.
  3. Wire the 4 apply sites (2 A-engine + 2 B-engine) to `cases` the closure (5 fields), pull (C1)-(C3),
     run `hasTypeRT_subst` once, and `HasTypeRT.conv`/`hasTypeRT_weakenEff` back to the `weakenEff`+`conv`
     wrapper. (`hasTypeRT_weakenEff` — RT preserved under `weakenEff` — is a needed ~25-arm mirror of
     `weakenEffAux`; it lives in Soundness.lean, so it is only committable once the file is green.)

## Why nothing was committed / edited

The substitution consumer (`hasTypeRT_subst`, `RTSubstReady`, `HasTypeRTAt`, `Ty.not_mem_levels_substAt`)
is already landed and green (G25). Everything remaining is a runtime-judgment strengthening across
`Runtime.lean` (`EnvWf.cons`, `StackSegWf.applyf`) + `Machine.lean` (`StackWf.applyf`, `MStateWf`) + both
`Soundness.lean` engines — a multi-file change validatable ONLY when `Soundness.lean` reaches green (no
red-commit exception), and too large to land+verify reliably without LSP in one session. Speculatively
half-threading it would leave the near-green file more broken and harder to resume. The correct,
low-risk outcome is this precise design + the standing-recommendation correction; the near-green
`Soundness.lean` and the G25 infra are preserved for the executing session.

## Tree state at stop

- No commit. `Soundness.lean`/`plan.md`: uncommitted, exactly as G26 left them, verified intact
  (`git status` clean except the two known M files; sorry-count 0; HEAD `471de13a`).
- Caveat 5 OPEN. Substitution infra COMPLETE (G25); groundness invariant now correctly LOCATED (applyf
  frame + EnvWf ground-readiness, NOT HasTypeV.closure) with the single-grounding discharge + 3 side
  conditions fully worked out; wiring across both engines is the remaining (mechanical-but-large) step.
