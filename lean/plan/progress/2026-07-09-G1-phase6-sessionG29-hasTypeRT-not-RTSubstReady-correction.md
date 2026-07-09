---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G29". Design session on the closure-apply RT crux.
  No code landed (correctly — nothing independently committable; all entangled in red Soundness).
  Two substantive results: (1) the crux needs `HasTypeRT hbody`, NOT `RTSubstReady lvl' hbody` —
  correcting G27's framing and showing its two rejection witnesses are non-adversarial; (2) the
  forward-readiness-on-arg-frame design (G28) does NOT reduce to the StackWfE-Assign template and
  relocates rather than solves the problem; the true minimal obstruction is a runtime env-groundness
  invariant discharged at exactly one site (plain lambda-eval, Soundness ~214).
status: PARTIAL (design correction + target sharpened; no commit). Soundness.lean byte-identical to
  G26/G28 (backed up /tmp/Soundness.G28start.backup.lean, diff -q IDENTICAL). A-engine red at exactly
  the 2 closure-apply RT sites 874-877 / 1036-1039; B-engine un-migrated past 2460. No `sorry` anywhere.
  HEAD 96e68baf. Caveat 5 OPEN.
kind: progress
component: lean
---

# G1 Phase 6 (Session G29): the crux needs `HasTypeRT hbody`, not `RTSubstReady lvl' hbody`; the true obstruction is env-groundness at the lambda-eval site

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` unavailable). Read/Grep +
`lake env lean`. HEAD `96e68baf`. NO source edits — G26/G28 near-green working tree preserved
byte-identical (`diff -q` IDENTICAL vs `/tmp/Soundness.G28start.backup.lean`).
`grep -rn sorry Eyg/Types/*.lean` empty.

## Confirmed error state (unchanged from G26/G27/G28)

`lake env lean -DmaxErrors=60 Soundness.lean`: A-engine errors ONLY at 874-877 and 1036-1039 (the two
closure-apply RT sites — `cases hf with | closure henvc hbody heqc` binds 3 of the migrated 5
`HasTypeV.closure` fields `hlvl' henv hfv hbody heq`; the `.E` `refine` at 876-878 also omits the
`lvl,hlvl` pair and the `HasTypeRT hty` slot of `MStateWf.E`). Everything ≥ 2460 is the deliberately
un-migrated B-engine. No regressions vs G26.

## Task attempted: build the G28 forward-readiness obligation on `StackWf.arg`/`StackSegWf.arg`.
## What the concrete trace shows.

### Result 1 — the crux needs `HasTypeRT hbody`, NOT `RTSubstReady lvl' hbody` (corrects G27)

Traced what `MStateWf.E` actually requires at the crux (`preservation_V`, Apply-frame, closure case,
Soundness 868-882). The successor `.E` control is the closure BODY, and `mStateWf_E` (Soundness 196)
returns `⟨Γ, τin, lvl, hlvl, henv, hty, hrt, hst⟩` — so the missing slot is `hrt : HasTypeRT hty`
where `hty = weakenEff (HasType.conv hbody hR …) …`. Peeling the `weakenEff`/`conv` wrappers (which
need small RT companions `hasTypeRT_weakenEff`/`hasTypeRT_conv` — Soundness-local, NOT yet built;
confirmed absent), the real need is **`HasTypeRT hbody`** of the closure body — a `HasTypeRT`, **not**
the `RTSubstReady lvl' hbody` that G27/G28 threaded.

This distinction is decisive. `HasTypeRT.var` (Typing 968-970) bounds a var node's instantiation-arg
levels by `{0, s.level}` — the var's OWN scheme level. `RTSubstReady.var` (Typing 1138-1141) adds an
`ℓ` disjunct AND `RTSubstReady.let_poly` imposes `lvl ≠ ℓ` + `NoGenAt`. **G27's two witnesses for
rejecting a closure-stored readiness field are HasTypeRT-fine:**
- `\u. \w. a u` (inner closure body `a u`; `a` instantiated at `[.var L1 0]`, `a.level = L1` = f's gen
  level): `HasTypeRT.var` HOLDS because `L1 ∈ {0, a.level = L1}`. G27 rejected it only for
  `RTSubstReady lvl'` (ℓ = inner `lvl' ≠ L1`) — irrelevant to the crux.
- escape witness `\x. (let h = \z.z in h)` (body `let h=\z.z in h`, inner `let_poly` at exactly
  `lvl'`): `HasTypeRT.let_poly` (Typing 989-991) needs ONLY `HasTypeRT` of the let-body `h`; `h`
  instantiated at `[.var lvl' 0]`, `h.level = lvl'` ⇒ `HasTypeRT.var` HOLDS. `RTSubstReady` would FAIL
  here (inner `let_poly` at exactly `lvl'` violates `lvl ≠ ℓ`). So the **entire G6-G9
  "escape/level-normalization/raise-sublevel" worry is dissolved**: the crux never needed
  `RTSubstReady lvl'` of these bodies, only `HasTypeRT`, which holds directly with no grounding, no
  `hasTypeRT_subst`, no level-raise metatheorem.

**Consequence:** the G27 discharge recipe ("run `hasTypeRT_subst` once at ℓ=lvl' with 3 side
conditions (C1)-(C3), (C3) = `RTSubstReady lvl' hbody`") is HARDER THAN NEEDED and mis-targeted for
the common cases. The right recipe is `HasTypeRT hbody` directly.

### Result 2 — the G28 forward-readiness-on-arg-frame does NOT reduce to the Assign template

The Assign forward obligation (`StackWfE`, Machine.lean 281-283) reads "when the CURRENT control `e`
is a lambda, `HasTypeV (Closure lx lbody env) (sc.instantiateV args)` for all ground `args`." It is
dischargeable because `e` is the immediate control — its closure is **one lambda-eval step** away and
its body typing is available at `stackWf_toStackWfE` time (via `inv_lambda`/`closure_typed_of_lambda`/
keystone). The **arg frame's function slot is categorically different**: it is filled by the value
that the function subterm `f` reduces to after **arbitrary** evaluation. A forward obligation about it
must survive `f`'s entire multi-step evaluation, not one step, so it cannot be a one-lambda-step
Assign-style clause, and (as G28 already found) is NOT derivable from `rf : HasTypeRT hf` at
arg-frame creation (Soundness 224-226) — `HasTypeRT.lam` carries no body premise (re-confirmed:
`hasTypeRT_lambda`, Typing 930-ish, is `HasTypeRT.lam` with no body arg). To survive arbitrary
evaluation the obligation would have to be carried by the VALUE judgment itself — i.e. relocated onto
`HasTypeV.closure`. **So the forward-readiness-on-arg-frame relocates the problem to
`HasTypeV.closure`, it does not solve it.** G28's design is a detour.

### Result 3 — the TRUE minimal obstruction: env-groundness at the plain lambda-eval site

Put `HasTypeRT hbody` on `HasTypeV.closure` (the natural home, per Result 2). Discharge obligations:
- **Poly-let path** — the closure VALUE is never built eagerly; the Assign frame stores a readiness
  FUNCTION (`genAtV_closure_ready_value_node`, Soundness 248) that materializes `HasTypeV.closure`
  ONLY at GROUND instantiations (its `hargs : levels ⊆ {0,s.level}` hypothesis), where the body is
  re-typed/grounded via `substAt` ⇒ `HasTypeRT hbody` follows from the G25 `hasTypeRT_subst` infra.
  So this path is dischargeable with existing infra.
- **Mono-let path** (`closure_typed_of_lambda`, Soundness 238): similar — body typed at the binding.
- **Plain lambda-eval** (Soundness 211-215): `HasTypeV.closure (…) henv hfv hbody heq` is built from
  `inv_lambda hty`, but the only RT in scope is `hrt = HasTypeRT.lam` of the WHOLE lambda, which by
  design carries **no body premise**. So `HasTypeRT hbody` is **NOT locally available here.** This is
  the single genuine gap.

`HasTypeRT hbody` fails exactly when the body instantiates a captured var `a` at a level ∉
`{0, a.level}` — e.g. `\w. a w` with `a:level 1` at `[.var 2 0]`. Such a body arises statically as a
poly-let DEFN inside a level-2 generalization, but by the time ANY lambda is evaluated as a plain
control the enclosing generalization has been instantiated to ground (poly-let defns flow through the
readiness function at ground args; applied closures ground their result level), so the captured-var
instantiations reaching lambda-eval should be ground-in-`{0,a.level}`. **That is precisely a runtime
env/context-groundness invariant** (G26's candidate `CtxGround ℓ Γ`/`EnvGround`), threaded on
`EnvWf`/`HasTypeV.closure`, whose ONE payoff is: at plain lambda-eval, the captured env has no active
generalization-level type variable reachable ⇒ the lambda body's var/builtin instantiations are ground
⇒ `HasTypeRT hbody` is derivable and storable. Then the crux closes by `cases hf` yielding the stored
`HasTypeRT hbody` directly — **no forward-readiness on the arg frame, no apply-site grounding, no
level-normalization.**

## Net design correction for the next session

1. Field to add is `HasTypeRT hbody` on `HasTypeV.closure` (NOT `RTSubstReady lvl' hbody` on
   `applyf`/`arg`). Crux then closes with a `cases hf` projection + the two tiny wrappers
   `hasTypeRT_conv`/`hasTypeRT_weakenEff` (Soundness-local).
2. The single non-trivial discharge is the plain lambda-eval site; it needs a runtime env-groundness
   invariant (`CtxGround`/`EnvGround`) on `EnvWf`/`HasTypeV.closure` so the captured env forces the
   body's instantiation args ground. Design/prove that invariant (its construction at lambda-eval and
   its preservation across the readiness function + closure-apply) — this is the real remaining
   metatheory, and it is a strengthening of the runtime typing judgments (flag for sign-off, per the
   closing-session brief).
3. Poly/mono-let discharge reuse existing infra (`genAtV_closure_ready_value_node` +
   `hasTypeRT_subst` / `closure_typed_of_lambda`).
4. G27's `RTSubstReady lvl'`-on-frame recipe, G28's forward-readiness-on-arg-frame, and the G6-G9
   level-raise/normalization line are all avoidable detours for the crux (they targeted the wrong,
   stronger predicate). Keep `RTSubstReady`/`hasTypeRT_subst` — they ARE needed for the poly-let
   ground-instantiation re-typing (discharge item 3), just not at the apply site for HasTypeRT.

## Why nothing was committed

All entangled in the red `Soundness.lean`: adding a field to `HasTypeV.closure` breaks Runtime +
Machine + both Soundness engines simultaneously; the env-groundness invariant is unbuilt; the two RT
wrappers are Soundness-local (so not committable while Soundness is red); the B-engine is fully
un-migrated. No independently-green increment exists. As in G24/G26/G27/G28, speculatively landing any
subset only deepens the near-green tree's breakage with no committable checkpoint. Correct low-risk
outcome: the design correction (HasTypeRT ≠ RTSubstReady) + target sharpening (single site + single
invariant), tree preserved byte-identical, G25 substitution infra intact.

## Tree state at stop

No commit. `Soundness.lean` byte-identical to G26/G28 (verified `diff -q`). `plan.md` gains a
Session-G29 entry; this note added. `grep -rn sorry` empty; HEAD `96e68baf`. Caveat 5 OPEN.
Substitution infra COMPLETE (G25). The crux predicate is corrected `RTSubstReady lvl' → HasTypeRT`;
the obstruction is localized to one site (plain lambda-eval) + one invariant (env-groundness).
