---
name: eyg-g2-args-discipline-universal-readiness-plan
description: Rearchitect the runtime typing invariant to close G1 Phase 6's closure-RT wall — replace
  the {0, s.level}-bounded HasTypeRT/readiness architecture (machine-refuted in every storable form,
  G27–G31) with a STATIC per-derivation args-level discipline ("ArgsDisc") + floor-conditioned
  near-universal EnvWf readiness, so var-preservation types the looked-up value directly and closure
  bodies need no grounding at apply. Keystones instance-validated (machine-checked, this doc's
  appendix) at HEAD 1d92756d; full generality gated behind a Phase-1 spike.
date: 2026-07-09
status: PROPOSED — awaiting user sign-off on the one statement-level change (the soundness entry
  premise `HasTypeRT h` is REPLACED by `ArgsDisc … h`; same spec-refinement class as the authorized
  G20 strict-sublevel reshape). Nothing executed beyond the validation appendix.
---

# G2 — close Caveat 5 via a static args-level discipline + universal readiness

Successor to `plan/eyg-g1-level-tagged-ty.md`, which is PAUSED at Phase 6 with exactly one open
question. Read that plan's "Decision to pause" section first; do not re-derive the ~50-session
history. This plan is the requested rearchitecture to resolve (prove-or-refute) that open question.

## The wall, distilled (do not re-derive; see the G-session notes)

`MStateWf.E` requires `HasTypeRT hty` of the running control. At the two closure-apply crux sites
(`Soundness.lean:874-877`, `1036-1039`) the applied closure's **body** becomes the control, and
`HasTypeRT hbody` is genuinely unobtainable:

- `HasTypeRT.var` bounds instantiation args' levels by `{0, s.level}`, matching `EnvWf.cons`'s
  bounded readiness promise.
- But reachable, genuinely-sound closures instantiate captured schemes at **arbitrary free levels**:
  `let a = \x.x in \w. a w` (one off-scheme level, G30) and `let a = \x.\y.x in (\w. a w)` (two
  independent off-scheme levels, one escaping into the result type, G31). Machine-checked: no
  env-groundness property, no stored `HasTypeRT hbody` field, and no single-level `RTSubstReady ℓ`
  field can cover them.
- Root fact (G31): `HasType.var` constrains args levels **nowhere**, and `HasTypeRT.lam` carries no
  body premise (it must not — G2-session correction), so a closure body's instantiation levels are
  invisible to both well-typedness and the program-level RT invariant until the body is already the
  control.

The G31 verdict: the *level-bounding* architecture cannot witness soundness for these programs even
though soundness is true for them. G31 flagged three untried routes; this plan is route 3 ("type the
looked-up value directly, bypassing the args-level bound") made concrete.

## The rearchitecture

Three coupled changes. The direction of information flow reverses: instead of **grounding closure
bodies at apply time** so a bounded promise can fire, we make the promise wide enough to fire on the
body's *original* static args, and impose the (checkable, inference-aligned) discipline that makes
that promise constructible.

### (1) Floor-conditioned, near-universal readiness in `EnvWf.cons`

Replace the bounded promise

```
∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) → HasTypeV v (s.instantiateV args)
```

by a promise conditioned on a per-binding **floor** `B` (existentially stored; for a `let_poly`
binding, `B = lvl'`, the defn's sublevel):

```
∀ args, (∀ t ∈ args, ∀ l ∈ t.levels,
    l = 0 ∨ l = s.level ∨ (l < B ∧ l ∉ polySchemeLevels Γ)) →
  HasTypeV v (s.instantiateV args)
```

Why `l < B` is the right condition: every generalization level reachable inside the defn derivation
is ≥ its ambient (`noGenAt_of_lt` is literally this fact, already proven), and the defn is typed at
ambient `lvl' = B`. So `l < B` gives `NoGenAt l hdefn` **for free**, which is exactly what the
substitution engine needs per level (see (3)). The `l = s.level` disjunct keeps the legitimate
referencing pattern (`a @ [.var 2 0]` under a level-2 generalization); `l ∉ polySchemeLevels Γ` is
the per-level capture-avoidance for *context* schemes (the analog of today's `PolyAboveFV ℓ`).

This makes V1/V2 (appendix) the consumption-side witnesses: the exact G30/G31 counterexample values
**are** typeable at their fatal instantiations — machine-checked. The old architecture wasn't asking
for something false; it just couldn't route the proof.

### (2) `ArgsDisc` — a static, whole-derivation discipline replacing `HasTypeRT`

New derivation-indexed predicate (NoGenAt-shaped), tentatively `ArgsDisc F h` where `F` assigns each
in-scope binding its floor (rides alongside `Γ`, threaded like the G23 fields; exact carrier is a
spike decision — candidate: floors stored in `EnvWf.cons`/frame clauses, with `ArgsDisc` taking the
Γ-parallel floor list):

- **var/builtin arm**: every arg level `l` satisfies `l = 0 ∨ l = s.level ∨ (l < F(x) ∧
  l ∉ polySchemeLevels Γ \ {s.level})` — definitionally aligned with (1)'s promise condition, so
  var-preservation discharges by direct application, with **no `HasTypeRT`, no grounding**.
- **All other arms recurse — including `lam` and `let_poly` defn bodies.** This is the decisive
  difference from `HasTypeRT`: the condition is *static* (holds of the derivation as written, no
  runtime grounding needed), so recursion into un-applied lambda bodies rejects nothing legitimate.
  Consequently it **is storable on `HasTypeV.closure`** — the entire G27–G31 storability wall
  (Prop-elimination, non-ground `EnvWf.cons`, forward-frame obligations) dissolves, because the
  stored fact never needs re-establishment by substitution at apply time. At the two crux sites, the
  body's `ArgsDisc` is simply the closure's stored field.
- `MStateWf.E` swaps `HasTypeRT hty` → `ArgsDisc … hty`; the `assign`/`arg` frames swap their RT
  fields likewise; `mStateWf_initial`'s entry premise swaps `HasTypeRT h` → `ArgsDisc … h`.

**Satisfiability is structural, not accidental.** The discipline demands each `let_poly` choose its
defn sublevel `lvl'` above the arg levels used at that binding's lookups. `hstrict : lvl < lvl'` is
unbounded above, so floors are free choices (V5, appendix: the G31 program disciplined with
`lvl' = 3`). Nesting is automatically consistent: for a binding `y` inside `x`'s defn,
`floor(y) > ambient(y) ≥ floor(x)` by ambient monotonicity + strictness — inner floors dominate
outer floors with no extra bookkeeping. (Machine-check this as a spike lemma:
ambient-monotonicity is implicit in `noGenAt_of_lt`'s induction.)

### (3) The linchpin lemma: `hasType_substAt_multi`

Generalize `hasType_substAt_le` (`Typing.lean:693`) from the σ-range bound `l = 0 ∨ l = ℓ` to
**per-level** side conditions:

```
theorem hasType_substAt_multi {ℓ} (hℓ : ℓ ≠ 0) (σ : Nat → Ty)
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ (NoGenAt l h ∧ PolyAboveFV l Γ e))
    (hng : NoGenAt ℓ h) (hlt : ℓ ≤ lvl) (hΓ : PolyAboveFV ℓ Γ e) :
    HasType lvl (substCtxAt ℓ σ Γ) e (Ty.substAt ℓ σ τ) (Ty.substAt ℓ σ ε)
```

Rationale: the `{0, ℓ}` bound was **capture-avoidance in disguise** (machine-pinned in the appendix:
V3 shows a σ-range level hitting an inner gen level genuinely captures — `genAtV` arity changes; V4
shows freshness restores the commutation). The two commutations that forced `{0, ℓ}` — pushing
`substAt ℓ σ` past a looked-up scheme's `instantiateV` (var arm) and past an inner `genAtV` (let_poly
arm) — each need only "σ's range levels avoid *that* level", which the per-level `NoGenAt l h ∧
PolyAboveFV l Γ e` supplies. The current lemma is the special case σ-range ⊆ {0, ℓ} (where
`NoGenAt ℓ h`/`PolyAboveFV ℓ` are the existing premises), so the induction skeleton is expected to
carry over arm-by-arm. **This is the single genuinely-new piece of mathematics and the Phase-1
go/no-go gate.**

Where it is used: **only** at readiness construction (the `let_poly` preservation step and its
`EnvWf.cons`/`StackWfE` Assign clauses), via a strengthened `genAtV_closure_ready_value_node` whose
args condition becomes (1)'s floor form — `NoGenAt l hdefn` for `l < lvl'` discharged by
`noGenAt_of_lt`, `PolyAboveFV l` by a per-level `polyAboveFV_of_ctxPolyBd` analog. Companion needed:
`ArgsDisc`-preservation under `substAt` (the readiness-built closure stores a re-typed body whose
`ArgsDisc` field must hold post-substitution — analog of what `hasTypeRT_subst` did; the promise's
own side conditions bound the incoming σ levels, which is what the preservation needs).

There is **no substitution at closure apply at all** anymore — the env-machine binding
(`EnvWf.cons` with `.mono argTy`) already avoids it; the apply-time grounding existed only to
re-establish `HasTypeRT`, which no longer exists.

### (4) Statement change (NEEDS SIGN-OFF)

`soundness`/`soundness_evalR`'s entry premise `HasTypeRT h` is **replaced** by `ArgsDisc … h`. This
is the same spec-refinement class as the authorized G20 strict-sublevel reshape: a restriction to
the derivations a level-based inference actually produces (Rémy-style "generalization levels chosen
fresh/high"), hypothesized at the entry point exactly the way `HasTypeRT h` already is today.
Neither premise implies the other, but both hold for the canonical closed ground programs
(`let id = \x.x in id 5` etc. — re-verify as spike regressions), and `ArgsDisc` — unlike
`HasTypeRT` — is *threadable*. Caveat 5's report entry then documents: nested generalizable lets
are fully supported for args-disciplined derivations, with the G31 witness recorded as why the
fully-unconstrained-args entry premise is not witnessable by any level-bounded invariant.

## Why this is not one of the refuted designs

| Refutation | Why it doesn't apply here |
|---|---|
| G27/G28 (no storable closure field) | Those stored *runtime-conditional* facts (`HasTypeRT`/`RTSubstReady`) needing grounding to consume. `ArgsDisc` is static and recurses into lambda bodies, so the stored field is consumed as-is. |
| G30 (env-groundness ≠ fix; body non-RT with ground env) | We no longer require the body to be RT. The G30 body (`a w` @ `[.var 2 0]`) satisfies `ArgsDisc` directly (`2 < floor(a)` with floor ≥ 3, or `2 = s.level` in the referencing variant). |
| G31 (multiplicity of off-scheme levels; escape into result type) | No single-ℓ anywhere: the promise/discipline conditions are per-level with a per-binding floor. The disciplined derivation for the G31 program is machine-checked (V5); its readiness instances are V2/V6. Escaping-into-result-type is fine — nothing ever needs to ground it. |
| G15/G16 (raise/two-modes wall) | Not needed: no derivation ever has its gen levels relabeled. Floors are chosen at derivation time (hypothesis), not reconstructed by a metatheorem. |
| G5 (NoGenAt-on-RT narrowing) | `NoGenAt` appears only per-σ-level inside the substitution lemma, supplied by `noGenAt_of_lt` from the floor condition — no judgment is strengthened to carry it. |

## Phases

- [ ] **Phase 0 — sign-off.** User approves the entry-premise replacement (§4) and the `ArgsDisc`
      direction. Without this, stop; Caveat 5 stays documented-open per the G1 pause decision.
- [ ] **Phase 1 (spike, go/no-go) — `hasType_substAt_multi`.** Additive, in `Typing.lean` (or a
      spike file first, per the G1 Phase-1 methodology). Prove the lemma; if an arm genuinely
      resists, characterize with a machine-checked counterexample and STOP (that would refute this
      plan's premise, a legitimate outcome — record it like the G-session notes do). Also land the
      ambient-monotonicity/floor-nesting lemma and re-verify the canonical examples
      (referencing program, sequential lets, `id 5`) admit `ArgsDisc`-style derivations —
      permanent regressions à la `section Examples`. **Go/no-go gate for everything below.**
- [ ] **Phase 2 — `ArgsDisc` + readiness keystone.** Define `ArgsDisc` (+ floor carrier decision),
      its inversions, `ctxConv`/`weakenEff` transport, and substAt-preservation companion; strengthen
      `genAtV_closure_ready_value_node` to the floor-conditioned promise. Per-file green, additive.
- [ ] **Phase 3 — runtime re-thread.** `EnvWf.cons` promise swap + floor storage;
      `HasTypeV.closure` gains the `ArgsDisc` body field; `MStateWf.E`/`StackWf*`/frames swap
      RT → `ArgsDisc`; `mStateWf_initial` entry premise swap. Retire `RTSubstReady`/`HasTypeRTAt`/
      `hasTypeRT_subst` (and `HasTypeRT` itself once nothing consumes it) — significant net
      simplification. Like G1's Phases 4-6, this is inseparable from Phase 4 for a green build:
      plan Session-A (non-Soundness cone green) / Session-B (Soundness) the same way.
- [ ] **Phase 4 — Soundness A-engine re-green.** The two crux sites reduce to the mechanical
      5-field `HasTypeV.closure` rebind + supplying the stored `ArgsDisc`; var-preservation swaps
      `inv_var_rt` for the `ArgsDisc` inversion; `let_poly` case supplies the new promise via the
      strengthened keystone. **Preserve the current working-tree `Soundness.lean` diff** — the
      A-engine migration in it is the starting point (see G1 plan's tree-state warning).
- [ ] **Phase 5 — B-engine migration.** Mechanical mirror, but it is still on the *pre-G1* API, so
      it takes both migrations at once (level-native + this plan). Largest pure-grind phase.
- [ ] **Phase 6 — sanity example + report.** Nested-generalizable-let example runs through
      `soundness`; update Caveat 5 in `plan/report/type-soundness-report.md` (closed for
      args-disciplined derivations; G31 witness documented as the reason for the discipline).

## Definition of done

Unchanged from G1: `lake build` + `lake exe spec` 104/104 green, `#print axioms soundness` exactly
`[propext, Classical.choice, Quot.sound]`, no `sorry`, at every commit; never commit a red build
(Phase 3/4 pairing excepted only per the explicitly-authorized Session-A pattern, Soundness.lean
alone red between the paired sessions). Every refuted sub-design gets a machine-checked
counterexample note in `plan/progress/` before abandonment.

## Estimate

Phase 1: 1-2 sessions (the honest risk concentrates here — the var-arm commutation's exact
per-level conditions). Phase 2: 1 session. Phases 3-4: 2-3 sessions (paired). Phase 5: 1-2
sessions. Phase 6: half a session. Total 6-9 sessions, materially faster with live Lean LSP access
(no session in the G1 effort had it; strongly recommended for Phases 3-5).

## Appendix — validation performed for this plan (2026-07-09, HEAD `1d92756d`)

A scratch file with the six keystone checks compiled **clean** (`lake env lean`, exit 0, no sorry,
no axioms added) against the committed tree. Reproduce by saving the block below and running
`lake env lean <file>` from `lean/`:

- **V1** — the G30 counterexample value `Closure "x" x []` typed at
  `(genAtV 1 (α→α)).instantiateV [.var 2 0]` (the off-level instantiation `HasTypeRT` could not
  witness): `HasTypeV` derivation constructed, compiles.
- **V2** — the G31 value `Closure "x" (\y.x) []` typed at
  `(genAtV 1 (α→β→α)).instantiateV [.var 2 0, .var 5 0]` (two independent off-scheme levels, one
  escaping into the result type): compiles. Universal readiness is TRUE at exactly the args that
  refuted every bounded design.
- **V3** — necessity of per-level freshness: substituting `.var 2 0` at level 1 into a scheme body
  with an inner gen level 2 changes `genAtV 2`'s arity 1→2 (capture), `decide`-checked. So the
  `{0, ℓ}` bound really was capture-avoidance; `hasType_substAt_multi` must (and need only) demand
  σ-range levels avoid gen/scheme levels.
- **V4** — sufficiency at instance level: with σ at fresh level 3, arity is stable and the
  `substAt`/`instantiateV` commutation holds, `decide`-checked.
- **V5** — the G31 program admits a **disciplined** derivation: same program, args
  `[.var 2 0, .var 2 1]`, defn sublevel (floor) chosen `lvl' = 3 >` all lookup arg levels;
  full `HasType 1 []` derivation compiles. The escaping level-5 choice was gratuitous.
- **V6** — readiness also covers V5's disciplined instantiation (closure typed at
  `instantiateV [.var 2 0, .var 2 1]`): compiles.

```lean
import Eyg.Types.Runtime

namespace G2Validation

open Eyg.Types Eyg.Ir Eyg.Ir.Tree

abbrev defnA : Ty := .fun (.var 1 0) .empty (.var 1 0)
abbrev defnAB : Ty := .fun (.var 1 0) .empty (.fun (.var 1 1) .empty (.var 1 0))

-- V1
example : (Scheme.genAtV 1 defnA).instantiateV [.var 2 0]
    = .fun (.var 2 0) .empty (.var 2 0) := by decide

theorem v1 : HasTypeV (m := Unit) (.Closure "x" (variable_ "x") [])
    ((Scheme.genAtV 1 defnA).instantiateV [.var 2 0]) := by
  have hinst : (Scheme.genAtV 1 defnA).instantiateV [.var 2 0]
      = .fun (.var 2 0) .empty (.var 2 0) := by decide
  rw [hinst]
  have hbody : HasType (m := Unit) 3 [("x", Scheme.mono (.var 2 0))]
      (variable_ "x") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3) (Γ := [("x", Scheme.mono (.var 2 0))])
      (x := "x") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  exact HasTypeV.closure (lvl' := 3) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody (.refl _)

-- V2
example : (Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 5 0]
    = .fun (.var 2 0) .empty (.fun (.var 5 0) .empty (.var 2 0)) := by decide

theorem v2 : HasTypeV (m := Unit) (.Closure "x" (lambda "y" (variable_ "x")) [])
    ((Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 5 0]) := by
  have hinst : (Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 5 0]
      = .fun (.var 2 0) .empty (.fun (.var 5 0) .empty (.var 2 0)) := by decide
  rw [hinst]
  have hx : HasType (m := Unit) 6
      [("y", Scheme.mono (.var 5 0)), ("x", Scheme.mono (.var 2 0))]
      (variable_ "x") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 6)
      (Γ := [("y", Scheme.mono (.var 5 0)), ("x", Scheme.mono (.var 2 0))])
      (x := "x") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hbody : HasType (m := Unit) 6 [("x", Scheme.mono (.var 2 0))]
      (lambda "y" (variable_ "x")) (.fun (.var 5 0) .empty (.var 2 0)) .empty :=
    HasType.lam (le_refl 6)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hx
  exact HasTypeV.closure (lvl' := 6) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody (.refl _)

-- V3
abbrev dCap : Ty := .fun (.var 1 0) .empty (.var 2 0)

example : (Scheme.genAtV 2 dCap).arity = 1 := by decide
example : (Scheme.genAtV 2 (Ty.substAt 1 (fun _ => .var 2 0) dCap)).arity = 2 := by decide
example : Scheme.genAtV 2 (Ty.substAt 1 (fun _ => .var 2 0) dCap)
    ≠ Scheme.genAtV 2 dCap := by decide

-- V4
example : (Scheme.genAtV 2 (Ty.substAt 1 (fun _ => .var 3 0) dCap)).arity
    = (Scheme.genAtV 2 dCap).arity := by decide

example :
    Ty.substAt 1 (fun _ => .var 3 0)
      ((Scheme.genAtV 2 dCap).instantiateV [.integer])
    = (Scheme.genAtV 2 (Ty.substAt 1 (fun _ => .var 3 0) dCap)).instantiateV
        [Ty.substAt 1 (fun _ => .var 3 0) .integer] := by decide

-- V5
abbrev ΓAB' : Ctx := [("a", Scheme.genAtV 1 defnAB)]
abbrev ΓABw' : Ctx := ("w", Scheme.mono (.var 2 0)) :: ΓAB'

theorem v5_body : HasType (m := Unit) 3 ΓABw'
    (apply (variable_ "a") (variable_ "w"))
    (.fun (.var 2 1) .empty (.var 2 0)) .empty := by
  have haType : (Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 2 1]
      = .fun (.var 2 0) .empty (.fun (.var 2 1) .empty (.var 2 0)) := by decide
  have ha : HasType (m := Unit) 3 ΓABw' (variable_ "a")
      (.fun (.var 2 0) .empty (.fun (.var 2 1) .empty (.var 2 0))) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3) (Γ := ΓABw') (x := "a")
      (s := Scheme.genAtV 1 defnAB) (args := [.var 2 0, .var 2 1]) (ε := .empty)
      (a := ()) (by decide)
    rwa [haType] at h
  have hw : HasType (m := Unit) 3 ΓABw' (variable_ "w") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3) (Γ := ΓABw') (x := "w")
      (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  exact HasType.app ha (Ty.effWeaken_refl _) hw

theorem v5 : HasType (m := Unit) 1 []
    (let_ "a" (lambda "x" (lambda "y" (variable_ "x")))
      (lambda "w" (apply (variable_ "a") (variable_ "w"))))
    (.fun (.var 2 0) .empty (.fun (.var 2 1) .empty (.var 2 0))) .empty := by
  have hx : HasType (m := Unit) 3
      [("y", Scheme.mono (.var 1 1)), ("x", Scheme.mono (.var 1 0))]
      (variable_ "x") (.var 1 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3)
      (Γ := [("y", Scheme.mono (.var 1 1)), ("x", Scheme.mono (.var 1 0))])
      (x := "x") (s := Scheme.mono (.var 1 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hbodydefn : HasType (m := Unit) 3 [("x", Scheme.mono (.var 1 0))]
      (lambda "y" (variable_ "x")) (.fun (.var 1 1) .empty (.var 1 0)) .empty :=
    HasType.lam (le_refl 3)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hx
  have hlamw : HasType (m := Unit) 2 ΓAB'
      (lambda "w" (apply (variable_ "a") (variable_ "w")))
      (.fun (.var 2 0) .empty (.fun (.var 2 1) .empty (.var 2 0))) .empty :=
    HasType.lam (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
      v5_body
  exact HasType.let_poly (by omega)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbodydefn (by intro b hb; cases hb) hlamw

-- V6
theorem v6 : HasTypeV (m := Unit) (.Closure "x" (lambda "y" (variable_ "x")) [])
    ((Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 2 1]) := by
  have hinst : (Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 2 1]
      = .fun (.var 2 0) .empty (.fun (.var 2 1) .empty (.var 2 0)) := by decide
  rw [hinst]
  have hx : HasType (m := Unit) 3
      [("y", Scheme.mono (.var 2 1)), ("x", Scheme.mono (.var 2 0))]
      (variable_ "x") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3)
      (Γ := [("y", Scheme.mono (.var 2 1)), ("x", Scheme.mono (.var 2 0))])
      (x := "x") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hbody : HasType (m := Unit) 3 [("x", Scheme.mono (.var 2 0))]
      (lambda "y" (variable_ "x")) (.fun (.var 2 1) .empty (.var 2 0)) .empty :=
    HasType.lam (le_refl 3)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hx
  exact HasTypeV.closure (lvl' := 3) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody (.refl _)

end G2Validation
```

## Honest open risks (for the spike, not hidden)

1. **`hasType_substAt_multi`'s var-arm commutation** may need its per-level `PolyAboveFV` phrased
   more carefully (per looked-up scheme, not per expression) — medium risk; the induction skeleton
   exists (`hasType_substAt_le`).
2. **Floor carrier plumbing** (how `F` rides with `Γ` through `EnvWf`/frames/`ArgsDisc`) — design
   fiddliness, low mathematical risk; the G23 threading is the template.
3. **`ArgsDisc` preservation under `substAt`** at readiness construction — the promise's own side
   conditions bound the incoming levels, but the interaction with *other* bindings' floors inside
   the defn needs the floor-nesting lemma (§2); if a genuine counterexample appears here, STOP and
   record it — that is this plan's refutation surface.
4. **B-engine** takes two migrations at once; budget it as pure grind, not risk.
