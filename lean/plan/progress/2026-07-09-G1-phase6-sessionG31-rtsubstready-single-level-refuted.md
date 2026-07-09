---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G31". Refutation session: the *authorized* single-level
  `RTSubstReady ℓ hbody`-on-`HasTypeV.closure` field is disproved by a machine-checked counterexample.
  No code landed (correctly — the authorized change is proven unworkable; salvaging needs a materially
  larger, different core redesign requiring fresh sign-off).
status: STOP + FLAG. Soundness.lean byte-identical to session start (diff -q vs
  /tmp/Soundness-backup-1783631690.lean IDENTICAL). A-engine red at exactly the 2 closure-apply crux
  sites 874-877 / 1036-1039; B-engine un-migrated >= 2460. No `sorry` anywhere. HEAD c1800acb.
  Caveat 5 OPEN.
kind: progress
component: lean
---

# G1 Phase 6 (Session G31): the authorized single-level `RTSubstReady ℓ hbody` field is refuted; the obstruction is a *multiplicity* of independent off-scheme instantiation levels that no single `ℓ` covers

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` unavailable). Read/Grep +
`lake env lean` scratch (`decide` + explicit `HasType`/`HasTypeRT` derivations). HEAD `c1800acb`.
**Fresh, specific user authorization this session for the `RTSubstReady ℓ hbody` field on
`HasTypeV.closure`** (replacing the G30-refuted `HasTypeRT hbody` + `EnvWf`-groundness design) — that
exact single-level change is proven unworkable below. NO source edits; working tree preserved
byte-identical (`diff -q Eyg/Types/Soundness.lean /tmp/Soundness-backup-1783631690.lean` IDENTICAL).
`grep -rn sorry Eyg/Types/*.lean` empty.

## Confirmed error state (unchanged from G26–G30)

`lake env lean Soundness.lean`: A-engine errors ONLY at the two closure-apply crux sites (874-877 /
1036-1039): `cases hf with | closure henvc hbody heqc` under-binds the 5-field `HasTypeV.closure`, and
the `.E` `refine` omits `lvl,hlvl` + the `HasTypeRT hty` slot of `MStateWf.E`. Everything >= 2460 is
the deliberately un-migrated B-engine. No regressions.

## The task and the result

Task (per G30's flag, freshly authorized): add `RTSubstReady ℓ hbody` (single stored level `ℓ` =
closure-domain top level) to `HasTypeV.closure`, supply it at every construction site (esp. the
plain-lambda-eval site the CE class targets), consume it at the two crux sites via `hasTypeRT_subst`,
close the crux. **Result: the design is REFUTED by a machine-checked counterexample. A single-level
`RTSubstReady ℓ` cannot be constructed at plain-lambda-eval for a reachable, `HasTypeRT`, closed
program, because the closure body legitimately instantiates a captured MULTI-parameter scheme at TWO
independent off-scheme levels, and one `ℓ` covers only one of them.**

## Root fact: `HasType.var` constrains `args` levels NOWHERE

`Typing.lean`:
```
| var {lvl Γ x s args ε a} :
    Γ.lookup x = some s → HasType lvl Γ ⟨.Variable x, a⟩ (s.instantiateV args) ε
```
`args` is entirely free — any list of `Ty`. So a well-typed var node may instantiate a scheme at
arbitrary levels. The whole-program `HasTypeRT` invariant bounds var args by `{0, s.level}`, but
`HasTypeRT.lam` carries NO body premise (Typing.lean ~972), so it never reaches instantiations UNDER a
lambda. Hence a closure body's instantiation levels are unconstrained by both well-typedness and
program-level RT. `RTSubstReady ℓ` is therefore a genuine extra obligation whose var arm demands
`args` levels subset of `{0, ℓ, s.level}` — and this can fail for every single `ℓ`.

## The counterexample (machine-checked; every `def`/`example` compiled via `lake env lean`)

Program `let a = \x.\y.x in (\w. a w)` — the BARE outer let-body form.

- **`a : ∀αβ. α→β→α`**, `defnAB := (.var 1 0) → (.var 1 1) → (.var 1 0)`, generalized at level 1
  (`genAtV 1 defnAB`).
- **Body `a w`** instantiates `a` at `args = [.var 2 0, .var 5 0]`:
  - `(genAtV 1 defnAB).instantiateV [.var 2 0, .var 5 0]
     = .var 2 0 → .var 5 0 → .var 2 0` (`decide`-verified).
  - First arg `α := .var 2 0` is FORCED by `w`'s domain `.var 2 0` (level 2).
  - Second arg `β := .var 5 0` is FREE (level 5): `β` does not appear in `a w` (which has type
    `β→α`), so it is unconstrained — chosen at an independent level 5.
  - `def hbodyAB : HasType 3 ΓAB (apply a w) (.var 5 0 → .var 2 0) .empty` — COMPILED.
- **The whole closed program type-checks:** `def progAB : HasType 1 []
  (let_ "a" (lambda "x" (lambda "y" x)) (lambda "w" (apply a w)))
  (.var 2 0 → (.var 5 0 → .var 2 0)) .empty` (let_poly generalizing `a` at level 1; defn `\x.\y.x` at
  sublevel 2; body `\w. a w` at sublevel 2, its body `a w` at level 3) — COMPILED.
- **It is `HasTypeRT`:** `example : HasTypeRT (HasType.lam … hbodyAB) := HasTypeRT.lam …` — COMPILED
  (the closure-creating lambda's RT is body-premise-free, so the whole program's RT holds regardless of
  `a w`'s off-level args — identical to G30's Typing.lean:2295 machine-verified single-param pattern).
- **The closure is created DIRECTLY at top-level plain-lambda-eval** (Soundness ~213): the program
  evaluates `a` to a closure, then evaluates `\w. a w` to `Closure "w" (a w) [(a,…)]` — NO prior
  application to ground anything. So the `RTSubstReady ℓ hbody` field MUST be constructed here.
- **It cannot be — the `RTSubstReady.var` side-condition is unsatisfiable for every `ℓ`:** for the
  `a`-node, `s.level = 1`, `args = [.var 2 0, .var 5 0]`, so the condition is
  `∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = ℓ ∨ l = 1`, i.e. `(ℓ = 2) ∧ (ℓ = 5)`. Machine-checked:
  `example : ∀ ℓ : Nat, ¬ (∀ t ∈ [(.var 2 0), .var 5 0], ∀ l ∈ t.levels, l=0 ∨ l=ℓ ∨ l=1) := … omega`
  — COMPILED. G30's `ℓ`-disjunct admitted ONE off-scheme level (`a @ [.var 2 0]`); this witness has TWO
  independent ones, and a single stored `ℓ` covers at most one.

## Why the deeper `HasTypeRT`-at-E-state invariant is *also* incompatible (design-fatal, not just this field)

Even a hypothetical multi-level readiness (a SET/list `L` of grounding levels, iterated
`hasTypeRT_subst`) does not rescue the consume side: level 5 ESCAPES into the closure's result type
`.var 5 0 → .var 2 0`. Applying the closure to a `w`-value grounds only level 2 (the domain the argument
instantiates); the re-typed body `a @ [ground, .var 5 0]` still fails `HasTypeRT.var`'s `{0, s.level}`
bound (`5 ∉ {0, 1}`). So `HasTypeRT hbody` — the ACTUAL `MStateWf.E` requirement at the crux — is
genuinely unachievable for this reachable closure regardless of the field predicate. Equivalently, when
`a w` is evaluated, the `Variable` preservation case (Soundness ~216, `inv_var_rt hrt`) needs
`hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level` to type the looked-up value at
`s.instantiateV [ground, .var 5 0]`, and the `EnvWf.cons` poly-readiness clause only promises typing for
`{0, s.level}`-bounded args — neither admits the escaping level 5. The value `\x.\y.x` genuinely DOES
inhabit `integer → .var 5 0 → integer` (it is truly polymorphic and ignores the second arg's type), so
soundness itself is TRUE for this program; the gap is that the `{0, s.level}`-bounded `HasTypeRT`
invariant (and the matching readiness bound) cannot WITNESS it. This is a limitation of the whole RT
architecture accumulated across Phase 6, surfaced by this multiplicity/escape witness.

## Decision: STOP and flag (again), do not force, do not narrow soundness

Per the closing-session brief ("if you find ANY construction site genuinely cannot supply `RTSubstReady`
— a real counterexample, not just difficulty — STOP immediately; do not force it or narrow soundness"):

- The **authorized** change (single-level `RTSubstReady ℓ hbody` on `HasTypeV.closure`) is proven
  unconstructible at plain-lambda-eval for a reachable, `HasTypeRT`, closed program.
- Any **workable** change is materially larger and different: a multi-level readiness predicate AND a
  relaxation of the E-state RT invariant + `EnvWf.cons` readiness bound to admit escaping non-ground
  instantiation levels — or a rethink of whether `HasTypeRT`-at-E-state is the right invariant at all.
  This is well beyond the authorized closure field.

So: no source edit landed; tree preserved byte-identical; requesting fresh authorization / a design
decision for the broader change.

## Open questions for the next (broader-authorization) session

1. **Is the escaping-free-level class avoidable by construction?** e.g. does the inference/elaboration
   that PRODUCES the machine's initial derivation ever emit escaping-level instantiations, or only the
   declarative `HasType`? If soundness is only required for *inferred* derivations with a
   "no-escaping-free-var" normal form, a normalization pre-pass (bounding all instantiation levels by the
   ambient/exposed levels) could restore the invariant — but that is a statement-adjacent restriction
   needing sign-off, and must be checked against `soundness`'s current (fully declarative) hypothesis.
2. **Multi-level `RTSubstReadySet L` + relaxed E-state RT.** Define readiness over a set of levels;
   relax `HasTypeRT.var`/`EnvWf.cons` to bound args by `{0, s.level} ∪ (exposed/result-type levels)`;
   check whether preservation still closes (the escaping level then lives in the tracked exposed set at
   every step). Large: touches Typing (RT invariant), Runtime (`EnvWf.cons`, `HasTypeV.closure`),
   Machine (`StackWfE`), both Soundness engines.
3. **Whether `HasTypeRT` is the right E-state companion at all** — the recurring failure across
   G27–G31 is always the var-args bound at a re-entered closure body; a fundamentally different
   value-lookup soundness argument (typing the looked-up VALUE directly against the arbitrary
   instantiation, bypassing the args-level bound) may be the real fix.

## Tree state at stop

No commit of source; no source edit. `Soundness.lean` byte-identical to session start (`diff -q` vs
`/tmp/Soundness-backup-1783631690.lean` IDENTICAL). `plan.md` gains a Session-G31 entry; this note
added (doc-only). `grep -rn sorry Eyg/Types/*.lean` empty; HEAD `c1800acb`. Caveat 5 OPEN. Scratch CE
file (`scratch_ce.lean`) compiled clean then deleted; its content is reproduced above in full.
