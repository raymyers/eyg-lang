---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G30". Refutation session: the G29 env-groundness design
  is disproved by a machine-checked counterexample. No code landed (correctly — the authorized change
  is proven unworkable; the workable alternative is a DIFFERENT strengthening requiring fresh sign-off).
status: STOP + FLAG. Soundness.lean byte-identical to session start (backed up /tmp/Soundness.backup.lean,
  diff -q IDENTICAL). A-engine red at exactly the 2 closure-apply crux sites 874-877 / 1036-1039;
  B-engine un-migrated ≥ 2460. No `sorry` anywhere. HEAD a644b934. Caveat 5 OPEN.
kind: progress
component: lean
---

# G1 Phase 6 (Session G30): the G29 env-groundness / unconditional-`HasTypeRT`-field design is refuted; the constructible field is `RTSubstReady`-conditional (a different, unauthorized strengthening)

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` unavailable). Read/Grep +
`lake env lean` scratch (`decide`). HEAD `a644b934`. **Fresh, specific user authorization this session
for the `HasTypeRT hbody` field on `HasTypeV.closure` + an `EnvWf`-groundness invariant** — that exact
change is proven unworkable below. NO source edits; working tree preserved byte-identical
(`diff -q Eyg/Types/Soundness.lean /tmp/Soundness.backup.lean` IDENTICAL). `grep -rn sorry Eyg/Types/*.lean`
empty.

## Confirmed error state (unchanged from G26–G29)

`lake env lean -DmaxErrors=200 Soundness.lean`: A-engine errors ONLY at 874-877 and 1036-1039 (the two
closure-apply crux sites: `cases hf with | closure henvc hbody heqc` under-binds the migrated 5-field
`HasTypeV.closure`, and the `.E` `refine` omits `lvl,hlvl` + the `HasTypeRT hty` slot of `MStateWf.E`).
Everything ≥ 2460 is the deliberately un-migrated B-engine (`StackWfB`/`StackWfEB` etc.). No regressions.

## The task and the result

Task: design the env/context-groundness invariant that G29 claimed would make `HasTypeRT hbody`
constructible at the plain lambda-eval site (Soundness ~211-215), thread it onto `EnvWf`/`HasTypeV.closure`,
close the crux. **Result: the design is REFUTED by a machine-checked counterexample. env-groundness is
not the missing invariant; the unconditional `HasTypeRT hbody` field is not constructible at all.**

## The counterexample (machine-checked, `lake env lean` + `decide`)

Program `let a = \x.x in \w. a w` — crucially the BARE outer let-body form, NOT the canonical
`let a = \x.x in (let c = \w. a w in c)` of `section Examples`. Here `\w. a w` is the OUTER poly-let's
**body**, not a poly-let **defn**.

- **It type-checks:** `HasType (m:=Unit) 1 [] (let_ "a" (lambda "x" x) (lambda "w" (apply a w)))
  (.fun (.var 2 0) .empty (.var 2 0)) .empty` — poly-let `a` generalized at level 1
  (`genAtV 1 (α→α)`, α at level 1), body `\w. a w` typed via `HasType.lam` at ambient level 2, its body
  `a w` at level 3 under `[(w,.mono(.var 2 0)),(a,genAtV 1 (α→α))]`, `a` instantiated at `args=[.var 2 0]`
  (level 2). (This is the exact `hbody_ref`/`Γc`/`cRefBody` shape of Typing.lean `section Examples`,
  reused verbatim.) `example` compiled clean.
- **`\w. a w` is reached as a PLAIN lambda-eval control:** the poly-let binds `a` to its closure, then
  evaluates the body `\w. a w` as an E-state ⇒ `Lambda` case (Soundness 211-215) ⇒ builds
  `HasTypeV (Closure "w" (a w) [(a, Closure "x" x [])])`. This is NOT the readiness-function path (that
  fires only for poly-let *defns*, here `\x.x`).
- **The `HasTypeRT hbody` field is not constructible there:** it needs `HasTypeRT` of `a w`, whose
  `var`-arm side-condition for the `a` node (`s := genAtV 1 defnA`, `s.level = 1`, `args := [.var 2 0]`)
  is `∀ t ∈ [.var 2 0], ∀ l ∈ t.levels, l = 0 ∨ l = s.level`, i.e. `2 = 0 ∨ 2 = 1`. `decide` proves this
  **FALSE**.
- **env-groundness cannot help:** the captured env `[(a, Closure "x" x [])]` is *fully ground* (`a` is a
  closed value), yet the obstruction is in the body's *static* instantiation levels `[.var 2 0]`, entirely
  independent of the runtime env. So NO property of `env`/`Γ` can make `HasTypeRT hbody` hold. **G29
  Result 3 is wrong.**

Where G29 went wrong: G29 Result 1 ("crux needs only `HasTypeRT hbody`") surveyed only the witnesses
`\u.\w. a u` and `\x.(let h=\z.z in h)`, BOTH of which instantiate their captured var *at its own scheme
level* (`a @ [.var L1 0]`, `a.level=L1`; `h @ [.var lvl' 0]`, `h.level=lvl'`) and so ARE `HasTypeRT`. It
missed the *off-level* instantiation `let a=\x.x in \w. a w` (`a` @ level 2 ≠ `a.level`=1), where the
plain-control closure body is genuinely non-`HasTypeRT`. The witness survey was incomplete.

## Why the field is still the right HOME, but must be CONDITIONAL (`RTSubstReady`, not `HasTypeRT`)

The non-`HasTypeRT` closures have domain `.var 2 0` — an *uninstantiated* type variable. Such a closure
can only be APPLIED once the surrounding context instantiates its domain to something ground (there is no
closed runtime value at type `.var 2 0`). The substitution σ that produces an argument value simultaneously
grounds the very level (here 2) that broke `HasTypeRT`. Machine-checked corroboration: the SAME `a @
[.var 2 0]` node that fails `HasTypeRT.var` SATISFIES `RTSubstReady 2`'s var side-condition
`∀ l ∈ {2}, l = 0 ∨ l = ℓ=2 ∨ l = s.level=1` — `decide`-**TRUE**. So:

- **Constructible-at-lambda-eval field:** `RTSubstReady ℓ hbody` at `ℓ = the closure domain's top level`
  (here 2). The `RTSubstReady.var` `l = ℓ` disjunct admits exactly the off-level args `HasTypeRT` rejects.
- **Discharge at the crux:** `hasTypeRT_subst hℓ σ hσ (RTSubstReady ℓ hbody) …` with the apply-supplied
  ground σ ⇒ `HasTypeRT (re-typed body)` (the G25 infra, already complete, does exactly this).

This **resurrects the G6-G27 `RTSubstReady`-on-closure line** that G28/G29 declared a "detour"/"relocation."
That line had the right predicate; it was abandoned on G29's incomplete witness survey. `RTSubstReady` and
`hasTypeRT_subst` are NOT dead infra — they are precisely what the closure field needs.

## Decision: STOP and flag for authorization

Per the closing-session brief ("if it requires yet another distinct judgment-strengthening beyond what's
authorized here, STOP and flag it for further authorization rather than proceeding"):

- The **authorized** change was: unconditional `HasTypeRT hbody` field on `HasTypeV.closure` + an
  `EnvWf`-groundness invariant. **Both are proven unnecessary/unworkable** — the field can't be built, and
  groundness can't fix it.
- The **workable** change is: an `RTSubstReady ℓ hbody` (conditional) field on `HasTypeV.closure`, at
  ℓ = the closure-domain top level, with NO `EnvWf`-groundness invariant. This is a *materially different*
  runtime-judgment strengthening than the one signed off.

So: no source edit landed; tree preserved byte-identical; requesting fresh authorization for the
`RTSubstReady ℓ hbody`-on-`HasTypeV.closure` design.

### Open sub-questions for the RTSubstReady-field design (next session, once authorized)

1. **Exact ℓ.** Candidate: the top (max) level appearing in the closure's domain `argTy` (the level a
   ground argument's σ must eliminate). Confirm it is well-defined and ≥ 1 for every closure that can be
   applied; for fully-ground-domain closures (mono, ground argTy) the body is already `HasTypeRT` and
   `RTSubstReady` holds trivially at any ℓ.
2. **Constructibility at plain lambda-eval.** `RTSubstReady ℓ hbody` from `hty`/`inv_lambda` + the closure
   domain level. The `RTSubstReady.lam`/`.let_poly` arms carry `NoGenAt ℓ` obligations on nested
   bodies/defns — check these are dischargeable via `noGenAt_of_lt` at lambda-eval (the ambient level vs ℓ
   relation).
3. **Crux discharge.** Confirm the applied argument's type at the crux is ground (σ with `∀ l ∈ (σ i).levels,
   l = 0`), i.e. the apply genuinely supplies a ground instantiation of the closure domain, so
   `hasTypeRT_subst` fires. Plus the two small Soundness-local wrappers `hasTypeRT_conv`/`hasTypeRT_weakenEff`
   to peel the crux's `conv`/`weakenEff`.
4. **Field preservation across the readiness function** (`genAtV_closure_ready_value_node`): the materialized
   closure re-types the body at ground args via `substAt`; produce `RTSubstReady ℓ'` of the re-typed body
   (or directly `HasTypeRT`, which implies `RTSubstReady` trivially).
5. **B-engine mechanical migration** (≥ 2460): entirely un-migrated to even the CURRENT `MStateWf.E`
   (lvl/hlvl/hrt) and 5-field `HasTypeV.closure`; a large separate mechanical job after the A-engine closes.

## Tree state at stop

No commit; no source edit. `Soundness.lean` byte-identical to session start (`diff -q` vs
`/tmp/Soundness.backup.lean` IDENTICAL). `plan.md` gains a Session-G30 entry; this note added. `grep -rn
sorry Eyg/Types/*.lean` empty; HEAD `a644b934`. Caveat 5 OPEN. G25 substitution infra intact and now shown
to be exactly what the (revised) closure field needs.
