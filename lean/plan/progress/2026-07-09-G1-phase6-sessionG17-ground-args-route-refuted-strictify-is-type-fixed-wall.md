---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G17". Verified (against the exact source, not the note's
  prose) that the G16-recommended "restrict EnvWf.cons to ground args, discharge via hasType_fullRaise"
  route is a MISDIAGNOSIS: ground args do NOT avoid the wrapper's `NoGenAt lvl hbody` obligation, which
  reduces to the type-FIXED freshening (`hasType_strictify`) — the G13–G15 two-modes wall, still open.
  No soundness-narrowing tightening shipped (it would not help). Nothing committed to Eyg/Types code.
status: PARTIAL / analysis. The recommended route refuted with a source-level argument; the real
  bottleneck re-pinned precisely and the escLam mechanism's non-generalization made explicit. Caveat 5
  OPEN. Full green NOT reached. Soundness.lean left EXACTLY as found (pre-existing partial migration).
kind: progress
component: lean (analysis only — no code change)
---

# G1 Phase 6 (Session G17): the ground-args route refuted at the source; strictify = type-fixed wall

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake env lean`
scratch. The task asked to (1) pin what "ground/bounded args" must mean for
`Scheme.instantiateV_genAtV_raiseTy`'s identity case, (2) tighten `EnvWf.cons`/`StackWf*` to those args,
(3) rewire `genAtV_closure_ready_value_node` off `NoGenAt` via `hasType_fullRaise`, and — explicitly —
to STOP and document if the tightening is a soundness-narrowing change in disguise. It is worse than
narrowing: **it does not help at all.** Verified against the exact judgments, not the note's prose.

## Step 1 (as instructed): what `HasTypeRT` ACTUALLY guarantees vs what the note assumed

`HasTypeRT.var`'s groundness (`Typing.lean:835`) is **`∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level`**
— i.e. `⊆ {0, s.level}`, which for the closure scheme `genAtV lvl defnTy` (`s.level = lvl`) **admits
level `lvl` args**, not merely ground `{0}` ones. The G16 note (and this task's step 1) assumed runtime
args are "ground (⊆ {0})"; the actual invariant permits the escaped level-`lvl` tag. This is exactly the
current `EnvWf.cons` precondition (`Runtime.lean:218`) — they already match, which is why gap-1 wiring
(`inv_var_rt` → `envwf_lookup`) landed. So the note's premise for the identity case is not what
`HasTypeRT` establishes.

## Step 2/3: ground args do NOT avoid the wrapper's `NoGenAt` — two independent source-level reasons

The wrapper `genAtV_closure_ready_value_node` (`Substitution.lean:167`) needs
`HasTypeV (Closure) ((genAtV lvl defnTy).instantiateV args)`. Its only `NoGenAt`-free keystone is
`genAtV_instantiate_lam_ready` (`Typing.lean:443`), whose signature **requires `hlt : ℓ < lvl'`**
(strict body sublevel). The non-strict `..._le` variant (`Typing.lean:688`) fills `lvl' = lvl` but
**requires `NoGenAt ℓ hbody`** (`hasType_substAt_le`, `Typing.lean:584`, consumes it as the `let_poly`
arm's `hne`). Therefore:

- **(a) `lvl'` is body-derivation-determined, arg-INDEPENDENT.** Restricting the readiness args to ground
  cannot supply `ℓ < lvl'` when the derivation the runtime hands us has `lvl' = lvl`. Ground-ness of the
  instantiation args has no bearing on the body sublevel.
- **(b) Padding reintroduces level `lvl` even for ground args.** `Scheme.instantiateV` pads short args
  with `var lvl i` (level `lvl`); the substitution `σ i = args.getD i (var lvl i)` in
  `genAtV_instantiate_lam_ready_le` is level-`lvl`-carrying regardless of how ground `args` is — so the
  `substAt lvl` re-typing of the body still needs `NoGenAt lvl hbody`.

So the obstruction is **body-structural** (`hbody` contains an inner `let_poly` at exactly `lvl`, with
`lvl' = lvl`), NOT args-based. Tightening `EnvWf.cons` to ground args changes nothing about it. (And if
the runtime genuinely never supplies level-`lvl` args, tightening `HasTypeRT.var`/`EnvWf.cons` to match
would be sound — but pointless, since it does not unlock the discharge.)

## Why `hasType_fullRaise` (the G16 deliverable) cannot discharge the wrapper for ANY args

`NoGenAt lvl` of the un-freshened `hdefn` is genuinely UNPROVABLE for that derivation: a `let_poly` node
at ambient `lvl` generalizes at `lvl` (`HasType.let_poly` uses `genAtV lvl`), and `NoGenAt.let_poly`
(`Typing.lean:531`) requires `lvl ≠ ℓ`. So `NoGenAt lvl` of a lambda whose body sublevel `lvl' = lvl` and
whose body is a `let_poly` (ambient `lvl`) is impossible **for that derivation**; it is reachable only by
proof-irrelevance from an ALTERNATIVE derivation of the *same judgment* with body sublevel `lvl' > lvl`
(so the inner `let_poly` sits at ambient `> lvl`, and `noGenAt_of_lt` fires). This is exactly what
`escLam_lvl1_noGenAt := escLam_lvl2_noGenAt` (`Typing.lean:2113`) does by hand.

Producing that alternative derivation generally is `hasType_strictify : ∀ h, ∃ h', NoGenAt lvl h'` with
`lvl,Γ,τ,ε` **FIXED** — the **type-fixed** freshening. `hasType_fullRaise` is the **uniform** raise: it
moves the inner `let_poly` at `lvl` to `lvl+o`, but it ALSO moves the escaped level-`lvl` vars in `retTy`
to `lvl+o` (they are the inner gen's generalized vars, surfaced via instantiation), **changing** the
judgment's type to `raiseTy lvl o defnTy`. Instantiating the raised scheme
`genAtV (lvl+o) (raiseTy lvl o defnTy)` to recover the original type then requires readiness of the
**raised** closure at level `lvl+o` — where the inner `let_poly` (moved to `lvl+o`) collides with the
raised generalization (also `lvl+o`) exactly as before. **The raise recreates the identical collision at
the top level `lvl+o`; it provides zero net help.**

## The escLam mechanism (type-fixed, level-`lvl` re-instantiation) and why it does not generalize

`escLam_lvl2` (`Typing.lean:2095`) DOES the type-fixed freshening for the residual escape corner: it
moves the inner `let_poly` `1 → 2` while re-instantiating its use at the **same** `[var 1 0, var 1 0]`
(level 1), so `retTy = escRetTy = (var 1 0 → var 1 0)` stays **fixed** (`escH_body` — instantiation
recovers the escaped var at the fixed level 1 for **any** inner gen level `n`). This is the type-fixed
mode's escaped-var re-instantiation working concretely — but only because the inner defn is a **leaf**
(`\z.z`, re-derived fresh at level `n` by `escH_defn n`). For a **non-leaf** inner defn the type-fixed
re-typing at the freshened level is precisely the type-fixed derivation raise the whole G7–G15 arc walled
on (G13's foreign-`≥ t`-level fork; G15 machine-confirmed). A ground-args recovery lemma
`(genAtV (ℓ+o) (raiseTy ℓ o d)).instantiateV args = (genAtV ℓ d).instantiateV args` (args `< ℓ`, `d ≤ ℓ`,
full-length) IS provable from `instantiateV_genAtV_raiseTy` (scaffolded green this session) — but it is
the **ground-monomorphizing** freshening, NOT escLam's **level-`ℓ`** (`var 1 0`) re-instantiation, so it
does not keep `defnTy` fixed and does not discharge the wrapper. The two flavors are the two modes.

## Verdict and recommended next step

The G16 "ground-args restrict `EnvWf.cons`" route is **refuted**: ground args neither fire the identity
case cleanly (padding + `HasTypeRT`'s real `{0, lvl}` bound) nor bypass the body-structural
`NoGenAt lvl hbody` obligation, and `hasType_fullRaise` cannot supply that obligation because the uniform
raise moves the escaped `retTy` tags (changing the judgment) and re-collides at the top. **No tightening
shipped** — it would not help, and per the task's discipline a non-helping soundness-critical refactor is
not landed.

The genuine remaining target is unchanged from G15's recommendation and is genuine open metatheory: the
**type-fixed** `hasType_strictify` (equivalently the type-fixed derivation raise keeping `Γ,τ,ε` fixed),
whose escaped-var re-instantiation escLam demonstrates for leaf inner defns but which needs, for non-leaf
inner defns, either (i) an invariant that a `let_poly`'s `defnTy` never nests a foreign cross-level
`let_poly` (so single-level `substAt` = uniform `raiseTy` via `raiseTy_eq_substAt_of_single`; may be
false), or (ii) a genuine mutual (relabel-free-level-`t`-tags ⋈ strictify-inner-`let_poly`) induction with
derivation-structural `termination_by`. Both want live LSP goal-state, multi-session. Caveat 5 OPEN.

## Tree state at stop

- HEAD advanced only by this doc/plan commit; no Eyg/Types code touched.
- Soundness.lean left EXACTLY as found (pre-existing uncommitted partial migration, untouched).
- No `sorry` anywhere in `Eyg/Types/*.lean`. Axioms unchanged. Caveat 5 OPEN; full green NOT reached.
