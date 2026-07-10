# G2 B1′ prototype — decoupled `let_poly` validates the fix (Payoff 1 machine-checked)

Date: 2026-07-10. Spike `Eyg/Types/G2DecoupledSpike.lean` (does not touch live `HasType`), builds
clean, axioms `[propext, Quot.sound]`.

## What the prototype shows

`HasTypeD` = minimal declarative typing whose `let_poly` generalizes at a **chosen fresh** level `gl`
(required `CtxFresh gl Γ` — private to the context), **decoupled** from the ambient (body stays at
`lvl`, not `lvl+1`). This is the standard-Rémy shape.

**Payoff 1 (machine-checked, `v8_body_decoupled`).** V8's program types in `HasTypeD` with `g`
generalized at a fresh `gl = 5` while `b`'s body ambient stays low at `2`. The live coupled rule
cannot express this (it forces gen level = ambient — the rigidity that
`plan/progress/2026-07-10-G2-B1-blocked-ruleCoupling.md` proved blocks the V8 relabel). Decoupling
frees the two.

## Payoff 2 (the readiness argument — traced, not yet fully formalized)

Why decoupling delivers *unconditional* readiness, worked on V8:

- Readiness for `b`'s closure at args `[.var 2 0]` re-types the body under `substAt 1` (b's gen level)
  with `.var 2 0`. The **only** capture risk is at an inner gen level equal to an arg level.
- The inner `let g`'s gen level is `gl`, chosen **fresh/private** (`5`), so it never equals a
  use-site arg level (`2`) — no capture. (The inner `\w`'s binder level 3 is untouched: `substAt 1`
  doesn't reach it, and `w`'s type never receives an arg.) So readiness holds with **no raise**.
- Contrast the coupled rule: `g`'s gen level is *forced* to `b`'s body ambient, which can coincide
  with an arg level (V8: both 2) → capture, and the raise can't fix it (interleaving, machine-checked
  `v8_moving_g_moves_retTy` / `v8_fixing_retTy_strands_g`).

The general statement is a `HasTypeD` readiness keystone whose args-condition is **"levels avoid the
(private) inner gen levels"** — *free* by `CtxFresh`, replacing the too-strong `l < lvl'` floor. This
is the crux the floor keystone (`genAtV_instantiate_lam_ready_floor`, already proven for `HasType`)
would satisfy trivially once gen levels are private.

## Cost of finishing / the real decision

Fully proving Payoff 2 in `HasTypeD` means reproving the substitution/readiness cone (`substAt`,
`instantiateV_genAtV_*`, the keystone) for the new inductive — comparable in size to **migrating the
live judgment** to the decoupled rule. So the prototype has done its job: it **confirms decoupling is
the correct, sufficient mechanism** (Payoff 1 machine-checked; Payoff 2 traced and reduced to a
free-by-construction side condition).

**The real next step is the live-rule migration** (`HasType.let_poly` → chosen-fresh `gl`), which is a
**judgment change needing sign-off**: it widens which derivations exist, and every downstream lemma
(Generation, Substitution, Runtime `EnvWf`, Soundness) must be re-checked. The upside: it delivers the
*unconditional* soundness the user asked for, matches standard Rémy, and — per the trace above — makes
the existing floor keystone discharge readiness with no raise and no `ArgsDisc`.

Recommended: scope the migration as its own plan (rule change + downstream re-check), get sign-off on
the `let_poly` statement change, then execute. The prototype + V1–V8 + the keystones are the
foundation it builds on.
