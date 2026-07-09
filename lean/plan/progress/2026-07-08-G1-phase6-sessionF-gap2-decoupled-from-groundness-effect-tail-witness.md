---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 6 "Session F". Attempted the combined `HasTypeRT` + wrapper landing
  (steps 1-4) with no LSP. Discovered — and machine-checked — that the `genAtV_closure_ready_value`
  wrapper strictness gap and the var-preservation runtime-groundness blocker are **NOT the same
  obstruction** (correcting Session E's central conjecture): the strictness gap has a reachable,
  FULLY GROUND instance no groundness invariant excludes. Landed a permanent in-code witness of it in
  the green `Typing.lean`; sharpened the true fix. Full green NOT reached.
status: LANDED (one additive commit — the effect-tail strictness witness in `Typing.lean`, per-file
  green). Working tree: `Soundness.lean` still uncommitted (as-found Session-C/D partial migration,
  UNCHANGED this session). Every other file green per-file.
kind: progress
component: lean (Types.Typing — witness landed; Types.Substitution/Soundness — analysis)
---

# G1 Phase 6 (Session F): the wrapper strictness gap is DECOUPLED from runtime groundness

No LSP/MCP tools this session (canary failed: only Read/Grep/Edit + `lake env lean`/`lake build`).
Per plan guidance this constrained the session away from the blind 24-constructor `HasTypeRT` mirror +
4278-line two-engine grind (every prior session flagged those as needing live goal-state). Instead the
session did what batch tooling is good for: it **tested Session E's central conjecture with a concrete
derivation** and found it false, which redirects the whole remaining plan.

## The finding (machine-checked): gap 2 is reachable AND ground

Session E's Recommendation for Session F was: "land the wrapper as part of introducing `HasTypeRT` —
its arity≠0 branch's `hlt : ℓ < lvl'` should come from the runtime-restricted derivation ... they are
the same obstruction." **This is wrong.** Counterexample (now a permanent example in `Typing.lean`'s
`section Examples`, builds green):

```
defnPerf := integer →⟨op:(integer,integer) | μ⟩ integer     -- μ = var 1 0  (level 1)
\x. perform "op" x   :   HasType 1 [] (…) defnPerf .empty     -- via HasType.lam (lvl' := 1) …
(Scheme.genAtV 1 defnPerf).arity ≠ 0                          -- by decide (the μ occurrence)
```

- The lambda types at ambient level `1` with **body sublevel `lvl' = 1`**: `HasType.lam` requires only
  `lvl ≤ lvl'` and `∀ l ∈ argTy.levels, l < lvl'`; here `argTy = integer` is ground so the second
  premise is vacuous and `lvl'` is **not forced above `lvl`**. So `lvl' = ℓ = 1` (non-strict).
- Generalizing at `ℓ = lvl = 1` gives `genAtV 1 defnPerf` with **`arity ≠ 0`**, because level `1`
  occurs in `defnPerf.levels` — via the **effect tail `μ = var 1 0`**, generalizable exactly like any
  row variable (correct value-restricted HM behavior).
- So the wrapper's arity≠0 branch fires with `ℓ = lvl' = 1`, and
  `genAtV_closure_ready_value`'s `hlt : ℓ < lvl'` (strict) is **unavailable**.
- **The derivation is fully ground.** The only `.Variable` node is `HasType.var (s := .mono integer)
  (args := [])`; the level-`1` tag comes from the `perform` rule's freely-chosen effect tail `μ`, NOT
  from any instantiation argument. A runtime-groundness invariant (`HasTypeRT`, which bounds only
  `var`/`builtin` args to `l = 0 ∨ l = s.level`) says **nothing** about `μ`. So `HasTypeRT` does not
  close this case.

Hence gap 1 (var-preservation) and gap 2 (wrapper strictness) are **independent** obstructions, and
`\x. perform "op" x` (a runtime-reachable closure) inhabits gap 2 without touching gap 1.

## Why `hlt : ℓ < lvl'` is needed at all — and the true fix

Tracing `hasType_subst` (`Typing.lean`): the strict `ℓ < lvl` (equivalently `ℓ ≠ lvl` on the current
ambient) is consumed in **exactly one arm** — `let_poly`, as `hne : ℓ ≠ lvl` (the opening level must
differ from the node's generalization level, so `substAt ℓ` never touches the generalized region). The
`lam`/`let_`/`app`/atomic arms need only `ℓ ≤ lvl` (they recurse with `ℓ ≤ lvl'`, `hle : lvl ≤ lvl'`).

So the wrapper's conclusion **is true** even for the ground `\x. perform "op" x` case (its body has no
`let_poly` at all, so `substAt 1` into it is harmless — indeed the `perform` rule is *already*
polymorphic in `μ`, so re-typing at the instantiated `μ` is immediate). The strict `ℓ < lvl'` is a
**proof artifact of `hasType_subst`'s uniform induction**, not a soundness requirement.

**The correct fix (orthogonal to `HasTypeRT`):** a `hasType_subst` variant with precondition `ℓ ≤ lvl`
(non-strict) plus a **derivation-level side condition** "no `let_poly` reachable in this derivation
generalizes at exactly `ℓ`" — which the `let_poly` arm consumes as its `hne`, and which threads
through `lam`/`let_` (they can keep `lvl' = lvl = ℓ`, so the condition must be carried structurally,
not derived from `ℓ < lvl'`). Ruled-out shapes:
- **Not a term-only predicate.** A `let_poly` term node generalizes at its *ambient* level, which is
  a function of the derivation (the `lam`/`let_` sublevels chosen), not readable off the syntax.
- **Not a rule-strictness change.** Forcing `HasType.lam`/`let_` to `lvl < lvl'` would (a) break the
  `lvl' := 0` / `le_refl` examples, and (b) is **unsound to strengthen** — upward level-weakening is
  *not* admissible (a `let_poly` at ambient `k` generalizes at `k`; bumping the ambient changes the
  scheme), so some valid derivations would be rejected. Header-fence anyway.
- So it is a genuine parallel derivation predicate `NoGenAt ℓ (h : HasType …)` (inductive, indexed by
  the `HasType` proof; `let_poly` arm requires `level ≠ ℓ`, every other arm recurses), consumed by a
  `hasType_substAt_le` companion to `hasType_subst`. This is real, tractable metatheory best done with
  live goal-state; it is **additive** (no rule change, no `HasType` edit).

## Status of the two pieces after this session

- **Gap 2 (wrapper strictness):** REDIAGNOSED. Not a groundness problem. Needs `hasType_substAt_le` +
  `NoGenAt ℓ` (above). The arity-0 branch remains clean (`closure_typed_of_lambda` + the landed
  `instantiateV_genAtV_tyEquiv`). The arity≠0 branch splits: `ℓ ∈ argTy.levels` ⇒ `hfv` gives strict
  (clean, existing keystone); else (`ℓ ∈ εb.levels ∪ retTy.levels`, `lvl' = ℓ`) ⇒ needs the
  `NoGenAt`-guarded `hasType_substAt_le`.
- **Gap 1 (var-preservation):** UNCHANGED — still correctly addressed by `HasTypeRT` (the `var`/
  `builtin` args-ground invariant), as designed in Session D. But it is now known to be **independent**
  of gap 2, so Session G can land `HasTypeRT` and the `NoGenAt`/`hasType_substAt_le` fix separately (and
  in either order) rather than entangled.

## Recommended Session G order (needs LSP)

1. Land `NoGenAt ℓ (h : HasType …)` (inductive over the derivation) + `hasType_substAt_le` (the
   `ℓ ≤ lvl` companion to `hasType_subst`) + a `NoGenAt`-aware `genAtV_instantiate_lam_ready_le` /
   `genAtV_closure_ready_value` variant, and finish `genAtV_closure_ready_value_node` (both branches).
   Additive to `Typing.lean`/`Substitution.lean`; verify per-file green. The `\x. perform "op" x`
   witness in `Typing.lean` is the regression target (`NoGenAt 1` holds — no `let_poly` — so the
   wrapper should now fire).
2. `HasTypeRT` (Session D option 1) + RT-inversion, wired into `MStateWf`/`StackWfE`/`StackWfV`
   (`Machine.lean`) — gap 1. Independent of step 1.
3. The ~90-error two-engine `Soundness.lean` grind (var-preservation via `HasTypeRT.var`; the wrapper
   via step 1; migrate B-engine residual `sc.instantiate` at 130/1908/2700-2711/3775 — re-grep, drift).
4. `soundness`/`soundness_evalR` ambient level ≥ 1 (supplies `hlvl0`, and `let_poly` generalizes ≥ 1).
5. Phase 7 (sanity example + `type-soundness-report.md` Caveat 5).

## Tree state at stop
- Committed this session: `Typing.lean` (the `defnPerf` effect-tail strictness witness — 2 examples +
  docstring, per-file green, `lake env lean Eyg/Types/Typing.lean` EXIT 0; Substitution.lean and
  Machine.lean re-checked green as they import Typing) + this note + plan Phase-6 update.
- Working tree: `Eyg/Types/Soundness.lean` modified (as-found Session-C/D partial migration, UNCHANGED
  this session), uncommitted. The committed `Soundness.lean` at HEAD is itself red across the whole
  Phase-6 arc; the additive `Typing.lean` witness introduces no new breakage.
- `grep sorry Eyg/Types/*.lean`: none. No axioms added, no `sorry`, no statement weakened, no rule
  changed. Caveat 5 remains OPEN.
