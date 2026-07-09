---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G16". Built and LANDED the first machine-checked
  derivation-level generalization-level raise, `hasType_fullRaise`, in the *uniform* mode (relabel
  every level ≥ t by o throughout). This collapses the two-modes conflict G7–G15 fought into a single
  clean structural induction — but confirms (with the mode now built, not just sketched) that the
  uniform raise does NOT discharge the closure-readiness wrapper, because it raises the outer scheme's
  own to-be-generalized variables. The wrapper genuinely needs the *type-fixed* mode, whose two-modes
  wall at nesting depth ≥ 2 is unresolved.
status: PARTIAL. Two green additive commits (uniform-raise commutation lemmas; `hasType_fullRaise`).
  Soundness.lean left EXACTLY as found. Caveat 5 OPEN. Full green NOT reached.
kind: progress
component: lean (Eyg/Types/Scheme.lean + Eyg/Types/Typing.lean, additive)
---

# G1 Phase 6 (Session G16): the uniform derivation-level raise, LANDED; two-modes decoupled and pinned

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep/Edit + batch
`lake env lean` / `lake build`. Took the task's "build the mutual `hasType_relabelFree`/`hasType_raise`
pair" seriously, re-derived the obstruction independently and sharply, and found a **cleaner
single-theorem route** that actually compiles — the uniform raise — which the whole G7–G15 arc missed
because it fixated on the *type-fixed* raise the wrapper superficially wants.

## The key reframing: type-fixed (two modes) vs uniform (one mode)

Every prior session pursued a **type-fixed** raise: bump each reachable `let_poly`'s gen level `≥ t`
by `o`, holding the conclusion type/effect/context **literally fixed**. That is what the closure-
readiness wrapper superficially needs (it must keep `genAtV lvl defnTy` and its `Γ` unchanged so the
Soundness site's obligation is met). The type-fixed raise is intrinsically **two-moded**:
- its `let_poly` arm must relabel the defn's *own* gen level (`k ↦ k+o`) while keeping *foreign* `≥ t`
  levels **fixed** (reproduced at var uses via arg-padding / `raiseScheme_genAtV_instantiateV`);
- at nesting depth ≥ 2 a `let_poly`'s `defnTy` carries a foreign `≥ t` gen level (an intermediate
  enclosing generalization instantiated into it), and there the single-level `raiseScheme`
  (`substAt k`) and the relabel the defn actually needs **diverge** (`raiseTy_eq_substAt_of_single`
  fails). The defn (relabel mode) and body (type-fixed mode) sub-derivations share the same ambient
  context `Γ` but need it transformed **incompatibly** — exactly G13 Finding 5, re-confirmed here by
  independent re-derivation. The task's sketched `hasType_relabelFree` (relabel a *single* target
  level `t`) does not resolve this: nested `let_poly`s accumulate multiple target levels that converge
  to a full `raiseTy`, contradicting the single-level `raiseScheme` the type-fixed mode depends on.

The **uniform** raise collapses the two modes into one by **giving up "type-fixed"**: relabel *every*
level `≥ t` by `o` — types, effects, context, AND every gen level, uniformly. Then the `let_poly` arm's
defn is handled by the **same** theorem: the stored scheme becomes `genAtV (k+o) (raiseTy t o defnTy)`,
whose body `raiseTy t o defnTy` is *exactly* the defn's uniformly-raised type. No second mode, no
mutual recursion, no foreign-level divergence (every `≥ t` level, own or foreign, moves the same way).

## What LANDED (two green additive commits, per-file green, axiom-clean)

**Commit 1 (`09472c84`, Scheme.lean) — the pure-equality core:**
- `Ty.levels_raiseTy` — `raiseTy` acts on the level multiset by `l ↦ if t ≤ l then l+o else l`.
- `Ty.length_filter_levels_raiseTy` — arity preservation, **no freshness side-condition** (the uniform
  relabel is injective on levels, unlike the single-level `length_filter_levels_relabel`).
- `Ty.raiseTy_substAt_comm` — `raiseTy` commutes with `substAt` **unconditionally** (no `hclean`, no
  coverage) — the clean heart of the uniform mode.
- `Scheme.instantiateV_genAtV_raiseTy` — uniform raise commutes with `genAtV` instantiation via
  `args.map (raiseTy t o)`: **no argument padding, no coverage, no freshness budget** (contrast
  `raiseScheme_genAtV_instantiateV`'s type-fixed form).

**Commit 2 (`2271a256`, Scheme.lean + Typing.lean) — `hasType_fullRaise`:**
- `Ty.raiseTy_tyEquiv`, `Ty.raiseTy_effWeaken` (Scheme.lean): `raiseTy` respects `TyEquiv`/`EffWeaken`.
- `raiseScheme_U`/`raiseCtx_U` + `_mono`/`_genAtV`/`_lookup`/`_cons` lemmas,
  `instantiateV_raiseScheme_U` (uniform instantiation commutation for **any** scheme, no canonicity
  needed), `ctxWfV_raiseCtx_U` (Typing.lean).
- **`hasType_fullRaise`** (Typing.lean): `HasType lvl Γ e τ ε → 1 ≤ t → t ≤ lvl →
  HasType (lvl+o) (raiseCtx_U t o Γ) e (raiseTy t o τ) (raiseTy t o ε)`. A single ~21-arm structural
  induction — **no mutual recursion, no two-modes conflict, no freshness/coverage bookkeeping**. The
  `var` arm uses `instantiateV_raiseScheme_U`; the `builtin` arm notes builtin schemes are
  level-0-closed (raise-fixed); the `let_poly` arm's defn is the same theorem recursively; `conv`/`app`
  use the `raiseTy` `TyEquiv`/`EffWeaken` stability. Axioms `[propext, Quot.sound]`.

This is the **first machine-checked derivation-level generalization-level raise** in the entire 24-
session arc — every prior session stopped at pure equalities or a wall. It proves the derivation-level
raise *machinery* works end to end.

## Why the uniform raise does NOT discharge the wrapper (confirmed, now with the mode built)

`genAtV_closure_ready_value_node` (Substitution.lean, already proven) needs `NoGenAt lvl hdefn` at the
Soundness site, where `hdefn : HasType lvl Γ ⟨.Lambda x lbody, la⟩ defnTy ε`. By proof irrelevance it
suffices to exhibit *some* re-derivation of the **same** judgment (same `lvl,Γ,defnTy,ε`) with
`NoGenAt lvl`; the residual-corner case (`lvl' = lvl` with an inner `let_poly` at exactly `lvl` —
`escLam`/`advPerf`) forces raising the inner `let_poly`'s gen level while keeping `defnTy` fixed.

`hasType_fullRaise` raises **every** `≥ lvl` level — including the outer scheme's own to-be-generalized
level-`lvl` variables (which surface in `retTy ⊆ defnTy` as the escaped vars `genAtV lvl` quantifies).
So it produces a derivation of the *same term* at a **raised** scheme `genAtV (lvl+o) (raiseTy lvl o
defnTy)`, whose level-`lvl` quantifiers have moved to `lvl+o` — collapsing `genAtV lvl defnTy` to
arity 0. That is a **different judgment**, so proof irrelevance does not transport `NoGenAt lvl`. The
inner-`let_poly`-at-`lvl` (must move) and the outer escaped level-`lvl` vars in `retTy` (must stay, as
the outer quantifiers) are the **identical tag** `lvl`; no threshold separates them, so no uniform
raise (any `t`) can move one and fix the other. This is the type-fixed two-modes wall, re-confirmed
now that the uniform mode is actually built.

## The sharpest remaining route (recommended next, needs LSP + a soundness-critical decision)

`Scheme.instantiateV_genAtV_raiseTy` gives
`(genAtV (lvl+o) (raiseTy lvl o defnTy)).instantiateV (args.map (raiseTy lvl o)) =
 raiseTy lvl o ((genAtV lvl defnTy).instantiateV args)`. For **ground** `args` (levels ⊆ {0}) and
`defnTy` with no level `> lvl`, the target `(genAtV lvl defnTy).instantiateV args` has all levels
`< lvl`, so `raiseTy lvl o` **fixes it** — whence `hasType_fullRaise` (which keeps the closure *value*
`Value.Closure x lbody env` identical, only the derivation moves) yields `HasTypeV (Closure …) target`
directly, **with no `NoGenAt`**. The gap: `EnvWf.cons`/the wrapper quantify over all level-bounded
`args` (typing-time), not just ground ones. But **at runtime the args ARE ground** (gap-1
`HasTypeRT` runtime groundness). So the route is: restrict the closure-readiness obligation
(`EnvWf.cons` / `StackWfV`-Assign) to **ground / runtime** args (justified by `HasTypeRT`), then
discharge it via `hasType_fullRaise` + `instantiateV_genAtV_raiseTy` — dropping `NoGenAt` from the
wrapper entirely. This is a **soundness-critical `EnvWf.cons` refactor** (must not narrow soundness:
the readiness is only ever *consumed* at ground runtime args, so restricting the *stored* obligation
to ground args is sound provided the var-preservation site supplies ground args, which `inv_var_rt`
does) — best done with live LSP and careful review, and it is the first route in the arc that a built,
working raise theorem actually feeds.

Alternative (heavier): build the genuine *type-fixed* two-mode raise, resolving the depth-≥2 shared-
context fork by proving a let_poly's `defnTy` never nests a foreign cross-level `let_poly` (an invariant
that may or may not hold — `escLam` at depth 1 does not exhibit it, but a depth-2 chain plausibly can),
OR by carrying the accumulating relabel set explicitly with a structural `termination_by`.

## Tree state at stop

- HEAD advanced by two commits (`09472c84`, `2271a256`). Scheme.lean + Typing.lean per-file green.
- `hasType_fullRaise` axioms `[propext, Quot.sound]`; no `sorry` anywhere in `Eyg/Types/*.lean`.
- Substitution.lean re-checked per-file green (additive changes don't disturb it).
- Soundness.lean left EXACTLY as found (pre-existing uncommitted 53-line partial migration, untouched).
- Caveat 5 OPEN. Full green NOT reached.
