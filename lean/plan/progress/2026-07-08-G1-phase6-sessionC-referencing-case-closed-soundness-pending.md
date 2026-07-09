---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 6 "Session C". Part 1 (the referencing-case gap in the readiness
  keystone) CLOSED and validated non-vacuously. Part 2 (re-green Soundness.lean to full project green)
  NOT reached — characterized precisely below for a Session D.
status: LANDED (partial) — Part 1 committed per-file green (`32c42948`). Soundness.lean left in its
  as-found partial-migration working-tree state (uncommitted, ~103 errors), unchanged by this session.
kind: progress
component: lean (Types.Typing, Types.Substitution, Types.Runtime, Types.Machine)
---

# G1 Phase 6 (Session C): referencing-case gap closed; Soundness re-green still pending

## Part 1 — the referencing case (CLOSED, committed `32c42948`)

Session B2 fixed the sequential/non-referencing wall with the free-variable-aware `PolyAboveFV`, but
flagged one residual: a generalized inner lambda whose body **references** an outer, lower-level
polymorphic binding, e.g. `let a = \x.x in (let c = \w. a w in c)`. There `a` (level 1) is free in
`c`'s body, and B2's disjunct `ℓ < s.level` demanded `2 < 1` (false), so the keystone could not fire.

### Design (additive, localized — no new prototypes, no statement generalization)

Two coordinated changes:

1. **Weaken `PolyAboveFV`'s per-variable disjunct** from `s.arity = 0 ∨ ℓ < s.level` to
   `s.arity = 0 ∨ (s.level ≠ 0 ∧ s.level ≠ ℓ)`. This admits a *referenced* polymorphic binding
   **below** `ℓ` (like `a` at level 1), which the strict-`<` form rejected. Strictly weaker than B2's
   form (bridged by the updated `polyAboveFV_of_polyAbove`), so the already-validated non-referencing
   examples are unaffected. `polyAboveFV_bind`'s `hs0` premise weakened in lockstep; the `let_poly`
   body-descent discharges it from `ℓ < lvl` (gives `lvl ≠ 0 ∧ lvl ≠ ℓ` by `omega`).

2. **Tighten the substitution / instantiation-args side-condition** from `l ≤ ℓ` to `l = 0 ∨ l = ℓ`
   everywhere it is threaded:
   - `hasType_subst`'s `hσ` (Typing.lean) — plus a derived local `hσle : l ≤ ℓ` for the `lam`/`let_`
     freshness bounds and `ctxWfV_substCtxAt`;
   - `genAtV_instantiate_lam_ready`'s `hargs` and its two internal `hσ` constructions (Typing.lean);
   - `genAtV_closure_ready_value` (Substitution.lean);
   - `EnvWf.cons` and `envwf_lookup` (Runtime.lean);
   - `StackWfV`/`StackWfE` Assign readiness (Machine.lean).

   **Why this is exactly the fix:** `hasType_subst`'s `var` arm needs, for a referenced polymorphic
   binding at level `k = s.level`, both `ℓ ≠ k` and cleanliness `∀ i, k ∉ (σ i).levels`. With `σ`'s
   levels now `⊆ {0, ℓ}` and `k ∉ {0, ℓ}` (from the weakened `PolyAboveFV`: `k ≠ 0 ∧ k ≠ ℓ`), both
   discharge — uniformly for referenced bindings **below** `ℓ` (the referencing case) *and* above `ℓ`
   (the old case). The `var` arm's `hdisj` was rewritten to derive cleanliness from `hσ` + the two
   `≠` facts instead of from `ℓ < s.level`.

### Validated non-vacuously (permanent regression examples in `Typing.lean`, `section Examples`)

New, all axiom-clean (`[propext, Classical.choice, Quot.sound]`):
- `polyAboveFV_reflam` — `PolyAboveFV 2 Γseq (\w. a w)` holds (`a.level = 1 ≠ 0` and `≠ 2`), where
  B2's `2 < 1` disjunct was false.
- `hbody_ref` — `a w` types at level 3: `a` (`genAtV 1 (α→α)`) instantiated at `[var 2 0]` gives
  `(var 2 0) → (var 2 0)`, applied to `w : var 2 0`. (Note `a`'s instantiation arg is `var 2 0`, level
  2 — this is a *typing-time* instantiation inside the keystone, distinct from the runtime-facing
  `EnvWf.cons` args condition; see Part 2 below.)
- the readiness keystone **fires** for the referencing `c` at opening level `2` under `Γseq`,
  instantiating `c` to `Integer → Integer`;
- the whole program `let a = \x.x in (let c = \w. a w in c)` type-checks at `HasType 1 []`.

`hasType_subst`, `genAtV_instantiate_lam_ready`, `genAtV_closure_ready_value` all re-verified
`[propext, Classical.choice, Quot.sound]`. Per-file green: Typing, Substitution, Runtime, Machine,
Scheme, Generation, Generalization. No `sorry`.

## Part 2 — re-green `Soundness.lean` (NOT reached; precise state for Session D)

`lake build Eyg.Types.Soundness` reports **103 errors**. The working tree's `Soundness.lean` was found
**partially migrated** already (not the stale magnitude version its committed diff suggests): e.g. the
`evalE`/`progress` control cases (~lines 205-254) already use the level-native `inv_lambda` 8-tuple,
`HasTypeV.closure henv hfv hbody heq`, `stackWfE_lambda_step`, `Scheme.genAtV lvl`,
`Scheme.instantiateV_mono`, and the new `envwf_lookup`. This session did **not** edit Soundness.lean;
it is left exactly as found (uncommitted).

### The one genuinely non-mechanical obstruction (settle first)

**Var-preservation must discharge the args side-condition, which `HasType.var` does not record.**
At `Soundness.lean:216-219`:
```
obtain ⟨v, hvlk, hvty⟩ := envwf_lookup henv hlookup
... exact ⟨τin, (hvty args).conv heq, ...⟩
```
`envwf_lookup` now returns `hvty : ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) →
HasTypeV v (s.instantiateV args)`, so `hvty args` needs the side-condition proof for the **specific**
`args` produced by `inv_var hty`. `HasType.var` places **no constraint** on its `args`, so this is not
locally available. Options, in rough order of preference:
  (a) Show a *runtime* invariant "instantiation args in a well-typed machine state are ambient/ground"
      — i.e. the args at a runtime `var` lookup carry only level `0` (or `≤` the soundness ambient
      level), whence `l = 0 ∨ l = s.level` (this is the direction the note anticipated: runtime args
      are ground/low-level). This is the faithful route but needs a levels-well-formedness invariant
      threaded through the machine-state typing (`HasTypeS`/`StackWf`), which is currently absent.
  (b) Add the premise `∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level` directly to `HasType.var`
      (and `.builtin`). **CAUTION:** this is a core-judgment change (header-fence territory) and, more
      importantly, it would reject legitimate *typing-time* instantiations like `hbody_ref`'s
      `a : level 1` instantiated at `[var 2 0]` (level 2 ≠ 0, ≠ 1). So (b) as stated is **wrong** for
      general `HasType`; only the *runtime/value* boundary (`EnvWf`/`StackWf`, already tightened this
      session) should carry it. Prefer (a).
  The chosen `l = 0 ∨ l = s.level` (rather than `l = 0`) is deliberately the *weaker/safer* boundary
  condition — strictly more args qualify, so whatever runtime invariant Session D establishes, the
  discharge is easier. If (a) proves that runtime args are strictly level-`0`, the condition can be
  narrowed to `l = 0` later without touching the keystone (the keystone handles the wider `l=0∨l=ℓ`).

### The ~mechanical remainder (after the above is settled)

Error clusters from `lake build Eyg.Types.Soundness 2>&1 | grep error:` (103 total):
- **69, 90** — `weakenEffAux` `app`/`conv` arms: `HasType` minor-premise arg-shape drift
  (level-parameterized rule arities).
- **218-219** — the var-preservation discharge above.
- **243** — `genAtV_closure_ready_value_node` is referenced but does not exist: needs a **node-level
  wrapper** of `genAtV_closure_ready_value` (takes a `HasType lvl Γ ⟨.Lambda …⟩ defnTy ε` derivation,
  inverts it via `inv_lambda`, then applies the keystone), plus `hΓpa`/`hlvl0`/`hcw` in scope at the
  `let_poly` preservation site. This wrapper is additive and can be pre-landed in `Substitution.lean`
  once its exact signature (which `PolyAboveFV`/`CtxWfV` it threads) is pinned from the call site.
- **247, 1566, 1592 (×~20 "simp made no progress")** — rewrites/`simp` sets stale w.r.t. the
  level-native `instantiateV`/`substAt` lemma names.
- **701-720, 846-868, 1027-1030, 1564-1590, …** — dense "Application type mismatch" clusters: consumers
  of the inversion lemmas (`inv_app`/`inv_let`/`inv_lambda`/`inv_var`/`inv_builtin`) and `HasTypeV`
  constructors whose tuple shapes/arities shifted. Mechanical once the shapes are read off
  `Generation.lean`'s **current** definitions (do not trust older notes' tuple shapes).
- `soundness`/`soundness_evalR` will likely need their ambient level set to a **nonzero** constant
  (so `let_poly` at top level generalizes at level ≥ 1, keeping all polymorphic bindings' `s.level ≥ 1`
  — which is what makes the `s.level ≠ 0` half of the weakened `PolyAboveFV` discharge for referenced
  bindings, and rules out the level-0-polymorphic pathology).

### Recommended Session D order
1. Land the runtime levels-well-formedness invariant (option (a)) + the `genAtV_closure_ready_value_node`
   wrapper — the two non-mechanical pieces — verified per-file on `Typing`/`Substitution`/`Runtime`.
2. Then grind the mechanical inversion/constructor clusters with live LSP goal-state (batch `lake build`
   iteration alone is very slow for ~90 arg-shape mismatches).

## Tree state at stop
- HEAD `32c42948` (Part 1). Working tree: only `Eyg/Types/Soundness.lean` modified (as-found partial
  migration, uncommitted, unchanged by this session) + untracked `.claude/`.
- `grep sorry Eyg/Types/*.lean`: none. Committed files axiom-clean.
- `lake build` (whole project) still red **solely** on `Soundness.lean`; every other per-file target green.
