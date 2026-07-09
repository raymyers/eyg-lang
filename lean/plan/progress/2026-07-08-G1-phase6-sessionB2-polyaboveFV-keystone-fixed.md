---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 6 "Session B2": resolved the `PolyAbove` wall Session B found. Replaced
  the blanket `PolyAbove ℓ Γ` precondition of the readiness keystone (`hasType_subst` /
  `genAtV_instantiate_lam_ready` / `genAtV_closure_ready_value`) with a **free-variable-aware**
  `PolyAboveFV ℓ Γ e`, re-proved all three, and validated non-vacuously on the exact sequential
  counterexample `let a = \x.x in (let c = \z.z in c)`.
status: LANDED (partial) — the design gap is closed and validated; `Typing.lean`/`Substitution.lean`
  committed green per-file. `Soundness.lean` deliberately NOT touched (its pre-existing uncommitted
  broken state left exactly as found). One residual consideration (referencing closures) precisely
  scoped below for Session C.
kind: progress
component: lean (Types.Typing, Types.Substitution)
---

# G1 Phase 6 (Session B2): the `PolyAbove` wall, fixed — free-variable-aware precondition

## What was wrong (recap of Session B's wall)

`genAtV_closure_ready_value` (`Substitution.lean`) and the term-level `genAtV_instantiate_lam_ready` /
`hasType_subst` (`Typing.lean`) required the **blanket** precondition

```
PolyAbove ℓ Γ  :=  ∀ b ∈ Γ, b.2.arity = 0 ∨ ℓ < b.2.level
```

which is provably FALSE for the ambient context of any sequential/nested `let_poly`: for
`let a = \x.x in (let c = \z.z in c)`, discharging the inner `c`'s readiness at opening level `ℓ = 2`
happens under `Γ = [(a, genAtV 1 (α→α))]` with `a.level = 1 < 2` and `a.arity = 2`, so neither
disjunct holds. Session B machine-checked this and stopped.

## The design landed

`hasType_subst`'s `var` arm only ever consumes the disjoint/clean fact for the **single variable the
term actually looks up** — never for the whole context. So the correct precondition is
**free-variable-aware**:

```
def Node.freeVars : Node m → List String            -- binders remove their bound name
  | ⟨.Variable x, _⟩      => [x]
  | ⟨.Lambda x body, _⟩   => body.freeVars.filter (· != x)
  | ⟨.Apply f arg, _⟩     => f.freeVars ++ arg.freeVars
  | ⟨.Let x defn body, _⟩ => defn.freeVars ++ body.freeVars.filter (· != x)
  | ⟨_, _⟩                => []

def PolyAboveFV ℓ Γ e := ∀ x ∈ e.freeVars, ∀ s, Γ.lookup x = some s → s.arity = 0 ∨ ℓ < s.level
```

`PolyAboveFV` is **strictly weaker** than `PolyAbove` (`polyAboveFV_of_polyAbove` bridges them for any
`e`) and — crucially — **threads through the whole induction** because every binder the induction
descends under adds a binding that is automatically "fine":
- `lam`/`let_` add a `mono` binding (`arity = 0`);
- `let_poly` adds `genAtV lvl defnTy` whose `level = lvl > ℓ` (`ℓ < lvl` from the recursion's `hlt`).

So the invariant never demands anything of the pre-existing ambient bindings the term does not touch.
Two helper lemmas do all the work across the ~21 arms:
- `polyAboveFV_sub`  — restrict to a sub-term (`app`, `let_`-defn, `let_poly`-defn) via `mem_append`;
- `polyAboveFV_bind` — descend under a fine binding (`lam`, `let_`-body, `let_poly`-body) via
  `mem_filter`; `x` itself resolves to the fine binding, every other free var transports outward.

(One elaboration subtlety: `polyAboveFV_bind`/`_sub` take `hΓ` **before** the membership obligation, so
the enclosing term `e` is pinned by `hΓ` before `e.freeVars` needs to reduce definitionally.)

`hasType_subst`, `genAtV_instantiate_lam_ready` (`Typing.lean`) and `genAtV_closure_ready_value`
(`Substitution.lean`) now carry `PolyAboveFV ℓ Γ ⟨.Lambda x lbody, la⟩` (over the generalized lambda)
in place of `PolyAbove ℓ Γ`. Everything else (`CtxWfV`, the two commutations, the `let_poly`
reconstruction) is unchanged — this was exactly the localized fix the wall pointed at.

## Validated non-vacuously (regression tests, permanent in `Typing.lean`)

All in `section Examples`, `#print axioms` clean (`[propext, Classical.choice, Quot.sound]`):
- `¬ PolyAbove 2 Γseq`               — the wall itself, `by decide` (`a.arity=2`, `a.level=1`).
- `PolyAboveFV 2 Γseq (\z.z)`        — the fix holds (empty free-var set), where `PolyAbove` fails.
- the readiness keystone `genAtV_instantiate_lam_ready` **fires** for `c` at `ℓ = 2` under `Γseq`,
  producing a genuine `\z.z : Integer → Integer` (`β ↦ integer`) — the preservation obligation the
  wall blocked, now discharged.
- `(genAtV 2 (β→β)).instantiateV [integer] = Integer → Integer` (`by decide`) — the instantiation is
  a real, non-identity re-typing.
- **the whole program** `let a = \x.x in (let c = \z.z in c)` type-checks at `HasType 1 []` (both
  lets generalized: `a` at level 1, `c` at level 2), inner `c` instantiated to `Integer → Integer`.

## Residual consideration for Session C (Soundness re-green): referencing closures

The fix fully closes the **reported** wall (a generalized body that does *not* reference the outer
lower-level binding — the bread-and-butter sequential case). One sharper case is *not* yet covered and
should be settled while re-greening `Soundness.lean`:

- a generalized inner lambda that **references** an outer, lower-level polymorphic binding, e.g.
  `let a = \x.x in (let c = \w. a w in c)`. Here `a` (`level 1`) **is** free in `c`'s body, so
  `PolyAboveFV 2 Γ ⟨\w. a w, _⟩` demands `a.arity = 0 ∨ 2 < 1` — false. The keystone cannot be invoked.
- Why it is not automatic: the `var` arm looking up `a` (`a.level = 1 < ℓ = 2`) needs cleanliness
  `∀ i, a.level ∉ (σ i).levels`, i.e. the instantiation `σ` must have **no level-1 content**. But
  `EnvWf.cons`'s readiness (`Runtime.lean:218`) quantifies over **all** args with levels `≤ s.level`,
  including level-`1` ones — so cleanliness cannot be recovered from the `hσ : levels ≤ ℓ` bound alone.
- The pre-G1 magnitude keystone handled this via `ctxWf_fixed`/`subst_eq_of_fixes_free` (the
  substitution *fixes* the captured context's free vars). The level-native analog is a genuine
  **tightening of the `EnvWf.cons` args side-condition** (e.g. args must not mention the levels of the
  bindings the closure body references, or — likely cleaner — `l < s.level` strictly *plus* a
  disjointness from referenced-binding levels), threaded to the keystone as an extra hypothesis. This
  is judgment-bookkeeping in `Runtime.lean`/`Machine.lean` + one more clause in `PolyAboveFV`'s use,
  not open mathematics, and is best done together with the Soundness preservation cases that actually
  produce the args (which are typically closed/low-level, so the obligation is discharged in practice
  once the side-condition matches how `HasType.var` picks args).

This is flagged, not forced: the task scoped Session B2 to the non-referencing sequential example, and
that is closed and validated.

## Files / tree state

- `Eyg/Types/Typing.lean` — `Node.freeVars`, `PolyAboveFV`, `polyAboveFV_of_polyAbove`/`_sub`/`_bind`;
  `hasType_subst` and `genAtV_instantiate_lam_ready` re-proved over `PolyAboveFV`; 6 regression
  examples. Builds green per-file (`lake build Eyg.Types.Typing`).
- `Eyg/Types/Substitution.lean` — `genAtV_closure_ready_value` precondition switched to `PolyAboveFV`.
  Builds green per-file.
- All other per-file targets (`Scheme`, `Generation`, `Runtime`, `Generalization`, `Machine`) still
  build green.
- `Soundness.lean` — **untouched**; its pre-existing uncommitted, non-building working-tree state is
  left exactly as found (Session C's job). Not staged, not committed.
- No `sorry`, no custom axioms; `hasType_subst`/`genAtV_instantiate_lam_ready`/
  `genAtV_closure_ready_value` all `[propext, Classical.choice, Quot.sound]`.

Caveat 5 remains open pending the Soundness re-green (Session C), but the keystone that Session B
proved *unusable* for sequential let-polymorphism is now genuinely usable.
