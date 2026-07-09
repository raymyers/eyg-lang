---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 6 "Session B": attempted to re-green `Soundness.lean` over the
  level-native judgment. STOPPED on a genuine (non-mechanical) design gap in Session A's readiness
  keystone: the `PolyAbove ℓ Γ` precondition of `genAtV_closure_ready_value` is FALSE for the
  ambient context of any nested/sequential `let_poly`, so the two `let_poly` preservation cases are
  UNPROVABLE with the current keystone. This regresses basic sequential let-polymorphism relative to
  the pre-G1 system. Tree left at `6deadc54` (Soundness red, as authorized); uncommitted exploratory
  edits to `Machine.lean`/`Soundness.lean` are to be rolled back by the harness.
status: STOPPED — wall confirmed, machine-checked. No commit (Session B does not get the red-commit
  exception; full green not reached). Honest partial-progress stop per the plan's stated protocol.
kind: progress
component: lean (Types.Soundness, Types.Machine, Types.Typing/Substitution keystones)
---

# G1 Phase 6 (Session B): the `PolyAbove` wall — level-native keystone regresses sequential `let_poly`

## Summary

Session B was tasked with a "mostly-mechanical" re-green of `Soundness.lean` over the level-native
`HasType`/`HasTypeV`/`EnvWf` promoted in Session A (`6deadc54`), the only non-green file. While
threading the mechanical changes I hit — and then **machine-checked** — a genuine, non-mechanical
gap that blocks the two `let_poly` **preservation** cases. It is not a missing-lemma/plumbing issue;
it is a design gap in Session A's readiness keystone `genAtV_closure_ready_value`
(`Substitution.lean`) that makes it **inapplicable to any `let_poly` whose ambient context contains an
outer polymorphic binding** — i.e. to *sequential* (and nested) let-polymorphism, the bread-and-butter
of HM. This was sound in the pre-G1 magnitude system (`noLambdaLet` only ever restricted a
let-binds-a-lambda **nested inside a generalized lambda's body**, never sequential lets).

## The wall, precisely (machine-checked)

`genAtV_closure_ready_value` (and the term-level `genAtV_instantiate_lam_ready` / `hasType_subst` it
composes, `Typing.lean`) require the precondition

```
PolyAbove ℓ Γ  :=  ∀ b ∈ Γ, b.2.arity = 0 ∨ ℓ < b.2.level
```

where `ℓ` is the `let_poly`'s own generalization level (`= lvl`), and `Γ` is its ambient context.
It is used in `hasType_subst`'s `var` arm to give, for a looked-up polymorphic binding `s`,
`ℓ < s.level` — which in turn supplies both disjointness (`ℓ ≠ s.level`) **and** cleanliness
(`σ`'s levels `≤ ℓ < s.level`, so `σ` has no level-`s.level` content) for the
`substAt_instantiateV_scheme` commutation.

**Fact 1 (machine-checked).** For the outer binding `a := genAtV 1 (var⟨1,0⟩ → var⟨1,0⟩)`:
`a.arity = 2`, `a.level = 1` (`by decide`). Hence `PolyAbove 1 [(x,a)]` is provably **false**
(need `2 = 0 ∨ 1 < 1`).

**Fact 2 (machine-checked).** The standard sequential program

```
let a = \x. x in (let c = \z. z in c)     -- both value-restricted ⇒ both let_poly
```

type-checks under the level-native `HasType (m:=Unit) 1 []` (both lets generalized: `a` at level 1,
`c` at level 2), and the inner `let c` is typed under `Γ = [(a, genAtV 1 (var⟨1,0⟩→var⟨1,0⟩))]`.
So at the point preservation discharges `c`'s `EnvWf.cons` readiness (ambient level `lvl = 2`), the
keystone's precondition is `PolyAbove 2 Γ`, which is false (Fact 1, a fortiori: `1 < 2` needed with
`a.level = 1`).

(Both facts were verified in a scratch file `Eyg/Types/ScratchPolyAbove.lean`, now deleted — the
`HasType` derivation elaborated `sorry`-free and the `PolyAbove` refutation closed by `decide`.)

## Why this is not mechanical, and why it is a *regression*

- `PolyAbove ℓ Γ` combined with the `let_poly`-stored `CtxWfV ℓ Γ` (every scheme-body level `< ℓ`)
  forces **every** binding in `Γ` to have `arity = 0`: an `arity ≠ 0` binding `genAtV k d` has
  `k ∈ d.levels`, so `CtxWfV ℓ` gives `k < ℓ`, contradicting `PolyAbove`'s `ℓ < k`. So the keystone
  is usable **only when `Γ` has no genuinely-polymorphic binding**.
- `PolyAbove` is **not** an invariant one can thread: descending into a `let_poly` body adds
  `(x, genAtV lvl defnTy)` (level `lvl`) at ambient `lvl+1`, and `PolyAbove (lvl+1)` demands
  `lvl+1 < lvl`. So the *very act* of entering a polymorphic let's body destroys `PolyAbove` for any
  further `let_poly` inside it.
- The semantic content of `c`'s readiness is **trivially true** (`\z.z` is polymorphic; it types at
  every instantiation, including ones mentioning level 1). The blocker is purely that `PolyAbove` is a
  **blanket** precondition over all of `Γ`, while the `hasType_subst` induction only ever *uses* it for
  variables actually looked up in the re-typed term — and `c`'s body (`z`) never references `a`.
- The pre-G1 magnitude keystone (`genAt_closure_ready`, now removed) discharged exactly this via
  "`gen` only touches variables disjoint from the captured context's free vars"
  (`ctxWf_fixed`/`Ty.subst_eq_of_fixes_free`) — a **per-variable/free-variable** condition, not a
  blanket level bound. Session A's level-native flip replaced that with the strictly stronger
  `PolyAbove`, which **regresses sequential/nested let-polymorphism**.

## What the real fix requires (scoping for the next session)

`hasType_subst` (and thence `genAtV_instantiate_lam_ready` / `genAtV_closure_ready_value`) must be
re-proved with a **free-variable-aware** precondition replacing blanket `PolyAbove ℓ Γ` — e.g.
"for every `x` free in `e` with `Γ.lookup x = some s`, `s.arity = 0 ∨ ℓ ≠ s.level` with the
cleanliness obligation discharged per-lookup". Concretely the `var` arm needs, for the *specific*
looked-up `s`, either `arity = 0` (mono — skipped) or (`ℓ ≠ s.level` **and** `σ` clean w.r.t.
`s.level`). Since the readiness quantifies over **all** `args` with levels `≤ ℓ` (including
level-`s.level` ones for outer `s.level < ℓ`), cleanliness cannot be recovered from a σ-side bound; it
must come from `s` **not occurring** in `e`. Threading a "free vars of `e`" set through the ~15-arm
induction (correctly across binders, which extend `Γ`) is the actual deliverable — genuine
metatheory, not the mechanical arity/tuple re-green Phase 6 was scoped as. This is best done with live
Lean LSP (unavailable this session) and is realistically multi-session, on top of the ~150-error
mechanical migration that still sits above it.

Alternatives considered and rejected:
- Threading `PolyAbove` as an MStateWf invariant — impossible (not preserved across `let_poly`
  descent, per above).
- Restricting `soundness` to `PolyAbove`-satisfying programs — this excludes sequential
  let-polymorphism (basic HM), i.e. a **vacuous/dishonest weakening** the task forbids.
- Bumping the defn-lambda's body level to force `ℓ < lvl'` — not free (`let_poly` inside the body
  generalizes at a level a bump would shift). Also independent of the `PolyAbove` blocker.

## Mechanical findings that ARE correct (for reuse next session)

The mechanical migration pattern was validated as far as it went and is recorded here so it is not
re-derived:

- `MStateWf .E` / `mStateWf_E` / all inversion lemmas gain a `lvl` existential; `HasType` uses gain a
  leading `lvl`.
- Constructor arities: `HasType.lam hle hfv hbody`; `HasType.let_ hdefn hle hfv hbody`;
  `HasType.let_poly hdefn hcw hbody` (**no** `hnl`); `HasTypeV.closure henv hfv hbody heq`.
- `inv_lambda h ⇒ ⟨lvl', argTy, εb, retTy, hle, hfv, hbody, heq⟩`; `inv_let` mono ⇒
  `⟨lvl', defnTy, hdefn, hle, hfv, hbody⟩`, poly ⇒ `⟨lx, lbody, la, defnTy, hdl, hdefn, hcw, hbody⟩`.
- `weakenEffAux`/`weakenEff` re-prove cleanly with the new `lam`/`let_`/`let_poly` field shapes.
- **Required cross-file refactor (correct, Machine.lean builds green with it):** `StackWfV`/`StackWfE`
  readiness clauses must switch from magnitude `sc.instantiate args` to level-native
  `sc.instantiateV args` **with** the side-condition `(∀ t ∈ args, ∀ l ∈ t.levels, l ≤ sc.level)`, to
  match `EnvWf.cons` and the keystone; the mono-Assign proofs then use `Scheme.instantiateV_mono` and
  an extra ignored side-condition binder (`fun args _ => …`, `intro … args _`). This part is done and
  green in the (to-be-rolled-back) working tree and should be re-applied first next session.

## Tree state

`HEAD = 6deadc54` (Session A's authorized red checkpoint). No commit made this session (full green not
reached; the level-native keystone cannot prove the genuine soundness statement for sequential
let-polymorphism). Uncommitted exploratory edits to `Machine.lean`/`Soundness.lean` are to be rolled
back by the harness. **Caveat 5 remains open**; the level-native promotion (Session A) is now known to
have a soundness-regressing keystone that must be re-proved (free-variable-aware) before Phase 6 can
land.
