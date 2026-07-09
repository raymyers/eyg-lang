---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G18". STRATEGIC PIVOT session (per task: stop climbing the
  raise/strictify wall; investigate genuinely different routes). Result: identified a concrete alternate
  route that DISSOLVES the type-fixed raise/strictify wall instead of climbing it — make
  `HasType.let_poly` additively record `NoGenAt lvl hdefn` at construction time (Route 1). Verified the
  route is self-consistent, spec-adequacy-safe, and threadable, and that it needs NO raise theorem. It is
  a `HasType` SPEC change → requires parent/user approval before shipping; NOT shipped this session.
status: ANALYSIS / strategic. No Eyg/Types code changed. Soundness.lean left EXACTLY as found. Caveat 5
  OPEN. The recommendation is a strategic reset toward the additive-`NoGenAt` `let_poly` change (with
  approval), away from the type-fixed `hasType_strictify` theorem that 6+ sessions (G7–G17) converged on
  as walled.
kind: progress
component: lean (analysis only — no code change)
---

# G1 Phase 6 (Session G18): the additive-`NoGenAt`-on-`let_poly` route dissolves the strictify wall

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake`.
Task: STOP trying to prove the type-fixed level-raise/strictify theorem; step back and investigate
genuinely different routes (four candidates given). This is exploratory design, not proof-filling.

## The reframing that unlocks everything: `NoGenAt lvl h` is a property of the JUDGMENT, not the surface derivation

`HasType` is a `Prop`. By proof irrelevance any two derivations of the same judgment are equal, so for a
FIXED judgment `HasType lvl Γ e τ ε`, the proposition `NoGenAt ℓ h` is independent of which inhabitant
`h` we pick: `NoGenAt ℓ h₁ ↔ NoGenAt ℓ h₂`. This is exactly what `escLam_lvl1_noGenAt := escLam_lvl2_noGenAt`
(`Typing.lean:2113`) already exploits — the "obvious" `lvl'=1` derivation `escLam_lvl1` (inner `let_poly`
AT level 1) and the freshened `lvl'=2` derivation `escLam_lvl2` (inner `let_poly` at 2 > 1) prove the
IDENTICAL judgment, so `NoGenAt 1 escLam_lvl1` holds via `noGenAt_of_lt` on the level-2 derivation.

Consequence: `hasType_strictify` (the walled theorem) is, up to proof irrelevance, exactly "every holding
judgment `HasType lvl Γ e τ ε` admits SOME derivation with `NoGenAt lvl`". The wall (G7–G17) is proving
this for an ARBITRARY, adversarially-`lvl'=lvl` derivation handed over by the runtime, where an escaped
level-`lvl` var (in `retTy`) and a to-be-generalized level-`lvl` var (of an inner `let_poly`) are the
identical `var lvl i` leaf and cannot be disentangled for a type-fixed re-derivation.

## Root cause: the `lam` rule is TOO PERMISSIVE (`lvl ≤ lvl'`), so the collision is even constructible

`HasType.lam` (`Typing.lean:111`) permits `lvl ≤ lvl'` (non-strict descent). `noGenAt_of_lt`
(`Typing.lean:768`) shows the collision is EXACTLY the `lvl' = lvl` corner: whenever the lambda body
sublevel is strictly above the generalization level, `NoGenAt lvl` is free. The ONLY reason the wall
exists is that the declarative rule ADMITS `lvl' = lvl` — i.e. it admits an inner `let_poly` generalizing
at exactly the outer generalization level. Real algorithmic let-generalization (Rémy/OCaml "levels"/rank)
uses STRICTLY INCREASING fresh levels; the non-strict `≤` here is the overly-permissive, non-canonical
choice. Note the codebase's own canonical examples already use strict descent: Generalization.lean:651/667
type the poly-let defn's lambda body at `lvl' := 2` under ambient `1`.

## The route (Route 1, concrete form): make `HasType.let_poly` additively record `NoGenAt lvl hdefn`

Change the `let_poly` constructor (`Typing.lean:132`) to carry the fact the wrapper needs, at
CONSTRUCTION time, rather than deriving it post-hoc from an arbitrary derivation:

```
| let_poly ... :
    (hdefn : HasType lvl Γ ⟨.Lambda lx lbody, la⟩ defnTy ε) →
    NoGenAt lvl hdefn →                       -- NEW additive field (ℓ := the node's OWN level)
    CtxWfV lvl Γ →
    HasType (lvl + 1) ((x, Scheme.genAtV lvl defnTy) :: Γ) body bodyTy ε →
    HasType lvl Γ ⟨.Let x ⟨.Lambda lx lbody, la⟩ body, a⟩ bodyTy ε
```

Why this dissolves (not climbs) the wall:

1. **Self-enforcing.** `NoGenAt lvl hdefn`'s `let_poly` arm (`Typing.lean:531`) requires `lvl ≠ (inner gen
   level)`. So a `let_poly` whose defn-lambda nests another `let_poly` AT `lvl` is now LITERALLY
   UNCONSTRUCTABLE — the exact collision case is removed from the relation at the source. No adversarial
   `lvl'=lvl` derivation can be handed to the wrapper because it cannot be built.
2. **Wrapper gets its premise for free.** At the Soundness `let_poly` preservation site
   (`Soundness.lean:236-243`), `inv_let hty` now yields `NoGenAt lvl hdefn` directly (it is stored in the
   node), discharging `genAtV_closure_ready_value_node`'s `hng` (`Substitution.lean:170`) with ZERO raise
   theorem. This is precisely the premise 6+ sessions tried to synthesize.
3. **No re-derivation, only preservation.** Every OTHER `let_poly` construction site
   (`hasType_substAt_le`/`hasType_subst` arms Typing.lean:411/657; ctxConv 1063; effWeaken Soundness.lean:73;
   levelsBelow/others 1150/1631; examples 1733/1813/1966/1981/2081; Generalization 651/667) must now
   supply the new field. But these are TRANSFORMATIONS that DO NOT change any generalization level (subst
   at `ℓ_sub ≤ lvl` keeps `genAtV lvl` via cleanness; conv/effWeaken/levelsBelow never touch gen levels),
   so `NoGenAt lvl` is PRESERVED through them by a companion induction, never RE-DERIVED. This is the
   crucial difference from the wall: we replace "given an arbitrary derivation, prove `NoGenAt`" (the
   entanglement-walled strictify) with "carry `NoGenAt` established at construction, preserved through
   gen-level-fixing transformations" (mechanical). The escaped-vs-bound tag collision never arises because
   we never re-tag anything.

## De-risking checks performed this session

- **Spec adequacy is UNAFFECTED.** `lake exe spec` root is `Eyg.Spec.Harness`, which contains NO
  `HasType` (grep-confirmed): the 104/104 contract is pure runtime evaluation. Changing the typing rule
  cannot regress the spec — spec-adequacy risk is zero.
- **Canonical derivations already satisfy the field.** escLam (via proof irrelevance), and the
  Generalization.lean examples (strict `lvl' := 2`), already meet `NoGenAt lvl hdefn`.
- **Threadability of the companion `NoGenAt`-preservation lemmas** is plausible for every transformation
  site (all fix generalization levels), so the refactor is mechanical, not wall-bearing.

## Honest costs and the ONE blocking caveat (needs approval)

- **This is a `HasType` SPEC change.** Per the hard constraints ("May NOT change statements without
  permission"; "never ship a soundness-narrowing change"), it must NOT be shipped unilaterally. It should
  be presented to the user/parent as a spec DECISION to approve.
- **Narrowing question, answered honestly.** The change rejects `let_poly` nodes whose defn-lambda nests a
  same-level `let_poly`. Every such program is CONJECTURALLY re-typable with the inner at a fresh higher
  level (escLam is the paradigm), so the typable-PROGRAM set is conjecturally unchanged — but proving that
  equivalence IS `hasType_strictify` (the wall), so it stays unproven. What we DO get: soundness fully
  proved for the new `HasType` (non-trivial statement, still a standard sound let-poly system), spec
  104/104 intact. This is a defensible spec REFINEMENT to canonical fresh levels, NOT a trivialization of
  soundness — but its exact equivalence to the current relation is unproven, so it is a genuine spec
  change and the user must sign off on that framing.
- **Blast radius.** ~15 `let_poly` construction sites + companion `NoGenAt`-preservation lemmas for
  subst/conv/effWeaken/levelsBelow. Multi-file, multi-session, must land fully green (Soundness needs full
  `lake build`; no red-Soundness commit). Too large to land green in one no-LSP session; not started, to
  avoid a red tree.

## Routes 2/3/4 (also investigated; rejected as primary)

- **Route 2 (weaker wrapper conclusion).** The readiness `∀ args, HasTypeV closure (scheme.instantiateV
  args)` is consumed at FULL generality: `envwf_lookup` at the var site (`Soundness.lean:214-219`) needs
  `hvty args` for the specific `args` from `inv_var`, which range over all level-bounded args. Deferring
  instantiation to the var site does not help: `hdefn`'s ambient stays `lvl` (immutable), so
  `noGenAt_of_lt` never fires there. No weaker-but-sufficient conclusion found.
- **Route 3 (runtime freshness discipline in Machine.lean).** Plausible in principle (levels consumed
  once) but strictly larger than Route 1 (touches the runtime state + all preservation) and still needs a
  static invariant equivalent to Route 1's field. Not preferable.
- **Route 4 (unreachability).** The `lvl'=lvl` collision IS constructible (escLam_lvl1, escBodyAt) and
  `inv_let` can hand the preservation site an arbitrary `hdefn`, so it is not ruled out by an existing
  invariant. (But note: Route 1 makes it unconstructable BY FIAT, which is the point.)

## Verdict / recommendation

The additive-`NoGenAt`-on-`let_poly` route (Route 1) is the first path in 10+ sessions that STRUCTURALLY
avoids the type-fixed raise/strictify theorem rather than trying to climb it. It converts the walled
"reconstruct `NoGenAt` from an arbitrary derivation" into "record `NoGenAt` at construction, preserve
through gen-level-fixing transformations". It is de-risked (spec-safe, self-consistent, threadable) but is
a `HasType` spec change requiring approval and a multi-session green refactor.

Recommended next step: obtain approval for the `let_poly` additive-`NoGenAt` field as a spec refinement to
canonical fresh levels (with the honest unproven-equivalence caveat above), then execute the refactor
incrementally with live LSP — companion `NoGenAt`-preservation lemmas first (per-file green, committable),
then the constructor change + Soundness discharge last. If approval is withheld, Caveat 5 should be
documented OPEN with this route recorded as the recommended resolution, rather than budgeting further
sessions against the type-fixed strictify wall (which G7–G17 have shown is expensive and convergent).

## Tree state at stop

- HEAD `872541a8` unchanged (this doc + plan update only).
- Soundness.lean left EXACTLY as found (pre-existing uncommitted partial migration, untouched).
- No `sorry` anywhere in `Eyg/Types/*.lean`. Axioms unchanged. Caveat 5 OPEN; full green NOT reached.
