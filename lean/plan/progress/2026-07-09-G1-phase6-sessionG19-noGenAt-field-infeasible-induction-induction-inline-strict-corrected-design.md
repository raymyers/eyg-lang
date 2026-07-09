---
date: 2026-07-09
milestone: G1 (Caveat 5) — Phase 6 "Session G19". EXECUTION session for the G18 authorized
  additive-`NoGenAt`-on-`let_poly` route. Result: the LITERAL authorized design is machine-checked
  INFEASIBLE in Lean 4 (it requires induction-induction, which Lean does not support). Identified and
  validated the corrected feasible realization of the SAME authorized intent: strict-sublevel
  (`lvl < lvl'`) on the `let_poly` defn lambda (inline the lam-structure), from which the wrapper's
  `NoGenAt lvl hdefn` follows FOR FREE via `noGenAt_of_lt` at the Soundness site — no mutual induction.
status: ANALYSIS + machine-checked infeasibility finding. No Eyg/Types code changed. Tree left EXACTLY
  as found (Soundness.lean pre-existing uncommitted partial migration untouched). Caveat 5 OPEN. Had
  explicit user authorization for the `HasType.let_poly` change; the authorized FORM is infeasible, so
  nothing was shipped — the corrected form (same intent, slightly different shape) is handed to the next
  session for execution.
kind: progress
component: lean (analysis only — no code change)
---

# G1 Phase 6 (Session G19): the authorized `NoGenAt`-field design is infeasible (induction-induction); corrected to inline strict-sublevel

No LSP/MCP (canary failed — `lean_goal`/`lean_diagnostic_messages` absent). Read/Grep + `lake env lean`
scratch. **This session had explicit user authorization** to change `HasType.let_poly` (the header-fence
change every prior session deferred), specifically to "additively record `NoGenAt lvl hdefn` at
construction time" per the G18 pivot. The tradeoff the user signed off on: reject `let_poly` nodes whose
defn-lambda nests a same-level `let_poly` (a spec REFINEMENT to canonical Rémy/OCaml fresh-level
generalization; conjecturally re-typable at fresh levels so the typable-PROGRAM set is conjecturally
unchanged, but that equivalence = the unproven strictify wall; soundness fully proved for the refined
relation, spec 104/104 unaffected). This session was to EXECUTE that change.

## Headline finding: the authorized field is not expressible in Lean 4

`HasType.let_poly` carrying `NoGenAt lvl hdefn` requires `HasType` and `NoGenAt` to be **mutually
inductive with `NoGenAt` indexed by `HasType` proofs** — because `NoGenAt` is a `Prop` indexed by a
`HasType` derivation (`inductive NoGenAt (ℓ) : … → HasType lvl Γ e τ ε → Prop`), and the `let_poly`
constructor would reference it. That is **induction-induction**, which Lean 4 core does not support.
Two independent machine-checked errors (minimal repros, this session):

1. Indexing one mutual-block inductive by another:
   `inductive NoGenAt : … → HasType lvl → Prop` inside `mutual … HasType … NoGenAt … end`
   ⇒ `error: Unknown identifier 'HasType'` (the type is not yet available to be used as an index of its
   mutual partner — the defining feature Lean forbids).
2. `inductive NoGenAt (ℓ : Nat) : …` alongside parameterless `HasType`
   ⇒ `error: Invalid mutually inductive types: 'NoGenAt' has 1 parameter(s), but the preceding type
   'HasType' has 0 … All inductive types declared in the same 'mutual' block must have the same
   parameters.`

The G18 pivot note asserted the route was "threadable" and "self-consistent" but never checked this
type-theoretic feasibility. It does not hold. A `NoGenAt`-as-a-recursive-`Prop`-function (via
`HasType.rec`) has the same circularity (it needs `HasType` to already exist, so it cannot be a field of
`HasType`). Encoding induction-induction manually (a flat "pre-derivation" type + a well-formedness
predicate) is possible in principle but is a from-scratch re-encoding of the entire 24-constructor
`HasType`, far beyond a "header-fence field addition" and not what was authorized.

## Corrected feasible design (same authorized intent): strict-sublevel on the defn lambda

The wrapper `genAtV_closure_ready_value_node` (`Substitution.lean:167`) already takes `NoGenAt lvl h` as
a **plain premise** and is proven; it is unchanged by this analysis. The only open question is how the
`let_poly` node supplies `NoGenAt lvl hdefn` at the Soundness `let_poly` preservation site
(`Soundness.lean:226`, `inv_let` output). Key facts established this session:

- `NoGenAt lvl hdefn` for the defn lambda reduces (via `inv_lambda_noGenAt`) to `NoGenAt lvl hbody` at
  the defn lambda's body sublevel `lvl'`, and `noGenAt_of_lt hbody` (`Typing.lean:768`) supplies it
  **for free whenever `lvl < lvl'`** (strict descent). No mutual induction, no external witness.
- So the self-enforcing constraint that makes `NoGenAt lvl hdefn` free is exactly: **the `let_poly`
  defn lambda descends strictly, `lvl < lvl'`** (the Rémy/OCaml "strictly increasing fresh levels"
  discipline the G18 note itself cites as the justification). A same-level nested `let_poly` (inner
  gen level `= lvl`) becomes unconstructable — the exact G18 goal — realized without induction-induction.
- This is expressible by **inlining the defn lambda's `lam`-structure into the `let_poly` constructor**
  (store `lvl'`, `argTy`, `εb`, `retTy`, the strict `lvl < lvl'`, the level bound
  `∀ l ∈ argTy.levels, l < lvl'`, and the inner body `HasType lvl' ((lx,.mono argTy)::Γ) lbody retTy εb`
  in place of the opaque `hdefn : HasType lvl Γ ⟨.Lambda…⟩ defnTy ε`; `defnTy := .fun argTy εb retTy`).
  `inv_let`'s `let_poly` branch then reconstructs `hdefn := HasType.lam (le_of_lt hstrict) hfv hbodydefn`
  and additionally returns `NoGenAt lvl hdefn := NoGenAt.lam _ _ (noGenAt_of_lt hbodydefn hstrict)` —
  exactly the wrapper's premise, for free.

### Verified this design does not reject any existing construction

Every EXISTING *fresh* `let_poly` construction site already descends strictly (checked this session):
- `Typing.lean` examples (`:1735/:1742/:1815/:1822`) — `HasType.lam (lvl' := 2)` under ambient `1`.
- `Generalization.lean:652/668` — `HasType.lam (lvl' := 2)` under ambient `1`.
All use `lvl' = lvl + 1 > lvl`. This is forced anyway in the common case: `HasType.lam` already requires
`∀ l ∈ argTy.levels, l < lvl'`, so a defn whose *argument* type carries a generalizable level-`lvl` var
(the usual polymorphism source) already forces `lvl < lvl'`. The only sites that could in principle use
`lvl' = lvl` are result/effect-only generalizations (e.g. the `defnPerf` witness `\x. perform "op" x`,
ground arg) — but those are freely re-typable at `lvl' = lvl+1` (pick the effect var at level `lvl`
under sublevel `lvl+1`), so the strict rule still accepts the program. The reconstruction arms
(`hasType_subst`/`hasType_substAt_le` `let_poly` at `Typing.lean:411/657`, `hasType_ctxConv` at `:1063`,
`hasTypeRT_ctxConv` at `:1145`, `hasType_fullRaise` at `:1625`, `effWeaken` at `Soundness.lean:73`)
PRESERVE the stored strict-sublevel components from their input (never re-derive), so they stay green by
construction. **No existing construction genuinely needs `lvl' = lvl`** — so this is not a
soundness-narrowing *regression* beyond the authorized same-level-collision refinement.

### Honest narrowing note (vs. the exact authorized field)

Strict `lvl < lvl'` is *marginally* different from the authorized `NoGenAt lvl hdefn`: `NoGenAt` would
accept a `lvl' = lvl` defn that happens to contain no colliding inner `let_poly`; strict rejects all
`lvl' = lvl` defns. But (a) every such program is re-typable at `lvl' = lvl+1` (shown above), and (b)
proving that re-typing is universal is itself the strictify wall — so `NoGenAt` and strict have the SAME
unproven-equivalence status against the original relation. Strict is the honest, expressible realization
of the SAME "canonical fresh-level generalization" refinement the user authorized, and is arguably
*cleaner* (it is literally the Rémy discipline). It is NOT a further narrowing of any consequence; it is
the same refinement in the only form Lean can express.

## Why nothing was shipped (and why a blind reshape was NOT started)

Changing `HasType.let_poly`'s arity is **all-or-nothing across the whole `HasType` cone** (~8 files:
Typing, Substitution, Generalization, Generation, Machine, Runtime, Soundness) and has **no
committable per-file-green checkpoint** short of the entire Soundness re-green (the ~90-error two-engine
grind that has needed live LSP for 10+ sessions). Consumers to update: `inv_let` (Generation:88),
`inv_let_rt`/`NoGenAt.let_poly`/`LevelsBelow.let_poly`/`HasTypeRT.let_poly`/`noGenAt_of_lt`/
`hasType_subst`/`hasType_substAt_le`/`hasType_ctxConv`/`hasTypeRT_ctxConv`/`hasType_fullRaise` +
4 examples (all Typing.lean), Generalization `:652/668`, Generation `:99/129`, Soundness `:72`. Per the
plan's own repeated discipline ("not landable partially; don't leave the tree red between sessions"),
starting this blind (no LSP) would leave a large red uncommitted diff with no checkpoint and no
realistic path to green in one session. So the tree was left EXACTLY as found.

## Recommended next step (execution session, WITH live LSP)

Execute the inline-strict-sublevel reshape of `HasType.let_poly`:
1. Reshape the constructor (drop opaque `hdefn`; add `lvl'`, `argTy`, `εb`, `retTy`, `hstrict : lvl<lvl'`,
   `hfvdefn`, `hbodydefn`; `defnTy := .fun argTy εb retTy`). Optionally add a helper
   `letpoly_defn (…) : HasType lvl Γ ⟨.Lambda…⟩ defnTy ε := HasType.lam (le_of_lt hstrict) hfvdefn hbodydefn`
   to minimize consumer churn.
2. Re-green Typing.lean (all in-file consumers above) — `inv_let`/`inv_let_rt` additionally return
   `NoGenAt lvl hdefn` from `noGenAt_of_lt hbodydefn hstrict`.
3. Re-green Substitution/Generalization/Generation/Machine/Runtime.
4. Soundness `let_poly` preservation: consume the `NoGenAt` now handed by `inv_let`, discharge
   `genAtV_closure_ready_value_node`'s `hng` directly; also supply `hℓ : lvl ≠ 0` (enter soundness at
   ambient `≥ 1`) and `hΓpa : PolyAboveFV` (from `CtxWfV` via `polyAboveFV_of_ctxWfV`, gen-levels `≥ 1`).
5. Finish the two-engine grind; Phase 7 (sanity example `let f = \x.(let g=\y.y in g x) in …` at ambient
   `≥ 1`, both gen levels strict; report Caveat 5 entry describing the fresh-level discipline honestly).

Validation gates unchanged: `lake build` green, `lake exe spec` 104/104 x3, axioms `[propext,
Classical.choice, Quot.sound]`, no `sorry`.

## Tree state at stop

- HEAD `459d5179` unchanged (this note + plan update only).
- Soundness.lean left EXACTLY as found (pre-existing uncommitted partial migration, untouched).
- No `sorry` anywhere in `Eyg/Types/*.lean`. Axioms unchanged. Caveat 5 OPEN; full green NOT reached.
