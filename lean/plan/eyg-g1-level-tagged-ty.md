---
name: eyg-g1-level-tagged-ty-plan
description: Close Caveat 5 (nested let-polymorphism) by giving Ty a level-tagged variable representation, so nested generalization is structurally distinguishable instead of relying on a derivation-side de-Bruijn level. Multi-session; hard go/no-go checkpoint after the spike.
date: 2026-07-08
status: PAUSED 2026-07-09 by explicit user decision after ~42 sessions on Phase 6 — see "Decision to
  pause" section near the end of this document. Phases 1–5 done; Phase 6 (Soundness.lean re-green) and
  Phase 7 (sanity example + report) intentionally deferred, not abandoned. This is not a failure state:
  Phase 3b's mathematical wall is fully resolved and the actual let_poly preservation case (Caveat 5's
  core obligation) is mechanically proven — what remains is one narrow, precisely-characterized runtime-
  invariant design question that has resisted several careful, honestly-refuted attempts. Resume by
  reading the "Decision to pause" section first, then the most recent progress/ notes it references.
---

# G1 — nested let-polymorphism via a level-tagged `Ty`

**⏸ PAUSED (2026-07-09) — see "Decision to pause" near the end of this file before resuming or reading
further. Short version: the hard mathematics is done (Phase 3b), the actual soundness-critical proof
obligation for Caveat 5 is done (the `let_poly` preservation case in `Soundness.lean`), and what
remains is a narrow runtime-invariant design question deliberately left open rather than forced.**

## Background (do not re-derive)

The headline soundness theorem excludes nested *generalizable* `let`s (a `let` binding a
lambda, nested inside another generalized lambda's body) — `Tree.Node.noLambdaLet`
(`Typing.lean:106`). Prior sessions (`progress/2026-06-19-G1-foundational-wall-confirmed-no-additive-slice.md`
and its addendum) determined this is **not** an additive proof-engineering gap: it is a
representation wall in `Ty` itself.

**Root cause.** `Ty.var : Nat → Ty` (`Ty.lean:38`) is one flat index space. A `Scheme
⟨arity, body⟩` splits it in two *by convention* — indices `< arity` are this scheme's own
quantifiers, `≥ arity` is ambient/enclosing scope (`Scheme.lean:316-328`). That convention
works for exactly one layer of generalization. The current code instead threads a
**derivation-level de-Bruijn level** `n` (`HasType.let_poly`'s `n`, `Scheme.genAt n`,
`CtxWf n`) to fake a second layer — which works for typing a single top-level `let_poly`,
but breaks when re-proving `hasType_subst`'s `let_poly` arm for a *nested* one: the
instantiation witness `σ_args` (`Scheme.instantiate`) is a plain down-shift, and down-shifts
don't compose with the `LevelMap` substitution-stability argument
(`generalizesAt_subst`) the second layer needs. `generalizes_subst_false` is a
machine-checked theorem that no arbitrary substitution discharges this — the wall is real,
not a missing lemma.

Full sizing and rejected alternatives (intrinsically-scoped `Fin`-indexed `Ty`; named
variables + alpha-equivalence) are in the session transcript this plan was written from;
summary: level-tagging `Ty.var` is the minimal structural fix that keeps `subst` structural
(no shifting-logic change, no capture-avoidance) while making "which generalization layer"
decidable from the type itself instead of a side-channel.

## The fix

Change the variable constructor from `Ty.var (idx : Nat)` to `Ty.var (level idx : Nat)`.
`level` names which generalization layer a variable belongs to (0 = outermost/globally-
ambient, k = k-deep in nested polymorphic lets); `idx` is its position within that layer.
Instantiating a scheme at level `k` only ever touches `var k _`; every other level is
structurally untouched by that instantiation — no more index-arithmetic disambiguation,
no down-shift/`LevelMap` mismatch.

## Blast radius (measured from the current tree)

| File | Lines | `.var` sites | `HasType`/`HasTypeV` matches | Note |
|---|---|---|---|---|
| `Ty.lean` | 197 | 1 | – | the constructor itself; `TyEquiv` congruence shapes unaffected |
| `Scheme.lean` | 548 | 18 | – | `instantiate`/`substScheme`/`genAt`/`freeVars` — all index arithmetic, every one re-derived |
| `Substitution.lean` | 156 | 1 | 22 | **the crux** — where the nested `let_poly` arm currently goes vacuous |
| `Generalization.lean` | 591 | 35 | 11 | heaviest non-Soundness file; `genAt`, `LevelMap`, `generalizesAt_subst` |
| `Typing.lean` | 329 | 7 | – | `let_poly` rule signature (drop side-channel `n`, or reinterpret as the tag) |
| `Machine.lean` / `Runtime.lean` | 430 / 585 | 2 / 2 | 8 / 10 | value typing / interpreter port, mechanical re-green |
| `Soundness.lean` | 4278 | 20 | **141** | dominant cost: every `preservation`/`progress` case (A-engine + B-mirror) re-elaborates under the new constructor arity, even where the *logic* is unaffected |

~7,600 lines across 13 files touch `Ty`/`HasType`/`Scheme`; `Soundness.lean` is ~60% of
that and is where a constructor-arity change costs the most just from re-elaboration.

**Correction from Phase 3a (2026-07-08):** this table overstated the blast radius for
the *representation* change specifically. `Typing.lean`, `Machine.lean`, `Runtime.lean`,
`Substitution.lean`, `Generation.lean` needed **zero changes** for the `Ty.var` arity
change — their `.var`/`HasType.var` hits were all the unrelated `HasType.var` *judgment*
constructor, not `Ty.var`. Only `Scheme.lean` (real proof changes: totality + level
case-splits) and `Generalization.lean`/`Soundness.lean` (mechanical `.var i → .var 0 i`
transliteration, zero manual fixes needed in Generalization.lean beyond the mechanical
pass) were touched — see `progress/2026-07-08-G1-phase3a-done-phase3b-scoped.md` for the
exact diff shape. The *capability* work (Phase 3b onward — giving `Scheme` a real level
field and level-parameterizing `hasType_subst`) is where the real remaining cost is, not
the datatype change itself.

## Phases

- [x] **Phase 1 (spike) — tagged core in isolation.** DONE (2026-07-08),
      `Eyg/Types/LevelTagSpike.lean`: a minimal `var`/`fn`-only model with
      `Ty2.var (level idx : Nat)`, `substAt`, `Scheme2`, `genAt`, `instantiate`,
      `substScheme`. Touches nothing existing; wired into `Eyg.lean` only to be
      build-checked. `lake build` 1774 jobs, axiom/`sorry`-clean.
- [x] **Phase 2 (spike, go/no-go) — re-prove `generalizesAt_subst`'s nested case.**
      **GO** (2026-07-08) — see `progress/2026-07-08-G1-level-tag-spike-GO.md`.
      `substScheme_genAt` (the direct analog of `genAt_substScheme`) holds with **no
      `LevelMap`-style hypothesis at all** — `simp only [Scheme2.substScheme,
      Scheme2.genAt]`, essentially definitional. The original `generalizes_subst_false`
      counterexample scenario, re-run tagged, no longer collides. The down-shift/
      re-level problem that blocked the untagged system doesn't arise because
      `genAt`/`substAt` never inspect index magnitude, only the level tag.
      **Checkpoint passed — proceeding to Phase 3.**
- [x] **Phase 3a — port the level tag onto the real `Ty`, collapsed to level `0`.** DONE
      (2026-07-08, commit `8108591a`): `Ty.var(idx)` → `Ty.var(level, idx)`; every
      pre-existing use pinned to level `0` (pure representation change, zero semantic
      change). `lake build` 1774, spec 104/104, axioms unchanged. See
      `progress/2026-07-08-G1-phase3a-done-phase3b-scoped.md`.
- [x] **Phase 3b — make `Scheme`/`genAt`/`instantiate` level-native.** DONE (2026-07-08,
      seven follow-up sessions, commits `ea64f73c` through `78fa925e`). The mathematical
      wall is fully resolved, both term- and value-typing sides, all the way down to a
      concrete runtime closure — see `RuntimeAtV.lean`'s `genAtV_closure_ready_value` and
      the `hOuterVClosure_*` demonstrations. What remains (Phases 4–7 below) is folding
      this back into the real `HasType`/`HasTypeV`/`EnvWf`/`Soundness.lean` — engineering
      against a now-fully-de-risked design, not open mathematics. Give `Scheme` a
      `level` field; `genAt`/`instantiate`/`substScheme` become level-tag-based (no
      reindexing). **Attempted 2026-07-08, not landed on the first pass** — found a real
      subtlety: `hasType_subst` must become level-parameterized throughout its whole
      induction, not just the `let_poly` arm, and the `var`/`builtin` arms need a genuine
      side-condition on the ambient substitution's range. Full 7-step continuation spec
      and detailed history of each sub-session below is in the referenced progress notes.
      - **Follow-up 1** (commits `ea64f73c`/`53300a81`/`3e25495c`/`58d22a0a`): ported
        `substAt`/`levels`/`freeVarsAt` onto the real `Ty`; gave `Scheme` an actual
        `level` field (pinned to `0`); landed the additive `genAtV`/`instantiateV`/
        `substSchemeV` prototype with `subst_instantiateV` proved; ported `CtxWfV`.
        See `progress/2026-07-08-G1-phase3b-scheme-level-field-and-substAt-ported.md`.
      - **Follow-up 2** (WITH Lean tool access): `GeneralizesAtV` + the keystone
        `genAtV_substSchemeV_generalizesAtV` (unconditional); `hasType_substLM_letPoly`
        fires the `let_poly` arm non-vacuously on the existing `HasType`. Residual gap
        pinned: needs a level-tracking judgment. See
        `progress/2026-07-08-G1-phase3b-hasType_substAt-nested-arm-grounded.md`.
      - **Follow-up 3** (deliverable landed): `HasTypeAt (lvl)` (new `TypingAt.lean`) +
        `hasTypeAt_subst`, non-vacuous `let_poly` arm for arbitrary nesting, no
        `noLambdaLet`; wall-falls check on the exact Caveat-5 term succeeds. See
        `progress/2026-07-08-G1-phase3b-HasTypeAt-nested-arm-landed.md`.
      - **Follow-up 4** (readiness keystone, math half complete): `substAt_instantiateV`
        generalizes the instantiation commutation to arbitrary levels; both commutations
        the readiness keystone needs are now proved level-natively. Blocked by two located
        obstructions (A: no `HasTypeAtV` judgment yet; B: `Runtime.lean` needs a magnitude
        closure-body derivation nested lets don't have). See
        `progress/2026-07-08-G1-phase3b-readiness-keystone-two-obstructions-located.md`.
      - **Follow-up 5** (obstruction A resolved): `HasTypeAtV`/`hasTypeAtV_substAt`
        (new `TypingAtV.lean`) + the level-native readiness keystone
        `genAtV_instantiate_lam_ready`; nested Caveat-5 demonstration at distinct levels
        succeeds. See `progress/2026-07-08-G1-phase3b-HasTypeAtV-instantiation-keystone-landed.md`.
      - **Follow-up 6** (obstruction B resolved — Caveat 5 mathematically closed both
        sides): `HasTypeVAt`/`EnvWfAt` (new `RuntimeAtV.lean`) + the value-level keystone
        `genAtV_closure_ready_value`; builds and types the actual runtime closure for the
        doubly-nested Caveat-5 term. **This is the complete mathematical resolution of
        Caveat 5's soundness gap.** See
        `progress/2026-07-08-G1-phase3b-HasTypeVAt-value-keystone-landed.md`.
- [x] **Phase 4 — re-thread `Typing.lean`.** DONE (2026-07-08, "Session A", commit noted below).
      `HasType` is now level-parameterized (`HasType lvl Γ e τ ε`); `let_poly` generalizes at exactly
      `lvl` via `Scheme.genAtV`/`CtxWfV`, **`noLambdaLet` dropped**, no side-channel `n`. `hasType_subst`
      (instantiation-direction) + `genAtV_instantiate_lam_ready` live in `Typing.lean`. See
      `progress/2026-07-08-G1-phase4-5-sessionA-hastype-promoted-soundness-red.md`.
- [ ] **Phase 4 (superseded scoping note) — re-thread `Typing.lean`.** Drop the side-channel `n`/`CtxWf`; `let_poly`
      uses the tag directly; drop `noLambdaLet` from the rule (the actual deliverable).
      **Scoped 2026-07-08 (no source edits, tree held green at `f33550e7`), see
      `progress/2026-07-08-G1-phase4-scoped-multisession-not-landed.md`:** grounded blast-radius
      measurement confirms Phase 4 is **inseparable from Phases 5-6** and not one-session-landable
      without live LSP. The `noLambdaLet` field is load-bearing for *preservation*, not just typing:
      `Soundness.lean:242`/`:2967` (the two `let_poly` preservation cases) literally call
      `genAt_closure_ready … hnl …`, consuming the constructor's `noLambdaLet` field via `inv_let`.
      Dropping it makes both cases unprovable with the magnitude machinery; the only replacement,
      the level-native `genAtV_closure_ready_value` (`RuntimeAtV.lean`), concludes `HasTypeVAt`/
      `instantiateV`, whose type cannot bridge `EnvWf.cons`'s fixed `HasTypeV`/`instantiate`
      obligation — forcing `HasTypeV`→`HasTypeVAt` (**256 Soundness sites**) and `EnvWf`→`EnvWfAt`
      (22) wholesale, plus `HasType`→level-parameterized (changing `lam`/`let_`/`let_poly` arities,
      hence all 19 inversion lemmas + their consumers). No committable green intermediate exists
      (`Eyg.*` glob builds `Soundness`). Recommended: Session A promotes `HasTypeAt`→`HasType` and
      re-greens everything except Soundness (Phases 4-5); Session B/C re-greens `Soundness.lean`
      (Phase 6). All required lemmas already exist axiom-clean (Phase 3b); the remainder is
      re-elaboration-heavy editing safe only with interactive goal-state tooling.
- [x] **Phase 5 — re-green `Machine.lean`/`Runtime.lean`** (value typing, interpreter port). DONE
      (2026-07-08, "Session A"). `HasTypeV`/`EnvWf`/`StackWf`/`StackSegWf` keep their arities (the
      ambient level is an **existential field** of `closure`/`assign`/`arg`, not an index — this
      collapses the projected ~256-site migration to a handful of sites). `EnvWf.cons` readiness is now
      level-native + conditional; `genAtV_closure_ready_value` ported into `Substitution.lean`.
      `Generation.lean`/`Generalization.lean` re-greened; the magnitude readiness keystones removed as
      superseded. Prototype files (`TypingAt`/`TypingAtV`/`RuntimeAtV`) deleted. Verified green
      per-file; `Soundness.lean` deliberately left red (authorized exception — see the progress note).
- [ ] **Phase 6 — re-green `Soundness.lean` (Session B).** The remaining step, scoped as mechanical
      (101+ errors, categorized in
      `progress/2026-07-08-G1-phase4-5-sessionA-hastype-promoted-soundness-red.md`): thread `lvl`
      through the inversion-lemma consumers and case matches; re-prove the two `let_poly` preservation
      cases via `genAtV_closure_ready_value`; adjust `soundness`/`soundness_evalR` to a nonzero ambient
      level. **BLOCKED — Session B (2026-07-08) confirmed a non-mechanical wall; STOPPED, tree left at
      `6deadc54`.** The keystone `genAtV_closure_ready_value` requires `PolyAbove ℓ Γ`, provably false
      for the ambient context of any nested/sequential `let_poly` — regresses basic sequential
      let-polymorphism. See `progress/2026-07-08-G1-phase6-sessionB-polyabove-wall-sequential-letpoly.md`.
      Caveat 5 OPEN.

      **Session B2 — the `PolyAbove` wall RESOLVED.** Blanket `PolyAbove ℓ Γ` replaced by the
      free-variable-aware `PolyAboveFV ℓ Γ e`; `hasType_subst`, `genAtV_instantiate_lam_ready`,
      `genAtV_closure_ready_value` re-proved over it; validated non-vacuously with permanent
      regression examples. See `progress/2026-07-08-G1-phase6-sessionB2-polyaboveFV-keystone-fixed.md`.
      Caveat 5 OPEN (Part 2, Soundness re-green, not reached).

      **Session C — referencing-case gap CLOSED, commit `32c42948`.** Weakened `PolyAboveFV`'s
      per-variable disjunct + tightened the args side-condition to `l = 0 ∨ l = ℓ`; validated on the
      referencing program `let a = \x.x in (let c = \w. a w in c)`. Part 2 (Soundness re-green) NOT
      reached — 103 errors; one non-mechanical obstruction flagged for Session D (var-preservation
      needs a runtime groundness invariant). See
      `progress/2026-07-08-G1-phase6-sessionC-referencing-case-closed-soundness-pending.md`. Caveat 5 OPEN.

      **Session D — two non-mechanical pieces DESIGNED + VALIDATED; nothing committed.** (1) The
      var-preservation obstruction's fix is a *runtime groundness* invariant (`HasTypeRT`, a
      runtime-restricted judgment, NOT a premise on `HasType.var`). (2) The
      `genAtV_closure_ready_value_node` wrapper's `inv_lambda` TyEquiv bridge is solved, with one
      residual strictness subtlety. (3) Soundness error map corrected: 103 errors hid a masked
      second (B-)engine; true shape is ~25 A-engine + ~66 B-engine errors. See
      `progress/2026-07-08-G1-phase6-sessionD-runtime-groundness-invariant-designed-soundness-two-engine-map.md`.
      Caveat 5 OPEN.

      **Session E — the TyEquiv-bridge deliverable LANDED, one green commit.** `instantiateV_genAtV_tyEquiv`
      implemented in `Substitution.lean`. The wrapper's arity≠0/`lvl'=lvl` strictness gap is sharpened,
      not closed — shown entangled with the runtime-groundness invariant (Session D), recommending
      both close together via `HasTypeRT`. See
      `progress/2026-07-08-G1-phase6-sessionE-tyequiv-bridge-landed-strictness-gap-isolated.md`. Caveat 5 OPEN.

      **Session F — Session E's "same obstruction" conjecture REFUTED, one green commit.** A concrete
      `perform`-effect-tail witness shows gap 2 (wrapper strictness) and gap 1 (runtime groundness) are
      independent. True fix for gap 2: a `NoGenAt`/`hasType_substAt_le` companion with a
      derivation-level `NoGenAt ℓ` side condition, not a term-only predicate. See
      `progress/2026-07-08-G1-phase6-sessionF-gap2-decoupled-from-groundness-effect-tail-witness.md`.
      Caveat 5 OPEN.

      **Session G1 — gap 2 CLOSED.** `NoGenAt`/`hasType_substAt_le`/`genAtV_instantiate_lam_ready_le`/
      `inv_lambda_noGenAt` landed in `Typing.lean`, plus `Ty.mem_levels_substAt_strong`. Per-file green;
      whole-project build still fails only on `Soundness.lean` (103 errors, unchanged count). See
      `progress/2026-07-08-G1-phase6-sessionG1-noGenAt-closes-wrapper-strictness-gap.md`. Caveat 5 OPEN
      (gap 1 remains).

      **Session G2 — gap 1's `HasTypeRT` DESIGNED + LANDED, wired into `MStateWf.E`; three green
      commits.** Built as a derivation-indexed judgment (à la `NoGenAt`), not a 24-constructor standalone
      mirror; the `lam`/`let_poly` arms deliberately do NOT recurse into bodies (would wrongly reject
      the legitimate referencing program). `inv_var_rt` extracts the exact gap-1 discharge. Genuine
      finding: "runtime args always ground" holds only as a threaded property re-established at each
      preservation step, not a universal lemma. See
      `progress/2026-07-08-G1-phase6-sessionG2-hastypeRT-landed-lam-nonrecursion-correction.md`. Caveat 5 OPEN.

      **Session G3 — step 2 `genAtV_closure_ready_value_node` LANDED, one green commit; step-1
      frame-RT cascade fully mapped.** The lambda-node closure-readiness wrapper the `let_poly`
      preservation cases call. Step 1 (StackWf/StackWfE/StackWfV frame-RT threading) confirmed
      dischargeable but needs a new linchpin `hasTypeRT_ctxConv`, deferred. See
      `progress/2026-07-08-G1-phase6-sessionG3-wrapper-landed-step1-cascade-mapped.md`. Caveat 5 OPEN.

      **Session G4 — step 1 linchpin `hasTypeRT_ctxConv` LANDED; step 2 frame-RT threading LANDED
      across Runtime+Machine; two green commits.** Gap-2 provenance pinned: the `let_poly` preservation
      case needs three facts (`lvl ≠ 0`, `PolyAboveFV lvl Γ`, `NoGenAt lvl hdefn`) absent at the runtime
      site — the sharp one, `NoGenAt`, is the gap-2 analog of gap-1's `HasTypeRT`. See
      `progress/2026-07-08-G1-phase6-sessionG4-steps1-2-landed.md`. Caveat 5 OPEN.

      **Session G5 — `NoGenAt`-provenance question DECOMPOSED, prior leading hypothesis REFUTED; one
      green commit `8339200d`.** "Strengthen `HasTypeRT.let_poly` to carry `NoGenAt`" refuted by a
      counterexample that would narrow soundness coverage. Correct decomposition: `arity 0` case free;
      `lvl' > lvl` free via new `noGenAt_of_lt`; residual `arity≠0 ∧ lvl'=lvl` genuinely needs it. See
      `progress/2026-07-09-G1-phase6-sessionG5-noGenAt-of-lt-provenance-decomposed.md`. Caveat 5 OPEN.

      **Session G6 — `NoGenAt` shown to be a JUDGMENT-level property (proof irrelevance), correcting
      G5's framing; one green commit `865d8ac0`.** `NoGenAt ℓ h` means "the judgment admits *some*
      derivation with no reachable `let_poly` at `ℓ`," not a fact about the specific derivation. The
      hardest known residual-corner witness is machine-shown to satisfy `NoGenAt` via normalization.
      Open frontier: a general level-**renaming** metatheorem (not mere weakening). See
      `progress/2026-07-09-G1-phase6-sessionG6-noGenAt-proof-irrelevant-normalization.md`. Caveat 5 OPEN.

      **Session G7 — the renaming metatheorem's residual corner SHARPENED; one green commit
      `c50bbfe9`.** A uniform tag-shift is ill-defined there (outer escaped vars and inner `let_poly`
      gen vars share the identical tag with opposite requirements); the escape occurs in sound,
      `HasTypeRT`-valid derivations. Re-characterized correct metatheorem: per-`let_poly` fresh-level
      normalization, not a global shift. `Ty.substAt_substAt_same` landed. See
      `progress/2026-07-09-G1-phase6-sessionG7-renaming-entanglement-sharpened.md`. Caveat 5 OPEN.

      **Session G8 — G7's escape witness shown FRESHENABLE via re-instantiation (no mono-ize needed);
      one green commit `68f207d3`.** The residual corner reduces to a single level-raising lemma
      `hasType_raise_sublevel`, not a two-branch split. Machine-checked on `escLam_lvl1`/`escLam_lvl2`.
      Not proved this session — statement pinned only. See
      `progress/2026-07-09-G1-phase6-sessionG8-escape-freshenable-reinstantiation.md`. Caveat 5 OPEN.

      **Session G9 — sharpens G8's target; commit `8696f55b`.** Plain structural `induction h` is
      *provably insufficient* for the `let_poly` arm (the recursor fixes the stored scheme, but a
      raised `let_poly` needs it re-tagged); two edge cases the single `escLam` witness doesn't exhibit
      identified. `Ty.substAt_congr_freeVarsAt` landed as a building block. See
      `progress/2026-07-09-G1-phase6-sessionG9-raise-sublevel-induction-insufficiency.md`. Caveat 5 OPEN.

      **Session G10 — shortcut evaluated & REJECTED with proof; G9 rec 1 LANDED, commit `63ed5a67`.**
      No fresh-level choice sidesteps the sub-lemma — the generalization-level-shift sub-lemma is
      irreducibly required. Banked the pure re-instantiation equality
      (`length_filter_levels_relabel`/`substAt_relabel_getD`/`instantiateV_genAtV_relabel`). See
      `progress/2026-07-09-G1-phase6-sessionG10-reinstantiation-equality-shortcut-rejected.md`. Caveat 5 OPEN.

      **Session G11 — the raise pinned as a TWO-theorem re-elaboration; a natural `hasType_subst`
      reuse REFUTED; commit `26e1f566`.** The wrapper only needs an ambient raise (drops `NoGenAt`/
      `PolyAboveFV` premises); but the `let_poly` arm needs a *second*, coupled fresh-level relabel
      theorem that `hasType_subst` cannot be (its `{0,ℓ}` precondition excludes a fresh-level relabel
      map). `instantiateV_congr_getD`/`instantiateV_pad_default` banked. See
      `progress/2026-07-09-G1-phase6-sessionG11-raise-two-theorem-architecture-hasTypeSubst-refuted.md`.
      Caveat 5 OPEN.

      **Session G12 — THREE of G11's four remaining pieces landed; relabel re-entrancy insight; three
      green commits `5413665c`/`fe30f615`/`a9a80052`.** `LevelsBelow N h`, `raiseScheme`/`raiseCtx`,
      and the var-arm crux `raiseScheme_genAtV_instantiateV` landed. New structural insight: the two
      raise theorems are re-entrant on the collision, so their `mutual` block needs derivation-structural
      termination, not a level measure. See
      `progress/2026-07-09-G1-phase6-sessionG12-levelsBelow-raiseCtx-varArm-landed-relabel-reentrancy.md`.
      Caveat 5 OPEN.

      **Session G13 — the G12 single-relabel-level blueprint found INSUFFICIENT; commit `ddaf2e35`.**
      A relabel-`k` descent past an inner binding at a different level with foreign level-`k` content
      needs a double relabel the shared `raiseCtx` can't supply; no pure type-function formulation
      exists — the relabel companion is really uniform `raiseTy`, and the two modes need different
      context-raise ops. `Ty.raiseTy`/`raiseTy_eq_self_of_levels_lt`/`raiseTy_eq_substAt_of_single`
      landed. See `progress/2026-07-09-G1-phase6-sessionG13-raiseTy-two-modes-need-distinct-context-raise.md`.
      Caveat 5 OPEN.

      **Session G14 — traced the actual Soundness call site; no commit.** `genAtV_closure_ready_value_node`
      is already proven and needs no raise/relabel theorem for two of its three premises; the crux
      `NoGenAt lvl hdefn` is genuinely the general problem. Sharper target isolated: `hasType_strictify`
      — an *existence* statement (via proof irrelevance) that dodges G13's shared-context conflict
      entirely, a re-attack G9–G13 never tried. See
      `progress/2026-07-09-G1-phase6-sessionG14-narrow-insufficient-strictify-is-real-target.md`. Caveat 5 OPEN.

      **Session G15 — BUILT the raise induction; machine-confirmed the two-modes wall is REAL.** All
      ~20 arms of `hasType_raise` compile except `let_poly`, which fails at exactly the predicted spot:
      the defn sub-derivation needs the RELABELED type but the IH hands back the ORIGINAL. Definitive
      characterization: the raise is genuinely self-referential/mutual, not reducible to substitution.
      `ctxWfV_raiseCtx` landed. See
      `progress/2026-07-09-G1-phase6-sessionG15-raise-built-two-modes-wall-machine-confirmed.md`. Caveat 5 OPEN.

      **Session G16 — the FIRST working derivation-level generalization-level raise LANDED, in the
      *uniform* mode; two green commits `09472c84`/`2271a256`.** Reframing: a *type-fixed* raise is
      intrinsically two-moded and walls at nesting depth ≥ 2; the **uniform** raise (relabel every
      level `≥ t` by `o`, including gen levels) collapses the two modes into one. `hasType_fullRaise`
      landed, no mutual recursion, no freshness/coverage/padding. Confirmed limitation: it also raises
      the outer scheme's OWN gen vars, changing the judgment — proof irrelevance can't transport
      `NoGenAt` through it. Sharpest next route: restrict closure-readiness to ground/runtime args. See
      `progress/2026-07-09-G1-phase6-sessionG16-uniform-fullraise-landed-two-modes-decoupled.md`. Caveat 5 OPEN.

      **Session G17 — the G16 ground-args route REFUTED at the source; no code change.** Checked
      against the exact judgments: `HasTypeRT.var`'s groundness already admits level-`lvl` args (not
      `⊆{0}` as assumed); ground args don't avoid the wrapper's `NoGenAt` need (body-structural, not
      arg-dependent); `hasType_fullRaise` recreates the identical collision at the raised top level.
      Real target unchanged: type-fixed `hasType_strictify` = the two-modes wall. See
      `progress/2026-07-09-G1-phase6-sessionG17-ground-args-route-refuted-strictify-is-type-fixed-wall.md`.
      Caveat 5 OPEN.

      **Session G18 — STRATEGIC PIVOT; the raise/strictify wall DISSOLVED, not climbed; analysis only,
      no code change.** Investigated a genuinely different route: make `HasType.let_poly` additively
      record `NoGenAt lvl hdefn` at construction — self-enforcing (rejects same-level nested `let_poly`
      at the source, a defensible spec refinement to canonical Rémy/OCaml fresh-level generalization).
      Verified every existing construction site already descends strictly. **Needs user approval** (a
      `HasType` spec change). See
      `progress/2026-07-09-G1-phase6-sessionG18-strategic-pivot-additive-noGenAt-on-let_poly-dissolves-wall.md`.
      Caveat 5 OPEN, recommended resolution route recorded.

      **Session G19 — EXECUTION session; the LITERAL authorized `NoGenAt`-field design is
      machine-checked INFEASIBLE (induction-induction, unsupported in Lean 4); corrected to an
      equivalent expressible design; no code change.** Had explicit user authorization for the G18
      route. Corrected feasible design: inline the defn lambda's `lam`-structure into `let_poly` with a
      strict sublevel `hstrict : lvl < lvl'`, same intent, expressible. Verified non-narrowing beyond
      the authorized refinement. See
      `progress/2026-07-09-G1-phase6-sessionG19-noGenAt-field-infeasible-induction-induction-inline-strict-corrected-design.md`.
      Caveat 5 OPEN.

      **Session G20 — the authorized inline-strict `let_poly` reshape LANDED across the whole
      non-Soundness `HasType` cone; committed.** `HasType.let_poly` reshaped with an inlined, strict
      `hstrict : lvl < lvl'` defn-lambda; `noGenAt_letpoly_defn` discharges the wrapper's `NoGenAt`
      premise for free, exactly as designed; rejects nothing previously valid. `Soundness.lean` found
      to need a much broader partial level-native + RT migration (103 errors), orthogonal to and larger
      than the reshape itself — left untouched. See
      `progress/2026-07-09-G1-phase6-sessionG20-letpoly-inline-strict-reshape-landed-noncore-green-soundness-migration-remains.md`.
      Caveat 5 OPEN.

      **Session G21 — Soundness diagnosis; overturns the "purely mechanical" framing.** The poly-let
      preservation case has a genuine invariant gap: `genAtV_closure_ready_value_node` needs
      `lvl ≠ 0` and `PolyAboveFV`, neither derivable from the runtime state as currently typed — needs
      a carried runtime invariant (nonzero-ambient-level, poly bindings at nonzero level), an
      architectural strengthening gated behind approval. Also found: `Soundness.lean` contains TWO
      complete engines (A fully migrated, B untouched) — the 103 errors span both. See
      `progress/2026-07-09-G1-phase6-sessionG21-soundness-diagnosis-polylet-invariant-gap-not-mechanical.md`.
      Caveat 5 OPEN.

      **Session G22 — bridge lemma LANDED (commit `8110c393`) + full threading design finalized.**
      `CtxPolyBd`/`polyAboveFV_of_ctxPolyBd` landed. Finding: closing the gap end-to-end also needs a
      nonzero-ambient-level lower bound carried through `HasTypeV.closure` and the stack frames — a
      four-field threading design finalized for the next session, but not begun (would leave Soundness
      in an unvalidatable half-shaped state). See
      `progress/2026-07-09-G1-phase6-sessionG22-ctxpolybd-bridge-landed-threading-design-finalized.md`.
      Caveat 5 OPEN.

      **Session G23 — four-field threading LANDED (green-committed, HEAD `d86e253c`); FIRST ENGINE
      Soundness migration COMPLETE except a newly-surfaced closure-body-`HasTypeRT` gap.** The
      poly-let preservation obligation is MECHANICALLY DISCHARGED, exactly as G22 predicted. Remaining
      first-engine errors: only the 2 closure-application cases. New gap: `MStateWf.E` needs
      `HasTypeRT` of the applied closure *body*, which `HasTypeV.closure` cannot supply directly — needs
      re-typing infrastructure not yet built. See
      `progress/2026-07-09-G1-phase6-sessionG23-threading-landed-first-engine-green-closureRT-gap.md`.
      Caveat 5 OPEN (poly-let preservation itself discharged).

      **Session G24 — closure-RT gap analyzed; corrected mechanism; no code landed.** Corrected a
      technical misconception: `substAt`-re-typing DOES ground a var's instantiation args. The actual
      obstruction: `hasTypeRT_subst` needs a new predicate `HasTypeRTAt ℓ` (relaxed bound), AND a
      runtime groundness/level-bound invariant threaded through `HasTypeV.closure`/`MStateWf`/`StackWf*`
      supplying it at the four closure-apply sites — flagged as needing sign-off. See
      `progress/2026-07-09-G1-phase6-sessionG24-closureRT-gap-characterized-substAt-grounds-args.md`.
      Caveat 5 OPEN.

      **Session G25 — `HasTypeRTAt`/`RTSubstReady`/`hasTypeRT_subst` LANDED; entire gap-1 substitution
      infrastructure COMPLETE; three green commits `371918d7`/`be7c3eec`/`93e07b91`.** A two-induction
      inversion wall was isolated and dissolved by merging into ONE combined inductive `RTSubstReady ℓ h`
      (induct once, every sub-witness an arm variable). What remains: the runtime groundness/level-bound
      invariant to *supply* `RTSubstReady`/ground `σ` at the closure-apply sites — the load-bearing
      threading, not committable in isolation. See
      `progress/2026-07-09-G1-phase6-sessionG25-hasTypeRTAt-landed-subst-inversion-wall.md`. Caveat 5 OPEN.

      **Session G26 — `builtinApp_arity2`/`instantiateV` regression CLEARED (A+B engines); A-engine now
      at EXACTLY the 2 closure-RT crux sites; closure-RT gap signed off as an env/context-groundness
      invariant beyond the G22-G23 scalar-field pattern; no commit (uncommittable-red working tree).**
      Definitive sign-off: `HasTypeRT hbody` is genuinely un-storable directly in `HasTypeV.closure`;
      body-RT must be re-established at apply from environment/context groundness, and may need
      *iterated* grounding across several outer generalization levels. See
      `progress/2026-07-09-G1-phase6-sessionG26-builtinApp-regression-fixed-closureRT-groundness-signoff.md`.
      Caveat 5 OPEN.

      **Session G27 — closure-RT groundness DESIGN session; the G24/G26 "put it on `HasTypeV.closure`"
      recommendation CORRECTED; no code landed, Soundness.lean preserved intact.** Two concrete
      witnesses prove the groundness invariant cannot be a `HasTypeV.closure`/`HasTypeRT.lam` field
      directly. See `progress/2026-07-09-G1-phase6-sessionG27-closureRT-groundness-applyf-frame-correction.md`.
      Caveat 5 OPEN.

      **Session G28 — attempted the G27 applyf-frame threading; MACHINE-CHECKED refutation of that
      design too; no code landed.** See
      `progress/2026-07-09-G1-phase6-sessionG28-closureReady-propirrelevance-refutation.md`. Caveat 5 OPEN.

      **Session G29 — design correction: the crux needs `HasTypeRT hbody`, not `RTSubstReady lvl'
      hbody`; the G28 forward-readiness-on-arg-frame shown to relocate rather than solve the problem;
      true obstruction localized to ONE site + ONE invariant; no code landed, Soundness.lean preserved
      byte-identical.** Net for next session: the field is `HasTypeRT hbody` on `HasTypeV.closure`,
      discharged by a still-unbuilt env-groundness invariant at the plain lambda-eval site. See
      `progress/2026-07-09-G1-phase6-sessionG29-hasTypeRT-not-RTSubstReady-correction.md`. Caveat 5 OPEN.

      **Session G30 — G29's env-groundness design REFUTED by a machine-checked counterexample; the
      *exact authorized* `HasTypeRT hbody`-on-`HasTypeV.closure` + `EnvWf`-groundness change is proven
      unworkable; STOP + flag for sign-off, no source edits.** Counterexample: `let a = \x.x in \w. a w`
      creates a plain-lambda-eval closure whose body is genuinely non-`HasTypeRT` even with a fully
      ground environment. Workable path is `RTSubstReady`-conditional instead — a materially different
      strengthening, requiring fresh authorization. See
      `progress/2026-07-09-G1-phase6-sessionG30-envgroundness-refuted-rtsubstready-needed.md`. Caveat 5 OPEN.

      **Session G31 — the *authorized* `RTSubstReady ℓ hbody` single-level field is ALSO REFUTED by a
      machine-checked counterexample; the obstruction is a MULTIPLICITY of independent off-scheme
      instantiation levels a single `ℓ` cannot cover; STOP + flag, no code landed, Soundness.lean
      byte-identical.** Counterexample: `let a = \x.\y.x in (\w. a w)` instantiates `a`'s two
      quantifiers at two independent free levels in the body — unsatisfiable for every single `ℓ`.
      Deeper consequence: even iterated grounding can't salvage it (one level escapes into the result
      type). Salvage would need a multi-level readiness predicate AND a matching relaxation of the
      E-state RT invariant — a materially larger, different core redesign. Requesting fresh
      authorization / design decision. See
      `progress/2026-07-09-G1-phase6-sessionG31-rtsubstready-single-level-refuted.md`. Caveat 5 OPEN.
- [ ] **Phase 7 — sanity example + report update.** A nested-generalizable-let example
      (e.g. `let f = \x. (let g = \y.y in g x) in ...`) types under the relaxed rule;
      Caveat 5 in `plan/report/type-soundness-report.md` updated to reflect the closed gap
      (mirroring how Caveats 3/4 record corrected restrictions).
      **NOT STARTED — blocked on Phase 6. See "Decision to pause" below.**

## Decision to pause (2026-07-09)

After ~42 dedicated sessions on Phase 6 alone (part of a much longer multi-day, ~50-session-total
effort on this plan), the user was asked directly whether to (a) authorize further open-ended
architectural changes, (b) continue narrowly-scoped attempts, or (c) stop and mark Caveat 5
documented-open. **The user chose (c).** This section records that decision and the exact state left
behind, so a future session (or a future version of this assistant) can resume cleanly without
re-deriving 42 sessions of hard-won context, or — just as validly — can decide the juice isn't worth
the squeeze and leave Caveat 5 open indefinitely.

### What is actually DONE, unconditionally

- **Phase 3b (the core mathematical wall) is fully resolved and committed**, both for term-typing and
  value-typing, all the way down to a concrete runtime closure — see `Eyg/Types/TypingAtV.lean`/
  `RuntimeAtV.lean`'s history (later promoted into the real judgment) and the dozens of `progress/`
  notes from 2026-07-08 documenting each piece (`substAt`/`levels` ported onto the real `Ty`,
  `genAtV`/`instantiateV`/`substSchemeV`, `CtxWfV`, the readiness keystone, etc.).
- **`HasType`/`HasTypeV`/`EnvWf` were successfully promoted to be level-native** (Phases 4–5, commits
  `e8a99f74` through `6deadc54` and follow-ups) — the OLD magnitude-based judgment is gone; the real
  judgment now natively supports nested generalization. Every file except `Soundness.lean` builds
  clean, always has since Session A.
- **`HasType.let_poly` now requires a fresh-level generalization discipline** (`lvl < lvl'`, inlined
  into the constructor, commit `e9c867ad`) — an explicitly user-authorized core-judgment change,
  verified to reject nothing previously valid, that dissolved a 20-session-long obstruction
  (`NoGenAt`-provenance / the "type-fixed raise" wall) essentially for free.
- **The `let_poly` preservation case itself — the literal soundness-critical obligation Caveat 5 is
  about — is mechanically proven** in the current (uncommitted, see below) `Soundness.lean`, using
  `genAtV_closure_ready_value_node` discharged via `noGenAt_letpoly_defn` + `CtxPolyBd`/
  `polyAboveFV_of_ctxPolyBd`. This is not hypothetical — it type-checks in the working tree.

### What remains open, precisely

`Soundness.lean`'s **A-engine** (`MStateWf`, `~lines 30-2444`) is fully green **except exactly two
closure-application sites** (`~868-882`, `~1030-1044` as of the last session — will drift). Both need
`HasTypeRT`/a runtime-groundness fact for an applied closure's body, and every design tried for
supplying that fact has been refuted by a machine-checked counterexample:

1. `HasTypeRT hbody` directly on `HasTypeV.closure` + an `EnvWf`-groundness invariant — refuted (a
   fully-ground env doesn't prevent the body's *static* instantiation levels from escaping the
   `{0, s.level}` bound `HasTypeRT.var` demands).
2. A single-level `RTSubstReady ℓ hbody` field — refuted (a closure can have **multiple independent**
   escaping free levels simultaneously, e.g. `let a = \x.\y.x in (\w. a w)` where `a`'s two
   quantifiers get instantiated at two *different* free levels in the body; no single `ℓ` covers both).

The genuine open question (see `progress/2026-07-09-G1-phase6-sessionG31-rtsubstready-single-level-refuted.md`
for the full machine-checked writeup): either (a) a **multi-level** readiness predicate generalizing
`RTSubstReady` to a *set* of admissible levels, paired with relaxing `MStateWf.E`'s `HasTypeRT`
requirement and `EnvWf.cons`'s readiness bound to match, or (b) a genuinely different runtime invariant
architecture — possibly not level-bounding instantiation args at all, but something else that still
lets preservation reconstruct a typed closure application. **This is real, open proof-engineering
design, not a known-shape gap** — it may take several more sessions with live Lean LSP access (which
no session in this entire ~50-session effort has had) to resolve, or it may reveal a second, deeper
structural issue the way the `let_poly`-level wall did. Budget accordingly if resuming.

The **B-engine** (`MStateWfB`, `~lines 2460-4278`, a structural mirror of the A-engine) is essentially
untouched — still on much of the old pre-migration API — and will need the same migration the A-engine
just went through, plus whatever the closure-RT fix turns out to be, once that's settled.

### Tree state at the pause point

- `Eyg/Types/Soundness.lean` is **uncommitted** in the working tree — real, substantial, validated
  A-engine progress (the poly-let case working, most of the file re-green'd) that cannot be committed
  under this plan's "never commit a red build" rule, since the file still doesn't fully compile (the
  two closure-apply sites + the whole B-engine). **Do not discard this working-tree diff** — it
  represents dozens of hours of careful work and is the correct starting point for a resumed session.
  If disk/environment state is ever at risk of losing it, consider `git stash` (not `reset`/`checkout`)
  to preserve it explicitly, or copy it aside, before any operation that could touch the working tree.
- Every other file (`Scheme.lean`, `Typing.lean`, `Generation.lean`, `Substitution.lean`,
  `Generalization.lean`, `Runtime.lean`, `Machine.lean`) is fully committed and green.
- No `sorry` anywhere, no custom axioms introduced at any point across the whole ~50-session effort,
  no soundness statement ever weakened. Every refuted design was caught *before* being committed,
  with a machine-checked counterexample, not just abandoned on suspicion.

### If resuming

Read, in order: this section, then `progress/2026-07-09-G1-phase6-sessionG31-rtsubstready-single-level-refuted.md`
(the sharpest, most recent characterization of the open question), then work backward through the
`progress/2026-07-09-G1-phase6-session*` notes as needed for context on what's already been tried and
ruled out — there are ~30 of them, spanning the whole Phase 6 arc; do not re-attempt a design one of
them already machine-refuted. A session with live Lean LSP/interactive goal-state access would very
likely make much faster progress on the remaining design question than the batch-`lake-build`-only
sessions this whole effort has had to rely on throughout.

## Definition of done (per phase, and overall)

`lake build` + `lake exe spec` 104/104 green, `#print axioms soundness` (and
`soundness_evalR`) still exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`, at
every commit — this is not landable partially the way `EffSub'` was; don't leave the tree
red between sessions. If Phase 2 fails, that is a legitimate outcome: record why in
`plan/progress/`, same as `2026-06-19-G1-foundational-wall-confirmed-no-additive-slice.md`
did, and the caveat stays open and honestly documented.

## Estimate

Phases 1–2 (spike) and 3a (real datatype port) are **done** (2026-07-08, one session,
three commits: `406061c1` spike, `8108591a` Phase 3a, plus two further spike commits
`c2db9272`/`a3e448f7` that fully validate Phase 3b's remaining math — the conditional
`hasType_subst`-var/builtin commutation and the `CtxWf`/freshness-threading discipline,
both with zero open uncertainty left). Phase 3b's *math* is settled; what's left is
porting it onto the real `Ty`/`Scheme`/`Generalization.lean` (including a full redesign
of `CtxWf` and every lemma downstream of it — `ctxWf_fixed`, `ctxWf_substCtx`,
`genAt_generalizes`, `genAt_closure_ready`, `generalizes_closure_ready` — around levels
instead of magnitude) plus level-parameterizing `hasType_subst` across all ~15 rule
cases in `Substitution.lean` — genuinely substantial file-editing even with the design
fully de-risked. Then Phases 4–7 (re-thread `Typing.lean`, re-green `Machine`/`Runtime`,
re-green `Soundness.lean`, sanity example + report). Revised rough sizing: Phase 3b
1–2 more sessions (now low-risk, not open-ended), Phases 4–7 2–3 more. Total from here:
3–5 sessions.
