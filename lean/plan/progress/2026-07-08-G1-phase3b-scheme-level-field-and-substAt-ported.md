---
date: 2026-07-08
milestone: G1 (Caveat 5) — Phase 3b: two mechanical/additive steps landed, next step's design sharpened
status: two green commits landed on top of Phase 3a; the level-native genAt/instantiate/substScheme flip (continuation spec step 6) has a newly-found arity subtlety, not yet attempted live
kind: progress
component: lean (Eyg/Types/{Scheme,Generalization,Soundness}.lean)
---

# G1 Phase 3b: `Scheme` now carries a `level` field; `substAt`/`levels` ported onto the real `Ty`

Continuation of `progress/2026-07-08-G1-phase3a-done-phase3b-scoped.md`. That note's 7-step
continuation spec is still the reference; this session landed steps that de-risk step 6 without
attempting it live (no Lean LSP / interactive goal-state tooling was available this session — only
`lake build` batch feedback — so no changes that need iterative interactive proof search were
attempted; everything landed here was either purely additive or a mechanical field-threading pass,
verified by full rebuild + `lake exe spec` + axiom check after each).

## Landed, two commits

1. **`ea64f73c`** — `Ty.substAt`/`Ty.levels`/`Ty.freeVarsAt` ported from `LevelTagSpike.lean`'s toy
   `Ty2` model onto the **real**, 12-former `Ty`, plus `substAt_eq_self_of_not_mem` and the conditional
   cross-level commutation `substAt_substAt_comm` (with its `clean_of_levels_lt` freshness bridge).
   Purely additive — no existing definition touched, so nothing downstream could break. This retires
   the audit flagged as open in the continuation spec's step 5 ("verify the unconditional claim still
   holds once `Ty` has 12 formers instead of the spike's 2") — confirmed: none of the extra formers
   touch `var` specially, both facts port over unchanged in shape.

   **Pitfall hit and fixed**: the bridge lemmas `subst_eq_substAt_zero`/`freeVars_eq_freeVarsAt_zero`
   were initially marked `@[simp]`. This rewrites *every* existing `simp [Ty.subst]`/`simp [freeVars]`
   call site project-wide into the new vocabulary, breaking unrelated proofs elsewhere (caught by a
   full `lake build`, not by building `Scheme.lean` in isolation — build the whole tree, not just the
   changed file, before trusting green). Fixed by dropping the `@[simp]` attribute; they're now plain
   lemmas, used only where explicitly invoked.

2. **`53300a81`** — `Scheme` gains a `level : Nat` field (`⟨arity, level, body⟩`), pinned to `0` at
   every existing construction site — mirrors the Phase 3a playbook exactly (mechanical field-arity
   churn kept separate from the semantic change). `genAt`/`instantiate`/`substScheme`'s *logic* is
   completely unchanged — still the old arity/`reindexGen` magnitude machinery, now just carrying an
   unused tag. `Scheme.ext'` gained a third (`level`) premise, discharged by `rfl` at both call sites
   (both sides being compared are pinned to level `0` identically). Roughly 20 literal `⟨n, ...⟩`
   scheme constructions across `Generalization.lean`/`Soundness.lean` needed the extra field threaded
   through (mechanical `perl` pass, same shape as Phase 3a's `.var i → .var 0 i` pass).

Both commits: `lake build` 1774 jobs, `lake exe spec` 104/104, axioms unchanged
(`[propext, Classical.choice, Quot.sound]`), no `sorry`.

## The next step (continuation spec step 6) has a newly-found subtlety — worth recording before attempting

Worked through **by hand** (no Lean session) what happens when `genAt`/`instantiate`/`substScheme` are
flipped to the literal level-native definitions the continuation spec proposes:

```
genAt (ℓ) (d)      := ⟨(d.levels.filter (· = ℓ)).length, ℓ, d⟩        -- no reindexing
instantiate s args := Ty.substAt s.level (fun i => args.getD i (.var s.level i)) s.body
substScheme σ s     := ⟨s.arity, s.level, Ty.subst σ s.body⟩            -- σ always ambient/level-0
```

### 1. `instantiate`'s unconditional `args.getD` breaks `instantiate_mono` unless mono is special-cased

`instantiate_mono` (`(mono t).instantiate args = t` for **any** `args`) is not just a convenience
lemma — `HasType.var`'s declarative rule allows **arbitrary** `args` unconditionally (confirmed by
reading `Typing.lean`'s `var` rule and its use in `hasType_ctxConv`), so a mono (arity-0) scheme must
ignore `args` **regardless of what's in its body or what level it's tagged at**. Under the proposed
`instantiate`, if a mono scheme happens to be tagged at some level `ℓ` and its body contains a `var ℓ
j` leaf that a nonempty `args` covers, instantiation would (incorrectly) rewrite it — mono schemes
routinely reference *other* ambient/context type variables in their body, so this is not a
vacuous corner case.

**Resolution (not yet applied to real code, just derived)**: gate `instantiate` on arity explicitly:
```
def instantiate (s : Scheme) (args : List Ty) : Ty :=
  if s.arity = 0 then s.body else Ty.substAt s.level (fun i => args.getD i (.var s.level i)) s.body
```
This is a **smaller** case split than the old design's per-index `i < arity` branch inside the
substitution function (which the continuation spec's "no arity-bound case split needed" was
comparing against) — just gone from *no* split to *one* outer split, not zero. Worth flagging as a
deliberate, minor deviation from the continuation spec's literal reading, not an oversight.

### 2. `substScheme`-after-`genAt` is not literally `= genAt` on the substituted body, once `arity` is a real field

The spike's `Scheme2` has **no `arity` field at all** (`⟨level, body⟩` only) — so its
`substScheme_genAt` theorem needing no `ℓ ≠ ℓ'` hypothesis is partly an artifact of that: there's no
arity count for a substitution to accidentally perturb. The real `Scheme` keeps `arity` (continuation
spec step 1, "kept for informational parity"). Worked through by hand: if `substScheme` **recomputes**
arity from the substituted body (the naive reading, mirroring `genAt`), then `substScheme σ (genAt ℓ'
d) = genAt ℓ' (subst σ d)` requires the level-`ℓ'` occurrence *count* to survive substitution — false
in general even when `ℓ' ≠ 0` (the ambient ordinarily-only-touches-level-0 case): if `d` has an
ambient level-0 leaf and `σ` happens to map it to something containing a *fresh* level-`ℓ'` occurrence,
the count changes. This is the **same `hclean` condition** `substAt_substAt_comm` already needs (proven
in the first commit above) — not a new obstruction, just the arity-bookkeeping shadow of it.

**Resolution**: the continuation spec's step 4 already has the right answer, just needs to be read
carefully — `substScheme σ s := ⟨s.arity, s.level, Ty.subst σ s.body⟩` **carries `s.arity` forward
unchanged, does not recompute it**. Since neither `instantiate` nor `substScheme` ever *reads*
`.arity` in the level-native design (confirmed above — `instantiate`'s `args.getD` lookup is
arity-unbounded except for the mono short-circuit), `arity` is purely informational bookkeeping in this
design (e.g. for an inference algorithm's output, or a sanity display), not load-bearing for any
correctness proof. So `substScheme σ (genAt ℓ' d) = ⟨d.levels.filter(=ℓ').length, ℓ', subst σ d⟩`
need **not** equal `genAt ℓ' (subst σ d) = ⟨(subst σ d).levels.filter(=ℓ').length, ℓ', subst σ d⟩`
on the nose (their arity fields may legitimately differ under `hclean`-violating `σ`) — and that's
fine, because no downstream proof should ever need that literal equality; what `hasType_subst`
actually needs is the **instantiate-level** commutation (`subst_instantiate`-shape), which only touches
`.level`/`.body`, never `.arity`. This reframes the continuation spec's step 5 ("prove
`substScheme_genAt`-shape commutation") to target `instantiate`, not scheme-literal equality — a
sharper, easier target than the spike's `Scheme2` (which had no arity to worry about) suggested.

### Why not attempted live this session

Both subtleties above were derived by hand-tracing the definitions against `Typing.lean`'s actual
`HasType.var` rule and the arity field's real (non-)consumers — genuinely useful design corrections,
but this session had **no Lean LSP / interactive goal-state tool access** (only batch `lake build`
feedback), and flipping `genAt`/`instantiate`/`substScheme`'s logic is a live, error-prone rewrite that
cascades into ~400 lines of `Generalization.lean` (`CtxWf`, `genAt_generalizesAt`, `genArity_subst`,
`ctxWf_cons`, `ctxWf_substCtx`, `ctxWf_fixed`, `genAt_generalizes`, `genAt_closure_ready`, all currently
built on the *old* magnitude-based `genAt`) needing simultaneous redesign around levels. Better to land
this design correction as a note and stop at a green, mechanically-verified checkpoint than risk a
half-rewritten, sorry-laden intermediate state — consistent with `plan/eyg-g1-level-tagged-ty.md`'s
"Definition of done" (no sorry, exact axiom set, at every commit).

## Continuation spec for the next session (sharper than the prior note's step 6)

1. Apply the `instantiate` arity-gate fix (finding 1 above) when flipping `Scheme.instantiate` to
   level-native.
2. Do **not** expect/prove `substScheme σ (genAt ℓ' d) = genAt ℓ' (subst σ d)` as scheme equality;
   target the **instantiate-level** commutation directly (`subst_instantiate`-shape: `Ty.subst σ
   (s.instantiate args) = (substScheme σ s).instantiate (args.map (Ty.subst σ))` for `s = genAt ℓ' d`,
   `ℓ' ≠ 0`), built from `substAt_substAt_comm` (already proved, first commit) plus the arity-gated
   `instantiate`.
3. Redesign `CtxWf`/`GeneralizesAt`/`genAt_generalizesAt`/`ctxWf_cons`/`ctxWf_substCtx`/`ctxWf_fixed`/
   `genAt_generalizes`/`genAt_closure_ready` in `Generalization.lean` around `.level` instead of
   magnitude — this is the bulk of the remaining Phase 3b file-editing, now with both design subtleties
   above pre-resolved so it shouldn't hit new surprises mid-rewrite.
4. Only after 1–3 land green: level-parameterize `hasType_subst` (`Ty.substAt ℓ` throughout, not just
   `Ty.subst` for the ambient level-`0` case), per the prior note's finding 1.
5. Then Phases 4–7 unchanged in shape (re-thread `Typing.lean`'s `let_poly`, re-green
   `Machine.lean`/`Runtime.lean`/`Soundness.lean`, sanity example + report update).

A session with Lean LSP tool access (interactive goal-state inspection, not just batch `lake build`)
will move much faster through step 3's ~400-line `Generalization.lean` redesign than batch-feedback
iteration would.

## Update (same session): the level-native flip itself is now proven, not just hand-derived

After writing the above, the two design corrections (findings 1 and 2) were applied and the
level-native design was landed as an **additive prototype** — `Scheme.genAtV`/`instantiateV`/
`substSchemeV` (the `V` suffix: "level-native **v**ariant"), coexisting with the still-magnitude-based
`genAt`/`instantiate`/`substScheme` without touching any of their (or `Generalization.lean`'s) existing
call sites.

**`Scheme.subst_instantiateV`** (commit `3e25495c`) — the actual target: substitution commutes with
level-native instantiation for a scheme generalized at any nonzero level `ℓ`, given `hclean` (`σ`'s
range never mentions level `ℓ`). Proved directly from `substAt_substAt_comm` (the first commit's
result) plus a short calculation on `List.getD`/`List.map` bounds-cases. This is genuinely the
mathematical core `hasType_subst`'s `var`/`builtin` arms will need once `Typing.lean` is re-threaded —
now proven on the real 12-former `Ty` and the real `Scheme` (with its `arity` field and mono
short-circuit), not just the spike's 2-former toy model with no `arity` at all. Confirms both design
corrections (findings 1–2 above) were exactly right: the proof goes through cleanly with the
`arity = 0` short-circuit in `instantiateV` and without ever needing `substSchemeV`-after-`genAtV` to
equal `genAtV` on the substituted body.

**`CtxWfV`/`ctxWfV_cons`** (commit `58d22a0a`) — the freshness-threading discipline
(`LevelTagSpike.lean`'s `CtxWf2`/`ctxWf2_cons`, plus its closing "feeds `hclean` at every deeper level"
example) ported onto the real `Ctx`/`Scheme`, using the already-proven `Ty.clean_of_levels_lt`. This
was the one piece of the spike not yet ported by the first commit — its port is now complete.

### What's left to actually retire Phase 3b

`subst_instantiateV` + `CtxWfV` are the two pieces `hasType_subst`'s `let_poly`/`var`/`builtin` arms
need — but wiring them into the keystone (`generalizes_closure_ready`) requires a level-native
`GeneralizesAtV` (mirroring `GeneralizesAt`/`genAt_generalizesAt`), and *that* keystone bottoms out in
`closure_typed_of_lambda_subst` (`Substitution.lean`), which is built on `hasType_subst` — **still
hardcoded to level `0`** (`Ty.subst`, not `Ty.substAt ℓ`) throughout its entire induction. So the
remaining Phase 3b work is unavoidably: level-parameterize `hasType_subst` itself (`Ty.substAt ℓ`
threaded through all ~15 rule cases in `Substitution.lean`, not just the `let_poly` arm — the finding
from the prior progress note, unchanged). This is qualitatively different from everything landed this
session (which was either purely additive or a short, mechanically-checkable calculation) — it's a
large, live rewrite of an existing induction, best done with actual Lean LSP tool access (interactive
goal-state inspection at each rule case) rather than batch `lake build` iteration, which is all this
session had.

## Current state

Tree is green at commit `58d22a0a`: `lake build` 1774, spec 104/104, axioms unchanged
(`[propext, Classical.choice, Quot.sound]`), no `sorry` anywhere. Four commits this session
(`ea64f73c`, `53300a81`, `3e25495c`, `58d22a0a`), each independently green. This note plus the plan
update are the only further changes on top.
