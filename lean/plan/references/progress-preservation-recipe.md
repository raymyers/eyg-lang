# Syntactic Type Soundness: Progress + Preservation (recipe & mechanization)

> Reference summary for the EYG type-soundness plan (`../eyg-type-soundness.md`),
> overall skeleton (milestones T5/T6/T7) and binder/mechanization choices (T1).
> The canonical theorem statements and lemma DAG, adapted to EYG's *total,
> environment-based, crash-on-ill-formed* CEK semantics.

**Citation / source URLs:** Wright & Felleisen, *A Syntactic Approach to Type
Soundness*, Information and Computation 115(1):38–94, 1994
(https://dl.acm.org/doi/10.1006/inco.1994.1093); Pierce, *Types and Programming
Languages* (TAPL), ch. 8 & 9; *Software Foundations* vol. 2 (PLF), chapters
[Stlc](https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html),
[StlcProp](https://softwarefoundations.cis.upenn.edu/plf-current/StlcProp.html),
[Types](https://softwarefoundations.cis.upenn.edu/plf-current/Types.html),
[References](https://softwarefoundations.cis.upenn.edu/plf-current/References.html);
Amin & Rompf, *From F to DOT: Type Soundness Proofs with Definitional
Interpreters* (https://arxiv.org/pdf/1510.05216); Lean 4 STLC formalizations:
[ElifUskuplu/stlc](https://reservoir.lean-lang.org/@ElifUskuplu/stlc),
https://www.arxiv.org/pdf/2512.09280.

> Accuracy note: the Wright–Felleisen PDF would not machine-parse; its exact
> theorem text below is reconstructed from TAPL and secondary sources (the
> conceptual content — subject reduction, "faulty expressions," extension to
> refs/exceptions/continuations — is well-corroborated). The Software Foundations
> statements are quoted from the fetched pages and are reliable.

---

## 1. Progress and Preservation, combined

For STLC with small-step `t ---> t'` and `Γ ⊢ t : T` (`empty` = closed):

```
Theorem progress     : ∀ t T, empty ⊢ t : T → value t ∨ ∃ t', t ---> t'.
Theorem preservation : ∀ t t' T, empty ⊢ t : T → t ---> t' → empty ⊢ t' : T.
```

**Combination → Soundness.** `stuck t := normal_form step t ∧ ¬ value t`.
Soundness ("well-typed terms don't get stuck", Milner's "don't go wrong"): for
closed well-typed `t`, if `t -->* t'` then `t'` is not stuck. Proof by induction
on `-->*`: Preservation keeps `t'` well-typed; Progress says a well-typed `t'` is a
value or steps. Wright–Felleisen call the bad terms **"faulty expressions"**;
soundness = no well-typed term reduces to a faulty one (they did this for Core ML
incl. refs, exceptions, first-class continuations).

## 2. The supporting lemma DAG (leaves first)

- **Canonical Forms** — a well-typed *value* has the shape its type predicts
  (`empty ⊢ t : T1→T2 → value t → ∃ x u, t = \x:T1,u`). Used only by **Progress**.
- **Inversion of typing** — recover subderivations from a compound term's typing;
  the automatic inversion principle of the inductive (`inversion`/`cases`). Used
  pervasively.
- **Weakening / Permutation / Context-invariance** (`includedin Γ Γ' → Γ ⊢ t:T →
  Γ' ⊢ t:T`; `free_in_context`; `context_invariance`). Used only by Substitution.
- **Substitution lemma** `(x⊢>U;Γ) ⊢ t:T → empty ⊢ v:U → Γ ⊢ [x:=v]t : T`. The
  heart of substitution-based preservation; used only by the β-case.

DAG: `Inversion` underlies all; `Canonical Forms → Progress`;
`free_in_context/weakening → Substitution → Preservation`;
`Progress + Preservation → Soundness`.

## 3. Proof-by-induction structure

- **Canonical Forms:** `destruct` value evidence, `inversion` on typing; mismatches
  are contradictions.
- **Progress:** **induction on the typing derivation.** `T_Var` vacuous (empty
  ctx); values done; `T_App` uses IH on both sides + `canonical_forms_fun` for the
  β-step; `T_If` uses `canonical_forms_bool`.
- **Preservation:** **induction on the typing derivation**, then `inversion` on the
  step inside each case (typing-induction lines up the IH better than
  step-induction). Only `ST_AppAbs` needs the **Substitution lemma**.
- **Substitution lemma:** **induction on the term, generalizing `Γ` and `T`**
  (forgetting to generalize makes the IH too weak). `var` case splits `x=y` vs
  `x≠y`; `abs` case uses `update_shadow`/`update_permute`.

## 4. "Stuck = normal form, not a value" — and total/explicit-error semantics

Classical: stuck = `normal_form ∧ ¬value`; well-typed closed terms never reach it.
New failure modes are handled by **either** proving them ill-typed **or** giving
them a step to a typed `error`/exception term (Wright–Felleisen's route for
refs/exceptions).

**Total / explicit-error semantics (EYG's CEK model).** When evaluation is a
*total* relation mapping every term to an outcome in `Value ⊎ {crash, diverge}`
(Milner's `wrong`; Amin–Rompf's definitional-interpreter `wrong`/timeout), there
are *no stuck states by construction*, and the two theorems collapse into one
soundness statement:

> **Soundness (total semantics):** `empty ⊢ t : T → eval(t) ≠ crash`
> (and if `eval(t) = value v` then `v : T`).

Progress becomes "the outcome is never `crash`"; Preservation becomes
"intermediate machine states stay well-typed (under a config typing)". This is the
modern definitional-interpreter style (*From F to DOT*) and the natural shape for
an environment/closure machine — **exactly EYG's regime.**

## 5. Mechanization lessons (Coq → Lean 4)

**Binder representation (for *term* variables):**
- **Named** (SF's STLC): readable, paper-like, but pays
  `update_shadow`/`update_permute`/`update_neq` + free-variable machinery; capture
  is a hazard for open substitution.
- **de Bruijn:** no α-equivalence/capture, canonical names — but every lemma drags
  `lift`/`shift` and the **substitution-composition** lemma (the dominant cost).
- **Locally nameless** (free vars named, bound de Bruijn, cofinite quantification):
  current best-practice middle ground (2025 Lean work targets this); best
  automation-to-readability ratio, needs `open`/`close`/`lc` discipline.

**How SF structures it:** define `tm`/`ty`/`value`/`step`/`has_type`; canonical
forms; context/substitution lemmas; `progress`; `preservation`; `soundness` over
`multistep`. The substitution lemma is the engineering bottleneck.

**Automation, Coq → Lean 4:** `inversion HT; subst` → `cases`/`rcases`;
`auto`/`eauto` → **`aesop`** (prime with `@[aesop]` on typing/step constructors) or
`constructor`/`apply <;>`; `discriminate`/`congruence` → `simp`/`grind` (`grind`
subsumes much of `eauto`+`congruence`+arithmetic); de Bruijn index arithmetic →
`omega`. The β-case / substitution lemma stay **manual** in both systems.

**Pitfalls:** (a) forgetting to generalize `Γ`,`T` before inducting in
substitution; (b) inducting on the *term* in Preservation instead of the *typing
derivation*; (c) capture in named representations; (d) Lean `cases` on
non-variable indices may need `generalize`/`subst`.

## 6. Adding effects/references (store typing) — template for effect-row threading

SF's `References` chapter:
- **Store typing** `ST : list ty` assigns a type to every heap location (parallel
  to `Γ`). Judgment becomes `Γ; ST ⊢ t : T`, threading `ST` through every rule.
- `store_well_typed st ST` ties runtime store to `ST`; `extends ST' ST` — store
  typing only **grows**; **store weakening** `Γ;ST ⊢ t:T → extends ST' ST → Γ;ST'
  ⊢ t:T`.
- **Preservation (with store)** returns an **existential extended `ST'`** (alloc
  invents typings) + `store_well_typed st' ST'`; store weakening reconciles old
  derivations.

Reusable pattern: a context that (i) threads through every rule, (ii) has a
well-formedness invariant tying it to runtime state, (iii) is monotone (only
grows), (iv) gets an existential in Preservation + a weakening lemma. **Effect rows
thread identically:** carry an effect-row context, relate it to the machine's
handler/continuation state, prove row-weakening (subsumption/monotonicity),
existentially extend where effects are introduced.

## Relevance to the EYG Lean proof

EYG's dynamics is an environment-based CEK machine that is **total** (ill-formed
terms → explicit `crash`), so it sits squarely in the §4 total/explicit-error and
§6 definitional-interpreter regime. Takeaways:

- **Lemmas still needed:** **Canonical Forms** (reformulated for runtime
  values/closures — "value typed `T1→T2` is a closure `⟨λx.body,env⟩`"), **Inversion
  of typing** (free via `cases`), and a **weakening/monotonicity** lemma in the §6
  sense (for the growing effect row / store typing — existential extension in
  Preservation).
- **Lemmas you can drop:** the **Substitution lemma** and the whole named-substitution
  apparatus — replaced by environment/closure typing (`env : Γ` + "extend a
  well-typed env with a well-typed value" — the trivial `cons` lemma). See
  `abstract-machine-type-soundness.md`.
- **Phrasing Progress for a total/crash semantics:** make it non-stuckness of the
  *outcome*: `well_typed_config c → step c ≠ Crash` (or end-to-end `empty ⊢ t : T →
  eval t ≠ crash`). Preservation = a machine-configuration typing preserved by
  every non-crash transition. Soundness by induction on the run; no explicit
  `stuck` predicate needed.
- **Binder representation for EYG TYPE variables:** recommend **de Bruijn for type
  variables** — canonical types + decidable type equality for free
  (`decide`/`grind`/`omega`-friendly), no α-renaming; the substitution-composition
  cost is mild for types and concentrated in one place (term-level substitution is
  already eliminated by going environment-based). Use named/locally-nameless only
  if type vars can capture across nested binders error-prone-ly, or if readable
  type-error messages matter; locally-nameless (cofinite, per 2025 Lean work) is the
  principled fallback. If the EYG core has *no* type-level binders (monomorphic /
  row-poly-without-∀), this is moot — see plan Open Question #2/#3.
