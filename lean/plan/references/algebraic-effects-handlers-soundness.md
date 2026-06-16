# Type-and-Effect Soundness for Algebraic Effects & Handlers

> Reference summary for the EYG type-soundness plan (`../eyg-type-soundness.md`),
> milestones **T3** (Perform/Handle typing rules), **T4** (handler/Delimit frame
> + resumption typing), **T5/T6** (effect safety in Preservation/Progress).
> Row-based effect systems — metatheory survey.

**Citation / source URLs:**

- Daan Leijen, *Type Directed Compilation of Row-Typed Algebraic Effects*, POPL 2017 —
  https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/algeff.pdf ·
  https://dl.acm.org/doi/10.1145/3093333.3009872
- Daniel Hillerström & Sam Lindley, *Liberating Effects with Rows and Handlers*, TyDe 2016 —
  https://dl.acm.org/doi/10.1145/2976022.2976033
- Hillerström & Lindley, *Shallow Effect Handlers* (extended), APLAS 2018 —
  http://homepages.inf.ed.ac.uk/slindley/papers/shallow-extended.pdf
- Daniel Hillerström, *Foundations for Programming and Implementing Effect Handlers*, PhD thesis, Edinburgh 2021/22 —
  https://www.dhil.net/research/papers/thesis.pdf
- Lindley, McBride, McLaughlin, *Do Be Do Be Do*, POPL 2017 (Frank) —
  https://arxiv.org/pdf/1611.09259
- Bauer & Pretnar, *An Effect System for Algebraic Effects and Handlers*, LMCS 2014 —
  https://arxiv.org/abs/1306.6316 ; *Programming with Algebraic Effects and Handlers*, JLAMP 2015 —
  https://arxiv.org/abs/1203.1539
- Biernacki, Piróg, Polesiuk, Sieczkowski, *Handle with Care*, POPL 2018 —
  https://doi.org/10.1145/3158096 ; *Abstracting Algebraic Effects*, POPL 2019 —
  https://doi.org/10.1145/3290319
- de Vilhena & Pottier, *A Separation Logic for Effect Handlers*, POPL 2021 (Hazel, Coq/Iris) —
  https://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf ;
  *A Type System for Effect Handlers and Dynamic Labels*, ESOP 2023 (Coq) —
  https://link.springer.com/chapter/10.1007/978-3-031-30044-8_9
- van Rooij & Krebbers et al., *Affect: An Affine Type and Effect System*, POPL 2025 (Coq/Iris) —
  https://iris-project.org/pdfs/2025-popl-affect.pdf
- Tsuyama, Cong, Masuhara, *An Intrinsically Typed Compiler for Algebraic Effect Handlers*, PEPM 2024 (Agda) —
  https://dl.acm.org/doi/10.1145/3635800.3636968

| Source | Effect annotation | Deep/Shallow | Soundness style |
|---|---|---|---|
| Koka (Leijen 2017) | **row** of labels, scoped (dup allowed) | **deep** | subject reduction + "faulty not typeable" |
| Links (Hillerström–Lindley) | **row**, Rémy presence/absence | **both** (λ†) | progress + subject reduction; CEK via simulation |
| Frank (Lindley et al.) | abilities + adjustments (ambient) | **shallow** | subject reduction + progress |
| Eff (Bauer–Pretnar) | **set** ("dirt") of `ι#op` | **deep** | progress + preservation (**Twelf-mechanized**) |
| Wrocław (Biernacki et al.) | **row** (Koka-style, dup allowed) | **deep** | logrel (2018) / progress+preservation (2019) |

---

## 1. How an effect row attaches to types

Every row-based system splits **value types** from **computation/dirty types** and
parks the effect on the function arrow. Judgment shape `Γ ⊢ e : τ ! ε`.

**Koka** (closest to EYG): effects appear *only on arrows* `τ →ᵋ τ'`; values are
pure. Rows: `⟨⟩`, tail var `µ`, `⟨l | ε⟩`; **only the tail may be polymorphic**.
**Duplicate labels meaningful** (`⟨exc, exc⟩ ≠ ⟨exc⟩`, scoped labels). Row equiv
`≅`: reflexivity, head congruence, transitivity, **swap** `l₁ ≠ l₂ ⟹ ⟨l₁|⟨l₂|ε⟩⟩
≅ ⟨l₂|⟨l₁|ε⟩⟩`. No lacks/absence constraints. **EYG's `Fun(argType, effectRow,
returnType)` is literally Koka's `τ →ᵋ τ'`.**

Links: `C ::= A ! E`, Rémy-style rows with presence polymorphism. Eff: set-based
dirt `Δ` with subtyping `Δ ⊆ Δ'` (not rows). Frank: ambient abilities pushed
*inward* (less applicable to EYG's explicit threading).

## 2. Typing rules — perform (adds) / handle (discharges)

**perform — Koka has no dedicated rule.** Operations are typed like variables,
each declared `op : τ →⟨l⟩ τ' | ⟨⟩` — a *singleton row* on its arrow. The effect
enters the ambient row through `App` (which forces function-effect = arg-effect =
ambient `ε`) plus `open` (a closed function effect grows a fresh tail to unify):

```
Γ ⊢ e₁ : τ₂ →ᵋ τ | ε     Γ ⊢ e₂ : τ₂ | ε             Γ ⊢ e : τ₁ →⟨l₁..lₙ⟩ τ₂ | ε
──────────────────────────────────────── [App]      ──────────────────────────────────── [open]
Γ ⊢ e₁(e₂) : τ | ε                                   Γ ⊢ e : τ₁ →⟨l₁..lₙ | ε'⟩ τ₂ | ε
```

> **EYG's `perform l : Fun(a, EffectExtend(l,(a,b),Empty), b)` is exactly Koka's
> `op : τ →⟨l⟩ τ' | ⟨⟩`.** No bespoke perform rule needed beyond that arrow type.

Links `T-Do`: `Γ ⊢ V : A, E = {ℓ:A→B; R} ⟹ Γ ⊢ (do ℓ V)ᴱ : B ! E`.

**handle — Koka `[Handle]`** (input row `⟨l | ε⟩` → output `ε`; `l` discharged):

```
Γ ⊢ e : τ | ⟨l | ε⟩          Σ(l) = {op₁..opₙ}
Γ, x : τ ⊢ er : τr | ε        Γ ⊢ opᵢ : τᵢ →⟨l⟩ τ'ᵢ | ⟨⟩
Γ, resume : τ'ᵢ →ᵋ τr, xᵢ : τᵢ ⊢ eᵢ : τr | ε
──────────────────────────────────────────────────────────────────── [Handle]
Γ ⊢ handle{ op₁(x₁)→e₁; …; return x→er }(e) : τr | ε
```

Three load-bearing facts: (i) input `⟨l|ε⟩` → output `ε` (**l discharged**);
(ii) `Σ(l)` requires *all* operations of `l` handled; (iii) `resume : τ'ᵢ →ᵋ τr`
— op-result → handler answer under the **already-discharged** row `ε` (deep). Eff,
Links, Wrocław agree (resumption: op-result → discharged row → handler answer).

## 3. Operational semantics — finding the handler & typing the resumption

**Evaluation-context form (Koka).** Two grammars — general `E` and `Xop` with
side-condition `op ∉ h`:

```
(return) handle{h}(v)          −→ er[x ↦ v]
(handle) handle{h}(Xop[op(v)]) −→ e[x ↦ v, resume ↦ λy. handle{h}(Xop[y])]
```

`op ∉ h` on `Xop` is *how perform finds its handler* (nearest enclosing). The
resumption `λy. handle{h}(Xop[y])` **re-wraps `h`** ⇒ **deep**.

**The CEK / segmented-stack machine (Hillerström–Lindley) — the EYG model.**
Continuation `κ` is a **two-level segmented stack** (pure `let`-frames grouped per
enclosing handler) plus a forwarding continuation `κ'`:

```
M-Do      handler frame on top handles ℓ ⟹ bind r ↦ (κ' ++ [frame])ᴮ   -- DEEP: handler retained
M-Do†     handler frame on top handles ℓ ⟹ bind r ↦ (κ', σ)ᴮ           -- SHALLOW: handler discarded
M-Forward top frame does NOT handle ℓ ⟹ pop it, append to κ', retry     -- walk to nearest handler
```

`M-Forward` is **exactly EYG's "perform walks the stack to the nearest Delimit
frame."** Deep resumption = reified continuation *including* the handler frame;
shallow resumption = a pair `(κ', σ)` with the handler **discarded**. Captured
continuations typed by input type `κᴬ`.

> **Verified caveat:** these sources have **no separate machine-configuration
> typing judgment.** Machine soundness is by *simulation* against the typed source
> semantics, not by frame typing. Typing EYG's CEK frames directly is a *novel*
> obligation; nearest precedent is the PEPM-2024 intrinsically-typed Agda machine.

## 4. Progress & Preservation — statements + key lemmas

Recurring pattern: a **normal form** is "a value **or** an op-call whose label is
in the ambient row", and **progress allows the op-call case** — that is *effect
safety*.

- **Koka:** preservation `Γ ⊢ e₁ : τ|ε ∧ e₁ ⟼ e₂ ⟹ Γ ⊢ e₂ : τ|ε`. *Lemma 4
  (faulty not typeable) = effect safety:* if `Γ ⊢ Xop[op(v)] : τ|ε` with `op ∈
  Σ(l)`, then `l ∈ ε`.
- **Eff (cleanest, Twelf-mechanized):** *Progress:* `⊢ c : A!Δ ⟹ c ⇝ c'`, or
  `c = val e`, or `c = ι#op e (x.c')` with `ι#op ∈ Δ`. *Preservation:*
  `⊢ c : C ∧ c ⇝ c' ⟹ ⊢ c' : C`. *Corollary:* `A ! ∅` is a **purity certificate**.
- **Frank:** soundness — normal w.r.t. `Σ`, or steps; **if `Σ = ∅` then value or
  steps** (the empty-row specialization).
- Canonical-forms needed: closed value of arrow type is a closure; closed value of
  resumption type is a reified continuation. Substitution + context-replacement are
  the preservation workhorses.

## 5. Trickiest cases

1. The handle/`S-Op` reduction (reified resumption well-typed + discharged row).
2. Typing the captured context/continuation — context typing `E : (τ|⟨l|ε⟩) ⇒
   (τr|ε)` + replacement lemma; the **frame-typing** analogue for a machine is the
   novel part.
3. Deep vs shallow resumption codomain confusion (`D` vs `C`) breaks preservation.
4. Rows: duplicate labels + swap ⟹ row equality ≠ set equality; keep a clean
   `Row.equiv` and prove typing closed under it. **Never model rows as sets.**
5. Multi-shot resumptions are a *semantic* hazard (Affect POPL 2025 tracks
   one-shot/multi-shot with affine types); not an obstacle for plain
   progress+preservation, but flag if EYG resumptions are multi-shot + stateful.

## 6. Deep vs shallow — the `shallow : Bool` flag

The distinction is *exactly* whether the resumption re-installs its handler, and it
shows up in **one place: the resumption's codomain row.** (Hillerström–Lindley:
deep `r : Bᵢ → D`; shallow `r : Bᵢ → C`.)

For EYG's `shallow : Bool`, the single switch in the handler-clause rule:
- `shallow = false` (deep): `resume : Fun(replyType, tailRow, returnType)` —
  codomain under the **discharged** tail row.
- `shallow = true`: `resume : Fun(replyType, EffectExtend(l,(liftType,replyType),
  tailRow), returnType)` — codomain under the **still-undischarged** input row
  (`l` still present), because the handler is not re-installed.

Operationally the flag toggles whether the captured prefix is re-wrapped in the
Delimit frame. **Links λ† (both in one calculus) is the right template for EYG.**

## 7. Mechanization precedent

- Koka, Links, Frank, Wrocław-2019 are **pen-and-paper**. (The claim that
  Hillerström–Lindley is mechanized in Abella is **doubtful/likely false** — do not
  rely on it.)
- **Eff (2014) IS mechanized in Twelf** — cleanest syntactic progress+preservation,
  but set-based dirt, not rows.
- **Wrocław 2018:** Coq step-indexed logical-relations artifact over a row-based
  calculus.
- State of the art for mechanized handler soundness is **Coq + Iris**: Hazel (POPL
  2021), Tes (ESOP 2023 — soundness = "cannot crash or perform an unhandled
  effect," the closest analogue to EYG's goal), Affect (POPL 2025).
- **Agda intrinsic typing** (PEPM 2024): type-indexed stack machine, preservation
  by construction — closest verified *abstract-machine* treatment; a strong Lean 4
  option.
- **Bottom line:** there is **no published Lean mechanization of syntactic
  progress+preservation for a row-based handler calculus** — EYG's would be novel.

## Relevance to the EYG Lean proof

**(a) Threading the effect row.** Judgment `Γ ⊢ e : τ ! ε`; values pure (split
`Γ ⊢ V : A` from `Γ ⊢ M : A!ε`). Type `perform l` *like Koka's operation Var*
(singleton-row arrow); the label enters via application + an `open`/row-unify step.
`App` forces one shared row across function/arg/result; add row-open subsumption
`⟨⟩ ≤ ε`. **Duplicate labels meaningful** — define `Row.equiv` with the swap rule
and prove typing closed under it; do not model rows as sets.

**(b) Handler/Delimit frame typing.** Source-level `handle`: clone Koka `[Handle]`
(input `EffectExtend(l,(a,b),tail)` → output `tail`, all of `Σ(l)` handled, bind
`resume`). Machine-level Delimit frames have **no row-paper template** — two
options: (i) *simulation route* (don't type the config; prove the machine
simulates a typed contextual semantics — lower risk); (ii) *frame-typing route*
(judgment `Frame : (τ ! ⟨l|ε⟩) ⇒ (τr ! ε)`, PEPM-2024 Agda style — matches EYG's
stated goal but more work). Either way you need a **replacement/context lemma**.

**(c) Resumptions.** A resumption is a function value whose type is governed by the
`shallow` flag (Links is the template); deep = codomain under discharged
`tailRow`, value includes the Delimit frame; shallow = codomain under undischarged
input row, value is the bare prefix. Prove canonical forms: "a closed value of
resumption type is a reified continuation."

**(d) Effect safety.** State **progress with the operation escape clause**: a
well-typed closed config is (i) a value, (ii) steps, or (iii) suspended on
`perform l v` where `l ∈ ε`. Headline corollary: a closed program with ambient
row `Empty` can never be stuck on an unhandled effect (Frank's `Σ=∅`; Eff's `A!∅`
purity certificate) — EYG's "no unhandled effect outside the row."

**Top picks:** clone Koka `[Handle]` + the `perform = singleton-row Var` trick; use
Links λ† as the deep/shallow template; prefer the simulation route for the machine
unless frame-typing is specifically wanted; state effect safety as Eff/Koka do;
model rows as scoped/ordered with a swap-based `equiv`, never as sets.
