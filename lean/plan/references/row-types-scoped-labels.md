# Extensible Records with Scoped Labels (Leijen 2005)

> Reference summary for the EYG type-soundness plan (`../eyg-type-soundness.md`),
> milestone **T1 — Types, rows, and row equivalence**. Tells us how to define
> `RowEquiv` and how it corresponds to the gleam `rewrite_row`/`rewrite_effect`.

**Citation / source URL:** Daan Leijen, "Extensible records with scoped labels,"
*Trends in Functional Programming* (TFP) 2005, pp. 179–194. Utrecht University
tech report draft (Revision 76, July 23, 2005). PDF:
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf
(mirror: https://www.cs.ioc.ee/tfp-icfp-gpce05/tfp-proc/21num.pdf). Companion
proofs: D. Leijen, "Unqualified records and variants: proofs," Tech. Report
UU-CS-2005-00, Utrecht.

Notation note: the paper writes a *row* in "banana brackets" `(| ... |)`, empty
row `(||)`, extension `(|l :: τ | r|)`. EYG's `RowExtend(label, fieldType,
tailRow)` is exactly `(|l :: τ | r|)`; EYG's `Empty` is `(||)`.

---

## 1. The core idea of scoped labels

A row is built from just two constructors (kind `row`):

- `(||)` — the empty row.
- `(|l :: τ | r|)` — row extension.

Records/variants wrap a row: record type `{r}`, variant type `⟨r⟩`.

The novel decision: **duplicate labels are allowed and retained**, in both value
and type. Extension `{l = e | r}` (*free extension*) never rejects or overwrites
an existing label — the old field is kept underneath, inducing a **scope** over
labels (a later extension shadows an earlier one, like nested binding).
Selection and restriction act on the **first matching label**:
`{x = 2, x = True}.x : Int`; `({x = 2, x = True} − x).x : Bool`. So
`(|l :: τ | r|)` means "outermost/first entry binds `l` to `τ`"; the leftmost
occurrence of a label is the visible one.

**Difference from other systems:** Gaster–Jones / TREX forbid duplicates via a
*lacks* predicate `(r \ l)` (qualified types); Rémy uses present/absent *flags*
and overwriting extension; Wand's overwrite reading loses principal types. Scoped
labels need **no extra predicates or flags** — only a new mono-type equality plus
an extended unifier.

## 2. Row equivalence / row-rewrite rule (the `RowEquiv` axioms)

Equality `(∼=)` between mono-types (paper Figure 1). Structural/congruence rules
plus the two row rules:

```
(eq-head)   τ ∼= τ'    r ∼= s
            ─────────────────────────────────
            (|l :: τ | r|) ∼= (|l :: τ' | s|)

(eq-swap)   l ≠ l'
            ─────────────────────────────────────────────────────────
            (|l :: τ, l' :: τ' | r|) ∼= (|l' :: τ', l :: τ | r|)
```

Crucial points:
- `(eq-swap)` swaps the **first two** entries **iff their labels differ**.
  Same-label entries do *not* commute — that is what preserves scoping.
  `{x::Int, x::Bool} ≇ {x::Bool, x::Int}` deliberately.
- With `(eq-trans)` + congruence `(eq-head)`, swapping bubbles any
  distinct-labelled field to the front "but not past an equal label."
- Rows are "equal up to permutation of distinct labels." Reflexivity is
  structural; `(eq-swap)` is its own inverse (symmetry); `(eq-trans)` gives
  transitivity. In a proof assistant you'll want `symm` as an explicit
  constructor.

This equality is threaded through the HM application rule (replacing syntactic
equality): `Γ ⊢ e1 : τ1→τ ∧ Γ ⊢ e2 : τ2 ∧ τ1 ∼= τ2 ⟹ Γ ⊢ e1 e2 : τ`.

## 3. Types for record operations (as written)

```
selection    ( _.l )        :: ∀r α. {l :: α | r} → α
restriction  ( _ − l )      :: ∀r α. {l :: α | r} → {r}
extension    { l = _ | _ }  :: ∀r α. α → {r} → {l :: α | r}
update       { l := _ | _ }  :: ∀r α β. α → {l :: β | r} → {l :: α | r}   -- restrict-then-extend
rename       { l ← m | _ }   :: ∀r α. {m :: α | r} → {l :: α | r}
```

Selection/restriction are safe by typing: the argument type `{l :: α | r}` forces
`l` present (it is the head *up to `∼=` reordering of distinct labels*) — this is
what `RowEquiv` must enable. Extension is "free" (no lacks, no overwrite). Update
operates on the first `l` and can change its type.

## 4. Variants reuse the same row machinery

A variant type is `⟨r⟩`; the row + equality machinery is identical ("we do not
need to change anything"). Primitives:

```
injection      ⟨ l = _ ⟩  :: ∀α r. α → ⟨l :: α | r⟩
embedding      ⟨ l | _ ⟩  :: ∀α r. r → ⟨l :: α | r⟩
decomposition  ( l ∈ _ ? _ : _ ) :: ∀α β r. ⟨l :: α | r⟩ → (α → β) → (⟨r⟩ → β) → β
```

Pattern-`case` is sugar over nested decompositions. Runtime variant values carry
a **nesting level** (injection = 0, embedding bumps it, decomposition matches
level 0 and decrements on the else-branch) — the witness of which scope a tag
belongs to. EYG models records, variant unions, AND effects as rows, so one
`RowEquiv` serves all three.

## 5. Unification (the `rewrite_row`)

Robinson unification plus the row rule `(uni-row)`: to unify `(|l :: τ | r|)` with
`s`, first **rewrite `s` to surface label `l` at its head**, then unify field
types and tails. The rewriting judgment `r ≃ (|l :: τ | s|) : θ` (paper Figure 3,
= gleam `rewrite_row`):

```
(row-head)  (|l :: τ | r|) ≃ (|l :: τ | r|) : []                  -- already at head
(row-swap)  l ≠ l'   r ≃ (|l :: τ | r'|) : θ
            ──────────────────────────────────────────────
            (|l' :: τ' | r|) ≃ (|l :: τ | l' :: τ' | r'|) : θ     -- skip distinct head
(row-var)   fresh β, γ
            α ≃ (|l :: γ | β|) : [α ↦ (|l :: γ | β|)]             -- extend a polymorphic tail
```

Termination side-condition `tail(r) ∉ dom(θ)` rejects unifying rows that share the
same tail variable with differing prefixes (else `(row-var)` loops). `(row-var)`
+ substitution only matter if you mechanize *inference*; for soundness you mostly
need `(row-head)`/`(row-swap)`.

## 6. Metatheory

- **Thm 1 (soundness of unification):** `τ ∼ τ' : θ ⟹ θτ ∼= θτ'`.
- **Thm 2 (completeness / principal unifier).** Scoped labels *restore* principal
  types where Wand's overwrite lost them.
- The paper has **no separate small-step Progress+Preservation** — soundness is at
  the unification/typing level. EYG supplies the operational layer; the paper
  gives the typing rules and the equality relation that reduction must preserve.

## 7. Mechanizing row equivalence — guidance

- `(eq-swap)` is **head-local** (touches only the first two entries) — far easier
  than "rows are multisets." Keep the `l ≠ l'` guard as a real decidable
  obligation.
- Lean `RowEquiv : Row → Row → Prop` inductive: `refl`, `symm`, `trans`,
  `head` (congruence), `swap` (with `l ≠ l'`). Bundle as a `Setoid`/`Equivalence`.
- **Strongly consider a normalization decision procedure:** prove
  `RowEquiv r s ↔ stableSortByLabel r = stableSortByLabel s` (stable sort =
  "swap distinct labels only"). Converts symm/trans/congruence into `Eq` lemmas
  and yields a decidable `RowEquiv` — usually far less painful than chaining
  `swap`/`trans`.
- Mechanize `rewrite_row` as a fuel-bounded function returning
  `Option (FieldTy × Row × Subst)`; prove `rewriteRow l r = some (τ, s, θ) →
  θ r ∼= (|l :: τ | s|)` (links algorithm to relation).
- **Binders:** use de Bruijn for term/type binders; treat row-tail variables as
  ordinary type variables; keep declarative `RowEquiv` binder-light (or
  normalized); quarantine `fresh` machinery to the optional inference layer.

## Relevance to the EYG Lean proof — takeaways

1. `Empty` = `(||)`; `RowExtend(label, fieldType, tailRow)` = `(|l :: τ | r|)`;
   visible occurrence = leftmost. Bake into `select`/`overwrite`.
2. `RowEquiv` = Figure 1 restricted to rows: `refl/symm/trans/head/swap`.
3. The `l ≠ l'` guard is load-bearing — never drop it.
4. Prefer the `stableSortByLabel` normalization route for decidability + cheap
   proofs.
5. `rewrite_row` = Figure 3; for soundness, `(row-head)`+`(row-swap)` suffice.
6. One `RowEquiv` reused for records, variant `case`, and effect rows.
7. Use de Bruijn for type binders; keep `RowEquiv` binder-light/normalized.
