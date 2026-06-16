---
date: 2026-06-16
milestone: T4
status: row-free operators done; row operators blocked on T1b normalization
---

# T4 — the row-machinery boundary

## Delivered (sorry-free, axioms clean, `lake build` + `lake exe spec 104/104`)

The full data-operator extension **template** is proven end-to-end and applied to
every operator whose preservation does **not** need row-membership reasoning:

- **T4a** `Empty`/`Tail` — empty record / empty list values.
- **`Cons`** (lists) — `partialConsNil`/`partialConsOne`, `listCons`,
  `canonical_list`; the cons operation (cast can't fail — `canonical_list`).
- **`Tag`** (variant injection) — `tagged`, `partialTag`.
- **`NoCases`** (empty-variant elim) — vacuous via `canonical_union_empty` (no
  value inhabits `Union Empty`), using the new `tyEquiv_unionRow` projection.

`canonical_arrow` was generalized to any `Partial`, so each operator is one
`cases hf` arm in `preservation_V`/`progress`/`reduce1Run_done_value_typed`.

## The boundary: the remaining T4 operators need row membership / normalization

`Case` and the record ops (`Select`/`Extend`/`Overwrite`) all require reasoning
about **where a label sits in a row up to `TyEquiv`**, which the declarative
`TyEquiv` inductive (refl/symm/trans/swap/congr) does not invert cheaply:

- **`Case` (match), miss branch.** `reduceCall (Match label) [branch,otherwise]`
  on a `Tagged l v` with `l ≠ label` runs `otherwise` on the value, which is typed
  `Union tail → ret`. The value is typed `Union (rowExtend label inner tail)` (the
  Match input). So preservation needs:
  > `HasTypeV (.Tagged l v) (.union (.rowExtend label inner tail)) → l ≠ label →
  >  HasTypeV (.Tagged l v) (.union tail)`
  i.e. "a tag that isn't the head lives in the tail". Inverting `tagged` gives the
  value's *natural* row `rowExtend l elem' r'` and `TyEquiv (rowExtend l elem' r')
  (rowExtend label inner tail)`; with `l ≠ label` the swap rule forces `l` into
  `tail`. Extracting that is a **row-membership inversion**.
- **`Select l`** on a record: needs the record value's sorted fields to realize
  the row and `recordGet` to find `l` (no `MissingField`) — the **sorted-record ↔
  row reconciliation** (T1 deferred item).
- **`Extend`/`Overwrite`**: build/replace a field, again via the sorted-row hinge.

## Recommended next step: finish T1b (row normalization), then these fall out

Build the deferred normalization decision procedure — `normalizeRow`/`rowInsert`,
`tyEquiv_iff : TyEquiv s t ↔ normalize s = normalize t`, and a **row-membership**
lemma (`label ∈ row` up to `TyEquiv`, with head/tail extraction). With that:

- `Case` miss-branch = the membership lemma + `tagged` re-typing at the tail.
- `Select`/`Extend`/`Overwrite` = the sorted-record realizes the (normalized) row;
  `recordGet`/`recordInsert` correspond to row lookup/extend on normal forms.

This is the single shared dependency of all four remaining T4 operators, so it is
the right thing to build next. It is sizeable (rowInsert commutation + the iff),
hence a milestone of its own rather than an inline lemma.

The four row-free operators (Cons/Tag/NoCases + Empty/Tail) are already green, so
T4's pipeline integration is proven; what remains is purely the row metatheory.

## UPDATE — `Eyg/Types/Row.lean` delivered; the scoped-label refinement

`RowContains` (membership along a row's `rowExtend` spine) and
`tyEquiv_rowContains` (TyEquiv preserves membership both ways, field type up to
TyEquiv) are **green and axiom-free**. Working out how `Case` consumes them
pinned down the remaining obligation precisely — and it is the **scoped-labels**
subtlety, exactly Leijen's reason for the `l ≠ l'` guard:

- Redesign `HasTypeV.tagged` to carry `RowContains row label fieldTy` (membership)
  rather than the head-only `TyEquiv (union (rowExtend label …)) τ`. Then:
  - **miss** (`l ≠ matchLabel`): invert `tagged` ⇒ `RowContains natRow l f`;
    `tyEquiv_rowContains_mp` to the Match input row; the head is `matchLabel ≠ l`
    so membership lands in `matchTail` ⇒ re-type at `union matchTail`. Clean with
    the current (unguarded) `RowContains`.
  - **hit** (`l = matchLabel`): `branch : inner → ret`, and the payload `v` must be
    typed at `inner` (the union's *head* field). If `RowContains` is unguarded it
    could witness a **deeper** `matchLabel` occurrence with a different field type
    ⇒ unsound. So `RowContains.tail` must carry `l ≠ l'` (first-occurrence /
    visible binding), matching Leijen's scoping.
- Adding the guard makes `tyEquiv_rowContains`'s `swapRow` cases need the
  inequality witnesses (the swap reorders two *distinct* labels), so that proof
  grows — this is the genuine scoped-label metatheory, milestone-sized.

So the next slice is: guarded `RowContains` + re-green `tyEquiv_rowContains` +
redesign `tagged`/`partialTag` + add `Case` (3 `partialMatch` arities + the
hit/miss operation) + a `Tagged` canonical form. The unguarded version committed
here is the stepping stone and validates the `tyEquiv_rowContains` shape.

## UPDATE 2 — variant fragment DONE; records are the analog

`Case`/`Tag`/`NoCases` are all green now (no `tagged` redesign was needed — the
guarded `RowContains` + `tyEquiv_rowContains_mp` + `rowContains_tyEquiv` suffice
with the original `tagged` typing). `canonical_union` added.

**Records (`Select`/`Extend`/`Overwrite`) — the remaining T4, directly analogous:**
- `recordRow : Ty → Ty` projection + `tyEquiv_recordRow` (copy `unionRow`).
- `RecordWf : List (String × Value) → Ty → Prop` — fields realize a row in
  **lock-step** (`nil ↦ empty`; `(l,v)::fs ↦ rowExtend l fieldTy rest`). The
  dynamic record is sorted, so its row is in sorted order; `TyEquiv` reorders it.
  Add `HasTypeV.record : RecordWf fields row → TyEquiv (.record row) τ →
  HasTypeV (.Record fields) τ` (the non-empty generalization of `recordNil`).
- `recordWf_get : RecordWf fields row → RowContains row l f → recordGet fields l =
  some v ∧ HasTypeV v f` (induction; `recordGet`'s `==` lookup mirrors the row
  spine). This is the **`Select` no-`MissingField`** lemma.
- `canonical_record : HasTypeV v (.record row) → ∃ fields, v = .Record fields`.
- `Select l`: invert `record`, transport `RowContains (rowExtend l ..) l ..` back
  to the value's row via `tyEquiv_rowContains`, `recordWf_get` ⇒ the field, typed.
- `Extend l` / `Overwrite l`: the result `Record (recordInsert fields l v)` is
  typed by relating `recordInsert` to a row `rowExtend`/update (a `RecordWf`
  preservation lemma under `recordInsert`).

The variant work is the template; records add only the `RecordWf` lock-step
relation and the `recordGet`/`recordInsert` ↔ row correspondence.
