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
