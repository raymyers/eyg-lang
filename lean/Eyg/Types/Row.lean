import Eyg.Types.TyEquivInv

/-!
# Row membership and its `TyEquiv`-stability (Milestone T4 — row metatheory)

The remaining T4 operators (`Case`, and the record ops) need to reason about a
**label's membership in a row up to `TyEquiv`**. `RowContains row l f` says the
value row `row` carries field `l : f` somewhere along its `rowExtend` spine. The
key lemma — `tyEquiv_rowContains` — is that `TyEquiv` preserves membership (with
the field type recovered up to `TyEquiv`): equivalent rows have the same labels
carrying equivalent field types. This is what lets the `Case` *miss* branch move a
tagged value from a union into its tail (`tag ≠ head ⇒ tag ∈ tail`).
-/

namespace Eyg.Types.Ty

/-- `RowContains row l f`: the value row `row` carries `l : f` at its **first**
occurrence of `l` (the `l ≠ l'` guard skips only *distinct* heads, matching
Leijen's scoped labels — the leftmost `l` is the visible one). -/
inductive RowContains : Ty → String → Ty → Prop
  | head {l f r} : RowContains (.rowExtend l f r) l f
  | tail {l f r l' f'} : l ≠ l' → RowContains r l f → RowContains (.rowExtend l' f' r) l f

/-- **`TyEquiv` preserves (first-occurrence) row membership** (both directions,
field type up to `TyEquiv`). -/
theorem tyEquiv_rowContains {r s : Ty} (h : TyEquiv r s) :
    (∀ l f, RowContains r l f → ∃ f', RowContains s l f' ∧ TyEquiv f f') ∧
    (∀ l f, RowContains s l f → ∃ f', RowContains r l f' ∧ TyEquiv f f') := by
  induction h with
  | refl t => exact ⟨fun _ f hc => ⟨f, hc, .refl _⟩, fun _ f hc => ⟨f, hc, .refl _⟩⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ =>
      refine ⟨fun l f hc => ?_, fun l f hc => ?_⟩
      · obtain ⟨f', hc', he'⟩ := ih₁.1 l f hc
        obtain ⟨f'', hc'', he''⟩ := ih₂.1 l f' hc'
        exact ⟨f'', hc'', he'.trans he''⟩
      · obtain ⟨f', hc', he'⟩ := ih₂.2 l f hc
        obtain ⟨f'', hc'', he''⟩ := ih₁.2 l f' hc'
        exact ⟨f'', hc'', he'.trans he''⟩
  | @congrRow l f f' t t' hf ht ihf iht =>
      refine ⟨fun lq fq hc => ?_, fun lq fq hc => ?_⟩
      · cases hc with
        | head => exact ⟨f', .head, hf⟩
        | tail hg hc' => obtain ⟨g, hg', he⟩ := iht.1 _ _ hc'; exact ⟨g, .tail hg hg', he⟩
      · cases hc with
        | head => exact ⟨f, .head, hf.symm⟩
        | tail hg hc' => obtain ⟨g, hg', he⟩ := iht.2 _ _ hc'; exact ⟨g, .tail hg hg', he⟩
  | @swapRow l l' f f' t hne =>
      refine ⟨fun lq fq hc => ?_, fun lq fq hc => ?_⟩
      · cases hc with
        | head => exact ⟨f, .tail hne .head, .refl _⟩
        | tail h1 hc' => cases hc' with
            | head => exact ⟨f', .head, .refl _⟩
            | tail h2 hc'' => exact ⟨fq, .tail h2 (.tail h1 hc''), .refl _⟩
      · cases hc with
        | head => exact ⟨f', .tail hne.symm .head, .refl _⟩
        | tail h1 hc' => cases hc' with
            | head => exact ⟨f, .head, .refl _⟩
            | tail h2 hc'' => exact ⟨fq, .tail h2 (.tail h1 hc''), .refl _⟩
  -- every other former is not a value-row head, so `RowContains` is impossible
  | congrFun _ _ _ _ _ _ => exact ⟨(fun _ _ hc => nomatch hc), (fun _ _ hc => nomatch hc)⟩
  | congrList _ _ => exact ⟨(fun _ _ hc => nomatch hc), (fun _ _ hc => nomatch hc)⟩
  | congrRecord _ _ => exact ⟨(fun _ _ hc => nomatch hc), (fun _ _ hc => nomatch hc)⟩
  | congrUnion _ _ => exact ⟨(fun _ _ hc => nomatch hc), (fun _ _ hc => nomatch hc)⟩
  | congrPromise _ _ => exact ⟨(fun _ _ hc => nomatch hc), (fun _ _ hc => nomatch hc)⟩
  | congrEff _ _ _ _ _ _ => exact ⟨(fun _ _ hc => nomatch hc), (fun _ _ hc => nomatch hc)⟩
  | swapEff _ => exact ⟨(fun _ _ hc => nomatch hc), (fun _ _ hc => nomatch hc)⟩

/-- `RowContains` transported forward across a row equivalence. -/
theorem tyEquiv_rowContains_mp {r s : Ty} (h : TyEquiv r s) {l : String} {f : Ty}
    (hc : RowContains r l f) : ∃ f', RowContains s l f' ∧ TyEquiv f f' :=
  (tyEquiv_rowContains h).1 l f hc

/-- **Surface a contained label to the head**: if a row carries `l : f` (first
occurrence), the row is `TyEquiv` to `rowExtend l f rest` for some `rest` (the row
with `l` pulled to the front — Leijen's `rewrite_row` soundness, the inverse of
membership). Needs the first-occurrence guard. -/
theorem rowContains_tyEquiv {row : Ty} {l : String} {f : Ty} (hc : RowContains row l f) :
    ∃ rest, TyEquiv (.rowExtend l f rest) row := by
  induction hc with
  | head => exact ⟨_, .refl _⟩
  | @tail l f r l' f' hne _ ih =>
      obtain ⟨rest, he⟩ := ih
      exact ⟨.rowExtend l' f' rest, (TyEquiv.swapRow hne).trans (TyEquiv.congrRow (.refl _) he)⟩

/-! ## Sanity checks -/

-- `{a:Int, b:Str}` carries `b : Str` (skipping the distinct head `a`).
example : RowContains (.rowExtend "a" .integer (.rowExtend "b" .string .empty)) "b" .string :=
  .tail (by decide) .head

-- A row equivalent to one carrying `b` also carries `b`.
example {r s : Ty} (h : TyEquiv r s) (hc : RowContains r "b" .string) :
    ∃ f', RowContains s "b" f' ∧ TyEquiv .string f' := tyEquiv_rowContains_mp h hc

end Eyg.Types.Ty
