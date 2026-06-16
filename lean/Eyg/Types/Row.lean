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

/-- `RowContains row l f`: the value row `row` carries `l : f` along its spine. -/
inductive RowContains : Ty → String → Ty → Prop
  | head {l f r} : RowContains (.rowExtend l f r) l f
  | tail {l f r l' f'} : RowContains r l f → RowContains (.rowExtend l' f' r) l f

/-- **`TyEquiv` preserves row membership** (both directions, field type up to
`TyEquiv`). Equivalent value rows carry the same labels with equivalent fields. -/
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
        | tail hc' => obtain ⟨g, hg, he⟩ := iht.1 _ _ hc'; exact ⟨g, .tail hg, he⟩
      · cases hc with
        | head => exact ⟨f, .head, hf.symm⟩
        | tail hc' => obtain ⟨g, hg, he⟩ := iht.2 _ _ hc'; exact ⟨g, .tail hg, he⟩
  | @swapRow l l' f f' t hne =>
      refine ⟨fun lq fq hc => ?_, fun lq fq hc => ?_⟩
      · cases hc with
        | head => exact ⟨f, .tail .head, .refl _⟩
        | tail hc' => cases hc' with
            | head => exact ⟨f', .head, .refl _⟩
            | tail hc'' => exact ⟨fq, .tail (.tail hc''), .refl _⟩
      · cases hc with
        | head => exact ⟨f', .tail .head, .refl _⟩
        | tail hc' => cases hc' with
            | head => exact ⟨f, .head, .refl _⟩
            | tail hc'' => exact ⟨fq, .tail (.tail hc''), .refl _⟩
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

/-! ## Sanity checks -/

-- `{a:Int, b:Str}` carries `b : Str`.
example : RowContains (.rowExtend "a" .integer (.rowExtend "b" .string .empty)) "b" .string :=
  .tail .head

-- A row equivalent to one carrying `b` also carries `b`.
example {r s : Ty} (h : TyEquiv r s) (hc : RowContains r "b" .string) :
    ∃ f', RowContains s "b" f' ∧ TyEquiv .string f' := tyEquiv_rowContains_mp h hc

end Eyg.Types.Ty
