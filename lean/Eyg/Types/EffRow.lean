import Eyg.Types.Row

/-!
# Effect-row membership and its `TyEquiv`-stability (Milestone T5 — effect metatheory)

The effect layer (T5) needs to reason about an **effect label's membership in an
effect row up to `TyEquiv`**, exactly as `RowContains`/`tyEquiv_rowContains` do for
value rows (`Eyg/Types/Row.lean`). `EffContains eff l a b` says the effect row
`eff` carries operation `l : (lift a, reply b)` at its **first** occurrence.

The headline lemma — `tyEquiv_effContains` — is the effect analog of
`tyEquiv_rowContains`: `TyEquiv` preserves membership (lift/reply recovered up to
`TyEquiv`). This is the row machinery T5's effect safety needs: an emitted
operation that is a member of the ambient row stays a member across any row
reordering, and `Handle` can pull a handled operation to the head of its row
(`effContains_tyEquiv`) and re-type the residual at the tail.
-/

namespace Eyg.Types.Ty

/-- `EffContains eff l a b`: the effect row `eff` carries operation `l` with lift
type `a` and reply type `b` at its **first** occurrence of `l` (the `l ≠ l'` guard
skips only *distinct* heads, matching Leijen's scoped labels — the leftmost `l` is
the visible one). The effect-row analog of `RowContains`. -/
inductive EffContains : Ty → String → Ty → Ty → Prop
  | head {l a b t} : EffContains (.effectExtend l a b t) l a b
  | tail {l a b t l' a' b'} :
      l ≠ l' → EffContains t l a b → EffContains (.effectExtend l' a' b' t) l a b

/-- **`TyEquiv` preserves (first-occurrence) effect-row membership** (both
directions, lift/reply up to `TyEquiv`). The effect analog of
`tyEquiv_rowContains`. -/
theorem tyEquiv_effContains {r s : Ty} (h : TyEquiv r s) :
    (∀ l a b, EffContains r l a b →
      ∃ a' b', EffContains s l a' b' ∧ TyEquiv a a' ∧ TyEquiv b b') ∧
    (∀ l a b, EffContains s l a b →
      ∃ a' b', EffContains r l a' b' ∧ TyEquiv a a' ∧ TyEquiv b b') := by
  induction h with
  | refl t =>
      exact ⟨fun _ a b hc => ⟨a, b, hc, .refl _, .refl _⟩,
             fun _ a b hc => ⟨a, b, hc, .refl _, .refl _⟩⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ =>
      refine ⟨fun l a b hc => ?_, fun l a b hc => ?_⟩
      · obtain ⟨a', b', hc', ha', hb'⟩ := ih₁.1 l a b hc
        obtain ⟨a'', b'', hc'', ha'', hb''⟩ := ih₂.1 l a' b' hc'
        exact ⟨a'', b'', hc'', ha'.trans ha'', hb'.trans hb''⟩
      · obtain ⟨a', b', hc', ha', hb'⟩ := ih₂.2 l a b hc
        obtain ⟨a'', b'', hc'', ha'', hb''⟩ := ih₁.2 l a' b' hc'
        exact ⟨a'', b'', hc'', ha'.trans ha'', hb'.trans hb''⟩
  | @congrEff l a a' b b' t t' ha hb _ _ _ iht =>
      refine ⟨fun lq aq bq hc => ?_, fun lq aq bq hc => ?_⟩
      · cases hc with
        | head => exact ⟨a', b', .head, ha, hb⟩
        | tail hg hc' =>
            obtain ⟨x, y, hc'', hx, hy⟩ := iht.1 _ _ _ hc'; exact ⟨x, y, .tail hg hc'', hx, hy⟩
      · cases hc with
        | head => exact ⟨a, b, .head, ha.symm, hb.symm⟩
        | tail hg hc' =>
            obtain ⟨x, y, hc'', hx, hy⟩ := iht.2 _ _ _ hc'; exact ⟨x, y, .tail hg hc'', hx, hy⟩
  | @swapEff l l' a b a' b' t hne =>
      refine ⟨fun lq aq bq hc => ?_, fun lq aq bq hc => ?_⟩
      · cases hc with
        | head => exact ⟨_, _, .tail hne .head, .refl _, .refl _⟩
        | tail h1 hc' => cases hc' with
            | head => exact ⟨_, _, .head, .refl _, .refl _⟩
            | tail h2 hc'' => exact ⟨_, _, .tail h2 (.tail h1 hc''), .refl _, .refl _⟩
      · cases hc with
        | head => exact ⟨_, _, .tail hne.symm .head, .refl _, .refl _⟩
        | tail h1 hc' => cases hc' with
            | head => exact ⟨_, _, .head, .refl _, .refl _⟩
            | tail h2 hc'' => exact ⟨_, _, .tail h2 (.tail h1 hc''), .refl _, .refl _⟩
  -- every other former is not an effect-row head, so `EffContains` is impossible
  | congrFun _ _ _ _ _ _ => exact ⟨(fun _ _ _ hc => nomatch hc), (fun _ _ _ hc => nomatch hc)⟩
  | congrList _ _ => exact ⟨(fun _ _ _ hc => nomatch hc), (fun _ _ _ hc => nomatch hc)⟩
  | congrRecord _ _ => exact ⟨(fun _ _ _ hc => nomatch hc), (fun _ _ _ hc => nomatch hc)⟩
  | congrUnion _ _ => exact ⟨(fun _ _ _ hc => nomatch hc), (fun _ _ _ hc => nomatch hc)⟩
  | congrPromise _ _ => exact ⟨(fun _ _ _ hc => nomatch hc), (fun _ _ _ hc => nomatch hc)⟩
  | congrRow _ _ _ _ => exact ⟨(fun _ _ _ hc => nomatch hc), (fun _ _ _ hc => nomatch hc)⟩
  | swapRow _ => exact ⟨(fun _ _ _ hc => nomatch hc), (fun _ _ _ hc => nomatch hc)⟩

/-- `EffContains` transported forward across an effect-row equivalence. -/
theorem tyEquiv_effContains_mp {r s : Ty} (h : TyEquiv r s) {l : String} {a b : Ty}
    (hc : EffContains r l a b) : ∃ a' b', EffContains s l a' b' ∧ TyEquiv a a' ∧ TyEquiv b b' :=
  (tyEquiv_effContains h).1 l a b hc

/-- **Surface a contained operation to the head**: if an effect row carries
`l : (a, b)` (first occurrence), the row is `TyEquiv` to `effectExtend l a b rest`
for some `rest` (the row with `l` pulled to the front — the effect analog of
`rowContains_tyEquiv`, the inverse of membership). Needs the first-occurrence
guard. -/
theorem effContains_tyEquiv {eff : Ty} {l : String} {a b : Ty} (hc : EffContains eff l a b) :
    ∃ rest, TyEquiv (.effectExtend l a b rest) eff := by
  induction hc with
  | head => exact ⟨_, .refl _⟩
  | @tail l a b t l' a' b' hne _ ih =>
      obtain ⟨rest, he⟩ := ih
      exact ⟨.effectExtend l' a' b' rest,
        (TyEquiv.swapEff hne).trans (TyEquiv.congrEff (.refl _) (.refl _) he)⟩

/-! ## Sanity checks -/

-- `⟨log:(Str,{}), abort:(Str,Never)⟩` carries `abort` (skipping the distinct head `log`).
example : EffContains
    (.effectExtend "log" .string Ty.unit (.effectExtend "abort" .string .never .empty))
    "abort" .string .never := .tail (by decide) .head

-- An effect row equivalent to one carrying `abort` also carries `abort`.
example {r s : Ty} (h : TyEquiv r s) (hc : EffContains r "abort" .string .never) :
    ∃ a' b', EffContains s "abort" a' b' ∧ TyEquiv .string a' ∧ TyEquiv .never b' :=
  tyEquiv_effContains_mp h hc

end Eyg.Types.Ty
