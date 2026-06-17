---
date: 2026-06-17
milestone: T5 (Handle) — generalized Delimit + install discharge
status: DELIVERED (green) — install discharged; resume/perform scoped
---

# Generalized `StackWf.delimit` → `install` obligation discharged

Goal: build the row-subsumption-through-`Delimit` foundation and discharge `resume`/`install`
of `HandlerObligations`. **Result: `install` is fully discharged (green); the foundation
(`StackWf.delimit` generalized to discharge from the ambient) is in.** `resume` and `perform`
remain isolated, now precisely scoped.

## ✅ Delivered (green, `lake build` 1771 jobs, `lake exe spec` 104/104, axioms clean)

**Generalized `StackWf.delimit`** (`Machine.lean`). Before, the frame rigidly typed the
continuation `rest` at the discharged row `tail`:
```
delimit : HasTypeV handler (handlerTy lift reply tail ret) →
          StackWf rest ret tail τout →
          StackWf (Delimit l h e false :: rest) ret ⟨l:(lift,reply)|tail⟩ τout
```
Now it discharges `l` from the **ambient** `ε`, with `tail ⊑ ε`:
```
delimit : HasTypeV handler (handlerTy lift reply tail ret) →
          Ty.EffWeaken tail ε →                 -- the discharged row ⊑ the continuation ambient
          StackWf rest ret ε τout →             -- rest runs at the AMBIENT ε, not a fixed tail
          StackWf (Delimit l h e false :: rest) ret ⟨l:(lift,reply)|tail⟩ τout
```
`εInner = tail` (exact, `effWeaken_refl`) recovers the old behaviour, so `stackSeg_toStackWf`
(the `Resume`/segment composition) is unaffected. `stackWf_delimit_inv` gains an `εInner`
existential + the `EffWeaken tail εInner` it carries.

**The substitution-stable relation question is answered:** the existing
`Ty.EffWeaken := TyEquiv εf ε ∨ TyEquiv εf .empty` is exactly what `delimit` needs (it is the
relation the application frames already use, and `subst_effWeaken` keeps it substitution-
stable). No new `EffSub'` was required for this step — the membership `EffSub` (which is *not*
substitution-stable) was a red herring for the `Delimit` generalization. (A genuine
row-variable-aware subrow is still wanted for a *proper non-empty* `tail ⊊ ε`; `EffWeaken`
covers the exact (`tail ≈ ε`) and pure-discharge (`tail ≈ ∅`) cases, which is the common
fragment.)

**`install` DISCHARGED.** `install_preserves` (general, no exact-row hypothesis) proves the
`reduceDeep` handler-install successor `Apply exec :: Delimit l handler :: rest` well-typed at
`ε' = ⟨l:(lift,reply)|tail⟩`: the generalized `Delimit` takes the handle's `EffWeaken εf ε`
(with `εf ≈ tail`) directly, and `rest` stays at the call ambient `ε`. The `install` field is
**removed from `HandlerObligations`** (now just `{perform, resume}`); `preservation_V`'s two
install dispatches call `install_preserves` directly. The `ε`-free value/no-bad-crash soundness
and every headline theorem stay green with axioms `propext`/`Classical.choice`/`Quot.sound`.

## Remaining (scoped)

- **`resume`** — generalizing `Delimit` makes the deep handler run its continuation at the
  ambient `ε ⊇ tail`, so a `Resume` (latent `tail`) is now applied at `ε` in the **weakened**
  case (previously only exact). `resume_preserves_exact` (banked) covers `ε ≈ tail`; the general
  case needs genuine **subrow segment composition** — `stackSeg_toStackWf`/`partialResume`
  threading where the captured segment's bottom row is a *subrow* of the call ambient. This is
  the real continuation-typing crux; it needs the segment side of the row-subsumption story
  (a generalized `StackSegWf.delimit` + a subrow-aware `stackWf_resume`).
- **`perform`** — the hard stack-walk dispatch (design §5), independent of the above.
- **`TauKeepsRow → RowEvolves`** — now unblocked on the `Delimit` side (the generalized frame
  threads `tail ⊑ ε`); the downward `EffContains` reflection across discharges is the remaining
  content.

Net: `HandlerObligations` shrinks 3 → 2 fields; the `Delimit` row-subsumption foundation is in
and green; `resume`/`perform`/`RowEvolves` are the sharply-scoped follow-ups.
