import Eyg.Types.Runtime
import Eyg.Types.G2Spike
import Eyg.Types.Generation
import Eyg.Types.ClosDisc

/-!
# G2 Phase 2 (spike) — readiness lemmas for the discipline predicate `ClosDisc`

The predicate **`ClosDisc` itself now lives in `Eyg/Types/ClosDisc.lean`** (promoted to the build tree,
before `Runtime`, so Phase 3 can store it on `HasTypeV.closure`). This file keeps the *readiness
lemmas* that consume it (they depend on `HasTypeV` + the `G2Spike` keystones, so they sit downstream);
they are promoted alongside the `G2Spike` chain when Phase 3 lands.

The interleaving wall witness `W2` (`G2Validation.lean`) shows an *arbitrary* well-typed entry
derivation to `soundness` can be interleaving (a closure whose `retTy` carries a level `≥` its own
sublevel), which the substitution/raise readiness keystone cannot discharge. Per the approved Phase-0
sign-off we **bolt the discipline on at the front door**: restrict `soundness`'s entry premise to
derivations that are *closure-disciplined* — every lambda's `retTy`/`εb` sit strictly below its
sublevel `lvl'`. Those are exactly the derivations a Rémy/OCaml-style inferencer produces (fresh, high
generalization levels), and exactly the CLOSING case the universal readiness lemma
(`genAtV_instantiate_lam_ready_universal`, finding 7) discharges at **any** args.

The only new content on the `lam`/`let_poly` arms is `retTy.levels < lvl'` and `εb.levels < lvl'`.
Unlike `HasTypeRT`, `ClosDisc` **recurses into lambda/defn bodies** (it is a static, whole-derivation
property), so it is storable on a closure value and consumed as-is at apply time.

**The `var`/`builtin` args condition (Phase 2b).** The universal readiness lemma alone covers only
MONO-capturing closures (`hΓpa_fails`): a closure that captures and uses a *polymorphic* binding — the
ordinary `let a = id in let b = \w. a w in b 5` — needs an arg-level `PolyAboveFV` avoidance. The
`var`/`builtin` arms carry the **Γ-free** condition `∀ arg level l, l = 0 ∨ s.level ≤ l`, which — via
the freshness invariant `CtxPolyBd Γ` (captured poly levels `≠ 0`, `∈ body`) + `CtxWfV s.level Γ` —
*implies* `PolyAboveFV l Γ` at every arg level (`polyAboveFV_of_argCond` below). This is exactly the
Rémy-inference shape (a scheme is instantiated at fresh vars at the current level `≥ s.level`, or at
generalized-away `0`), so it rejects nothing a real inferencer produces. The numeric floor `l < lvl'`
is eliminated by the universal raise; only this set-avoidance is recorded — and it is **carrier-free**
(`s.level` is on the scheme; `Γ` is a derivation index). Readiness for the poly-capture fragment goes
through the floor keystone (`closDisc_closure_ready_value_hybrid`).

Spike; additive; validated with `lake env lean` (independent of the WIP `Soundness.lean`).
-/

namespace Eyg.Types

open Eyg.Ir
open Eyg.Ir.Tree
open Eyg.Interpreter

variable {m : Type}


/-! ## Universal ("any args") readiness for a CLOSING closure

The universal-closing lemma `genAtV_instantiate_lam_ready_universal` takes a raise offset `o` and a
per-args bound `hargbound`. The wrapper below picks `o` = (1 + the max level appearing in `args`), so
readiness holds at **any** `args` with **no** args condition — the shape the `EnvWf.cons` promise
needs once its bounded condition is dropped. -/

/-- Every list element is `≤` the running `foldr max`. -/
private theorem le_foldr_max (x : Nat) (l : List Nat) (h : x ∈ l) :
    x ≤ l.foldr Nat.max 0 := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-- A raise offset that dominates every level occurring in `args`. -/
def argsRaiseOffset (args : List Ty) : Nat := (args.flatMap Ty.levels).foldr Nat.max 0 + 1

theorem argsRaiseOffset_pos (args : List Ty) : 1 ≤ argsRaiseOffset args := by
  simp only [argsRaiseOffset]; omega

theorem lt_of_mem_args {args : List Ty} {lvl' : Nat} {t : Ty} (ht : t ∈ args)
    {l : Nat} (hl : l ∈ t.levels) : l < lvl' + argsRaiseOffset args := by
  have : l ∈ args.flatMap Ty.levels := List.mem_flatMap.mpr ⟨t, ht, hl⟩
  have := le_foldr_max l _ this
  simp only [argsRaiseOffset]; omega

/-- **Universal readiness for a CLOSING closure — any args, no args condition.** Given a
closure-disciplined body (`retTy`/`εb`/`argTy`/`Γ` all `< lvl'`), the closure inhabits
`(genAtV ℓ (argTy→εb→retTy)).instantiateV args` for **every** `args`. Composes the wrapper offset with
`genAtV_instantiate_lam_ready_universal`. This is the readiness the front-door discipline delivers. -/
theorem closDisc_closure_ready_any {ℓ lvl' : Nat} {Γ : Ctx} {x : String}
    {lbody : Tree.Node m} {la : m} {argTy εb retTy ε : Ty}
    (hℓ : ℓ ≠ 0) (hlt : ℓ ≤ lvl') (h1 : 1 ≤ lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hret : ∀ l ∈ retTy.levels, l < lvl')
    (hεb : ∀ l ∈ εb.levels, l < lvl')
    {hbody : HasType lvl' ((x, .mono argTy) :: Γ) lbody retTy εb}
    (hΓpa : ∀ l, PolyAboveFV l Γ ⟨.Lambda x lbody, la⟩)
    (hΓwf : CtxWfV ℓ Γ) (hΓlt : CtxWfV lvl' Γ) (hΓsl : ∀ b ∈ Γ, b.2.level < lvl') :
    ∀ args, HasType ℓ Γ ⟨.Lambda x lbody, la⟩
      ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) ε :=
  fun args =>
    genAtV_instantiate_lam_ready_universal hℓ hlt h1 hfv hret hεb (hbody := hbody)
      hΓpa hΓwf hΓlt hΓsl (argsRaiseOffset args) (argsRaiseOffset_pos args) args
      (fun _ ht _ hl => lt_of_mem_args ht hl)

/-- **Universal closure-VALUE readiness from the discipline fields (MONO-capture fragment).** Mirrors
`genAtV_closure_ready_value` but with **no** args condition: given the CLOSING-case discipline
(`argTy`/`retTy`/`εb` `< lvl'`) plus the captured-context invariants, the closure value is well-typed
at `(genAtV ℓ defnTy).instantiateV args` for **every** `args`. **Caveat:** `hΓpa : ∀ l, PolyAboveFV l Γ`
is satisfiable only when the captured `Γ` is mono (see `hΓpa_fails`); the poly-capture fragment needs
the floor keystone with a retained arg-level `PolyAboveFV` condition (Phase 3). `hΓsl` is a standard
runtime invariant deferred to Phase-3 threading. -/
theorem closDisc_closure_ready_value {ℓ lvl' : Nat} {Γ : Ctx} {x : String}
    {lbody : Tree.Node m} {la : m} {argTy εb retTy : Ty}
    (hℓ : ℓ ≠ 0) (hlt : ℓ < lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hret : ∀ l ∈ retTy.levels, l < lvl')
    (hεb : ∀ l ∈ εb.levels, l < lvl')
    (hbody : HasType lvl' ((x, .mono argTy) :: Γ) lbody retTy εb)
    (hΓpa : ∀ l, PolyAboveFV l Γ ⟨.Lambda x lbody, la⟩)
    (hΓwf : CtxWfV ℓ Γ) (hΓsl : ∀ b ∈ Γ, b.2.level < lvl')
    {env : Env m} (henv : EnvWf env Γ) :
    ∀ args, HasTypeV (Value.Closure x lbody env)
      ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) := by
  intro args
  have hΓlt : CtxWfV lvl' Γ := fun b hb l hl => Nat.lt_trans (hΓwf b hb l hl) hlt
  have hlam := closDisc_closure_ready_any (ε := .empty) hℓ (Nat.le_of_lt hlt) (by omega) hfv hret hεb
    (hbody := hbody) hΓpa hΓwf hΓlt hΓsl args
  obtain ⟨lvl'', aTy, eb, rt, hle', hfv', hbody', heq⟩ := inv_lambda hlam
  exact HasTypeV.closure (Nat.le_trans (Nat.one_le_iff_ne_zero.mpr hℓ) hle') henv hfv' hbody' heq

/-! ## Phase 2b — the hybrid readiness covering the POLY-capture fragment

The bridge: the Γ-free arg condition `l = 0 ∨ ℓ ≤ l` (`ℓ = s.level`), under the standard freshness
invariant `CtxPolyBd Γ` + `CtxWfV ℓ Γ`, implies `PolyAboveFV l Γ e` at every arg level — so a
poly-capturing closure's readiness is dischargeable by the floor keystone (after the universal raise),
with **no** `∀ l` mono-only requirement. -/

/-- **Def-site ↔ use-site bridge.** The Γ-free `l = 0 ∨ ℓ ≤ l` gives `PolyAboveFV l Γ e` (`ℓ` the
closure's gen level = `s.level`): a captured poly binding's level is `≠ 0` (`CtxPolyBd`) and `< ℓ ≤ l`
(`CtxWfV ℓ Γ`), hence `≠ l`; the `l = 0` case is `≠ 0` directly. -/
theorem polyAboveFV_of_argCond {ℓ l : Nat} {Γ : Ctx} {e : Tree.Node m}
    (hnz : CtxPolyBd Γ) (hΓwf : CtxWfV ℓ Γ) (hl : l = 0 ∨ ℓ ≤ l) :
    PolyAboveFV l Γ e := by
  rcases hl with rfl | hle
  · intro x _ s hlk
    by_cases h0 : s.arity = 0
    · exact Or.inl h0
    · obtain ⟨hne0, _⟩ := hnz (x, s) (lookup_mem hlk) h0
      exact Or.inr ⟨hne0, hne0⟩
  · exact polyAboveFV_of_ctxPolyBd hnz
      (fun b hb lv hlv => Nat.lt_of_lt_of_le (hΓwf b hb lv hlv) hle)

/-- **Poly-aware readiness lemma.** `genAtV_instantiate_lam_ready_universal` with its `∀ l` mono-only
`hΓpa` split into `PolyAboveFV ℓ Γ` (at the gen level) + a per-arg-level `PolyAboveFV`. Same raise +
floor keystone mechanism; works for POLY-capturing closures. -/
theorem genAtV_ready_polyaware {ℓ lvl' : Nat} {Γ : Ctx} {x : String}
    {lbody : Tree.Node m} {la : m} {argTy εb retTy ε : Ty}
    (hℓ : ℓ ≠ 0) (hlt : ℓ ≤ lvl') (h1 : 1 ≤ lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hretTy : ∀ l ∈ retTy.levels, l < lvl')
    (hεb : ∀ l ∈ εb.levels, l < lvl')
    {hbody : HasType lvl' ((x, .mono argTy) :: Γ) lbody retTy εb}
    (hΓpaℓ : PolyAboveFV ℓ Γ ⟨.Lambda x lbody, la⟩)
    (hΓwf : CtxWfV ℓ Γ) (hΓlt : CtxWfV lvl' Γ) (hΓsl : ∀ b ∈ Γ, b.2.level < lvl')
    (o : Nat) (ho : 1 ≤ o) (args : List Ty)
    (hargbound : ∀ t ∈ args, ∀ l ∈ t.levels, l < lvl' + o)
    (hargpa : ∀ t ∈ args, ∀ l ∈ t.levels, PolyAboveFV l Γ ⟨.Lambda x lbody, la⟩) :
    HasType ℓ Γ ⟨.Lambda x lbody, la⟩
      ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) ε := by
  have hraised := hasType_fullRaise (t := lvl') (o := o) h1 hbody (le_refl lvl')
  rw [raiseCtx_U_cons, raiseScheme_U_mono h1, Ty.raiseTy_eq_self_of_levels_lt hfv,
      raiseCtx_U_eq_self
        (fun b hb => raiseScheme_U_eq_self (hΓsl b hb) (fun l hl => hΓlt b hb l hl)),
      Ty.raiseTy_eq_self_of_levels_lt hretTy, Ty.raiseTy_eq_self_of_levels_lt hεb] at hraised
  exact genAtV_instantiate_lam_ready_floor hℓ (by omega : ℓ ≤ lvl' + o)
    (fun l hl => by have := hfv l hl; omega)
    (noGenAt_of_lt hraised (by omega)) hΓpaℓ hΓwf args
    (fun t ht l hl => Or.inr (Or.inr ⟨hargbound t ht l hl, hargpa t ht l hl⟩))

/-- **Hybrid closure-VALUE readiness (POLY-capture fragment).** The promise a discipline-widened
`EnvWf.cons` stores: for every `args` satisfying the Γ-free `l = 0 ∨ ℓ ≤ l` condition (recorded on
`ClosDisc.var`/`.builtin`), the closure value inhabits `(genAtV ℓ defnTy).instantiateV args`. Covers
poly-capturing closures via `CtxPolyBd`; no mono-only requirement. -/
theorem closDisc_closure_ready_value_hybrid {ℓ lvl' : Nat} {Γ : Ctx} {x : String}
    {lbody : Tree.Node m} {la : m} {argTy εb retTy : Ty}
    (hℓ : ℓ ≠ 0) (hlt : ℓ < lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hret : ∀ l ∈ retTy.levels, l < lvl')
    (hεb : ∀ l ∈ εb.levels, l < lvl')
    (hbody : HasType lvl' ((x, .mono argTy) :: Γ) lbody retTy εb)
    (hnz : CtxPolyBd Γ) (hΓwf : CtxWfV ℓ Γ) (hΓsl : ∀ b ∈ Γ, b.2.level < lvl')
    {env : Env m} (henv : EnvWf env Γ) :
    ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ ℓ ≤ l) →
      HasTypeV (Value.Closure x lbody env)
        ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) := by
  intro args hargcond
  have hΓlt : CtxWfV lvl' Γ := fun b hb l hl => Nat.lt_trans (hΓwf b hb l hl) hlt
  have hΓpaℓ : PolyAboveFV ℓ Γ ⟨.Lambda x lbody, la⟩ :=
    polyAboveFV_of_argCond hnz hΓwf (Or.inr (le_refl ℓ))
  have hargpa : ∀ t ∈ args, ∀ l ∈ t.levels, PolyAboveFV l Γ ⟨.Lambda x lbody, la⟩ :=
    fun t ht l hl => polyAboveFV_of_argCond hnz hΓwf (hargcond t ht l hl)
  have hlam := genAtV_ready_polyaware (ε := .empty) hℓ (Nat.le_of_lt hlt) (by omega) hfv hret hεb
    (hbody := hbody) hΓpaℓ hΓwf hΓlt hΓsl (argsRaiseOffset args) (argsRaiseOffset_pos args) args
    (fun _ ht _ hl => lt_of_mem_args ht hl) hargpa
  obtain ⟨lvl'', aTy, eb, rt, hle', hfv', hbody', heq⟩ := inv_lambda hlam
  exact HasTypeV.closure (Nat.le_trans (Nat.one_le_iff_ne_zero.mpr hℓ) hle') henv hfv' hbody' heq

/-! ## Why the mono-only route was insufficient (the motivating witness, now RESOLVED by 2b)

`closDisc_closure_ready_value` requires `hΓpa : ∀ l, PolyAboveFV l Γ ⟨lam⟩`, which forces the captured
context **mono-only**. `hΓpa_fails` machine-confirms this for `Γcap = [a : ∀α.α→α]` and body `\w. a`
(the ordinary `let a = id in let b = \w. a w in b 5` poly-capture shape). Phase 2b
(`closDisc_closure_ready_value_hybrid` above) resolves it: the Γ-free `l = 0 ∨ ℓ ≤ l` arg condition
+ `CtxPolyBd`/`CtxWfV` discharge readiness for poly-capturing closures via the floor keystone. This
witness is retained as the regression pinning *why* the plain universal route needed strengthening.
See `plan/progress/2026-07-10-G2-phase2b-polycapture-RESOLVED.md`. -/

abbrev Γcap : Ctx := [("a", Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0)))]

/-- The universal route's `∀ l, PolyAboveFV l Γ ⟨lam⟩` is **false** when the closure captures and uses
a polymorphic binding — so `closDisc_closure_ready_value` does not apply to poly-capturing closures. -/
theorem hΓpa_fails : ¬ (∀ l, PolyAboveFV l Γcap ⟨.Lambda "w" (variable_ "a"), ()⟩) := by
  intro h
  have h1 := h 1
  have : (Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0))).arity = 0 ∨
      ((Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0))).level ≠ 0 ∧
       (Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0))).level ≠ 1) := by
    apply h1 "a" _ _ rfl; decide
  revert this; decide

/-! ## Inhabitation

That the discipline rejects nothing legitimate is already witnessed by the disciplined derivations in
`G2Validation.lean` — `r1_disciplined_body`, `v5`, `v6` all type at `retTy`/binder levels below their
sublevels, i.e. they are exactly the `ClosDisc`-shaped derivations. (Tagging them with `ClosDisc`
explicitly is deferred to Phase 3, where the inversion machinery for `ClosDisc` at a concrete node is
set up; the dependent-index reconstruction is awkward in isolation.) The interleaving wall `W2`
(`w2_interleave_body`) is the derivation the discipline *excludes* — its `\w` binder level 3 equals
`g`'s gen level 3, so no `ClosDisc.lam`/`let_poly` `hret` proof exists for it. -/

end Eyg.Types
