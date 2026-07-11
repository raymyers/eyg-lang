import Eyg.Types.Runtime
import Eyg.Types.G2Spike
import Eyg.Types.Generation

/-!
# G2 Phase 2 (spike) — the front-door discipline predicate `ClosDisc`

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

**Scope note (see the RISK section below).** `ClosDisc`'s `var`/`builtin` arms are currently
unconditional, and the universal readiness lemma discharges the promise **only for MONO-capturing
closures**. The de-risking probe (`hΓpa_fails`) confirms that a closure capturing and using a
*polymorphic* binding (the ordinary `let a = id in let b = \w. a w in b 5` shape) needs the args
**avoidance** condition retained — so the final `var`/`builtin` arm and the `EnvWf.cons` promise will
carry `PolyAboveFV` at the arg levels (carrier-free — `Γ` is a derivation index), falling back to the
floor keystone for that fragment. The numeric floor `l < lvl'` is still eliminated by the universal
raise; only the set-avoidance is recorded.

Spike; additive; validated with `lake env lean` (independent of the WIP `Soundness.lean`).
-/

namespace Eyg.Types

open Eyg.Ir
open Eyg.Ir.Tree
open Eyg.Interpreter

variable {m : Type}

/-- **Closure discipline** (indexed by a `HasType` derivation, `NoGenAt`-shaped). Every `lam` /
`let_poly`-defn lambda additionally has `retTy`/`εb` strictly below its sublevel `lvl'` — the CLOSING
case. Recurses into **all** sub-derivations, including lambda bodies (static discipline), so it is
storable and consumed without re-establishment. `var`/`builtin`/atomics are unconditional leaves. -/
inductive ClosDisc {m : Type} :
    {lvl : Nat} → {Γ : Ctx} → {e : Tree.Node m} → {τ ε : Ty} →
    HasType lvl Γ e τ ε → Prop where
  | var {lvl Γ x s args ε a} (hl : Γ.lookup x = some s) :
      ClosDisc (HasType.var (lvl := lvl) (Γ := Γ) (x := x) (s := s) (args := args)
        (ε := ε) (a := a) hl)
  | lam {lvl lvl' Γ x body argTy εb retTy ε a}
      (hle : lvl ≤ lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      (hret : ∀ l ∈ retTy.levels, l < lvl') (hεb : ∀ l ∈ εb.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb} :
      ClosDisc hbody → ClosDisc (HasType.lam (ε := ε) (a := a) hle hfv hbody)
  | app {lvl Γ f arg argTy εf retTy ε a}
      {hf : HasType lvl Γ f (.fun argTy εf retTy) ε} {hw : Ty.EffWeaken εf ε}
      {harg : HasType lvl Γ arg argTy ε} :
      ClosDisc hf → ClosDisc harg → ClosDisc (HasType.app (a := a) hf hw harg)
  | let_ {lvl lvl' Γ x defn body defnTy bodyTy ε a}
      {hdefn : HasType lvl Γ defn defnTy ε} (hle : lvl ≤ lvl')
      (hfv : ∀ l ∈ defnTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono defnTy) :: Γ) body bodyTy ε} :
      ClosDisc hdefn → ClosDisc hbody →
      ClosDisc (HasType.let_ (a := a) hdefn hle hfv hbody)
  | let_poly {lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a}
      (hstrict : lvl < lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      (hret : ∀ l ∈ retTy.levels, l < lvl') (hεb : ∀ l ∈ εb.levels, l < lvl')
      {hbodydefn : HasType lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb} {hcw : CtxWfV lvl Γ}
      {hbody : HasType (lvl + 1) ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body bodyTy ε} :
      ClosDisc hbodydefn → ClosDisc hbody →
      ClosDisc (HasType.let_poly (a := a) (la := la) hstrict hfv hbodydefn hcw hbody)
  | int {lvl Γ n ε a} :
      ClosDisc (HasType.int (m := m) (lvl := lvl) (Γ := Γ) (n := n) (ε := ε) (a := a))
  | str {lvl Γ s ε a} :
      ClosDisc (HasType.str (m := m) (lvl := lvl) (Γ := Γ) (s := s) (ε := ε) (a := a))
  | bin {lvl Γ b ε a} :
      ClosDisc (HasType.bin (m := m) (lvl := lvl) (Γ := Γ) (b := b) (ε := ε) (a := a))
  | builtin {lvl Γ id s args ε a} (hs : Builtins.scheme id = some s) :
      ClosDisc (HasType.builtin (lvl := lvl) (Γ := Γ) (args := args) (ε := ε) (a := a) hs)
  | tail {lvl Γ elem ε a} :
      ClosDisc (HasType.tail (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | cons {lvl Γ elem ε a} :
      ClosDisc (HasType.cons (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | tag {lvl Γ l elem tail ε a} :
      ClosDisc (HasType.tag (m := m) (lvl := lvl) (Γ := Γ) (l := l) (elem := elem)
        (tail := tail) (ε := ε) (a := a))
  | nocases {lvl Γ ret ε a} :
      ClosDisc (HasType.nocases (m := m) (lvl := lvl) (Γ := Γ) (ret := ret) (ε := ε) (a := a))
  | case_ {lvl Γ l inner eff ret tail ε a} :
      ClosDisc (HasType.case_ (m := m) (lvl := lvl) (Γ := Γ) (l := l) (inner := inner)
        (eff := eff) (ret := ret) (tail := tail) (ε := ε) (a := a))
  | select {lvl Γ l fieldTy tail ε a} :
      ClosDisc (HasType.select (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (tail := tail) (ε := ε) (a := a))
  | extend {lvl Γ l fieldTy row ε a} :
      ClosDisc (HasType.extend (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (row := row) (ε := ε) (a := a))
  | overwrite {lvl Γ l newTy oldTy tail ε a} :
      ClosDisc (HasType.overwrite (m := m) (lvl := lvl) (Γ := Γ) (l := l) (newTy := newTy)
        (oldTy := oldTy) (tail := tail) (ε := ε) (a := a))
  | empty {lvl Γ ε a} :
      ClosDisc (HasType.empty (m := m) (lvl := lvl) (Γ := Γ) (ε := ε) (a := a))
  | perform {lvl Γ l aa b μ ε ann} :
      ClosDisc (HasType.perform (m := m) (lvl := lvl) (Γ := Γ) (l := l) (a := aa) (b := b)
        (μ := μ) (ε := ε) (ann := ann))
  | handle {lvl Γ l lift reply tail ret ε ann} :
      ClosDisc (HasType.handle (m := m) (lvl := lvl) (Γ := Γ) (l := l) (lift := lift)
        (reply := reply) (tail := tail) (ret := ret) (ε := ε) (ann := ann))
  | conv {lvl Γ e τ τ' ε ε'} {h : HasType lvl Γ e τ ε}
      (hτ : Ty.TyEquiv τ τ') (hε : Ty.TyEquiv ε ε') :
      ClosDisc h → ClosDisc (HasType.conv h hτ hε)

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

/-! ## RISK CONFIRMED — the universal route covers only MONO-capturing closures

`closDisc_closure_ready_value` requires `hΓpa : ∀ l, PolyAboveFV l Γ ⟨lam⟩`. `PolyAboveFV l Γ e`
demands each free var's scheme be `arity = 0 ∨ (level ≠ 0 ∧ level ≠ l)`; for a **poly** binding
(`arity ≠ 0`) the right disjunct fails at `l = level`, so `∀ l` forces the captured context to be
**mono-only**. `hΓpa_fails` machine-confirms this for `Γcap = [a : ∀α.α→α]` and the body `\w. a`.

This is **not** an edge case: a closure that captures and *uses* an outer polymorphic binding is the
ordinary nested-polymorphism shape `let a = id in let b = \w. a w in b 5` — here `b` is `let_poly`,
its captured context holds the poly `a`, and its body uses `a`. So the universal route alone does
**not** discharge `EnvWf.cons`'s promise for such closures.

**Consequence for the design.** The `var`/`builtin` arms cannot stay fully unconditional after all: the
promise must retain the plan's args-**avoidance** condition (`arg levels ∉ polySchemeLevels Γ`, i.e.
`PolyAboveFV` at the arg levels) so the readiness lemma can avoid capturing a captured scheme's gen
level. That condition is **carrier-free** (`Γ` is a derivation index, so `PolyAboveFV l Γ e` is
computable from the index) — but it does mean the promise stays **conditional**, and the underlying
readiness must fall back to the **floor keystone** (`genAtV_instantiate_lam_ready_floor`, whose
`hargs` already carries `PolyAboveFV l Γ`) rather than the fully-universal lemma, for the poly-capture
fragment. The `l < lvl'` floor widening is still delivered by the universal raise; only the
`PolyAboveFV` avoidance must be recorded. See
`plan/progress/2026-07-10-G2-phase3-polycapture-risk-CONFIRMED.md`. -/

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
