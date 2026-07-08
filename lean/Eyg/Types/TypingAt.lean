import Eyg.Types.Generalization

/-!
# Level-tracking typing judgment `HasTypeAt` (G1 Phase 3b — the nested-`let_poly` deliverable)

`HasTypeAt lvl Γ e τ ε` is an **additive, parallel** copy of `HasType` that threads the ambient
de-Bruijn *level* `lvl` explicitly. It exists to close the one bookkeeping gap that blocks a
non-vacuous, arbitrary-depth `let_poly` arm of the term-substitution lemma (see
`progress/2026-07-08-G1-phase3b-hasType_substAt-nested-arm-grounded.md`).

`HasType.let_poly` records a scheme generalized at some level `n_let` and `CtxWf n_let Γ`, but **not**
the ambient level at the node, so a generic `hasType_subst` induction cannot establish `n ≤ n_let`
(needed to lift `LevelMap n σ` to `LevelMap n_let σ`). `HasTypeAt` makes the ambient level a judgment
index and has `let_poly` generalize at **exactly** `lvl`, so `n_let = lvl` by construction and the
missing fact is `rfl`.

Two design points that are *not* mechanical:

* **`lam`/`let_` store an explicit sublevel `lvl'`** (with premises `lvl ≤ lvl'` and
  `∀ i ∈ argTy.freeVars, i < lvl'`) rather than *computing* a bump from `argTy`. A computed bump
  `max lvl (argTy.genArity 0)` does **not** commute with an ambient `LevelMap lvl` substitution when
  `lvl > 0` (`genArity 0 (subst σ argTy) ≠ genArity 0 argTy` in general), so the body IH would land at
  the wrong level. A stored `lvl'` reconstructs at the *same* level, and
  `freeVars (subst σ argTy) < lvl'` follows structurally from `LevelMap lvl σ` (ambient vars `< lvl`
  map into `[0,lvl) ⊆ [0,lvl')`; fresh vars `≥ lvl` are fixed and were already `< lvl'`).
* **`let_poly` carries no `noLambdaLet`.** That predicate is the vacuity-guard the *unprovable*
  `hasType_subst` `let_poly` arm needs; here the arm is genuinely provable (`n_let = lvl`), so the
  guard is dropped and nested `Let`-binds-`Lambda` terms — the exact shape `noLambdaLet` rejects and
  the whole of Caveat 5 is about — are **genuinely accepted**.

Purely additive: `HasType`, `hasType_subst`, `HasType.let_poly`, and every soundness declaration are
untouched, so the 104/104 spec and the soundness axiom profile cannot regress.
-/

namespace Eyg.Types

open Eyg.Ir

variable {m : Type}

/-! ## Helper facts about `genAt`'s ambient free variables -/

/-- **The ambient free variables of `genAt n d` all sit below `n`.** `genAt n d` generalizes the
`≥ n` variables into its quantifier prefix; the only body variables surviving above the prefix are the
ambient `< n` ones (shifted up), so a scheme free var is `< n`. Feeds the `let_poly` arm's
`CtxWf (lvl+1) ((x, genAt lvl defnTy) :: Γ)` reassembly. -/
theorem genAt_freeVars_lt {n : Nat} {d : Ty} : ∀ i ∈ Scheme.freeVars (Scheme.genAt n d), i < n := by
  intro i hi
  rw [Scheme.mem_freeVars] at hi
  simp only [Scheme.genAt] at hi
  rw [Ty.mem_freeVars_subst] at hi
  obtain ⟨v, hv, hmem⟩ := hi
  by_cases hvn : v < n
  · simp only [Ty.reindexGen, if_pos hvn, Ty.freeVars, List.mem_singleton] at hmem
    omega
  · simp only [Ty.reindexGen, if_neg hvn, Ty.freeVars, List.mem_singleton] at hmem
    have hle : n ≤ v := Nat.le_of_not_lt hvn
    have := Ty.genArity_spec hv hle
    omega

/-! ## The level-tracking judgment -/

/-- The declarative typing judgment with an explicit ambient de-Bruijn **level** `lvl`. Mirrors
`HasType` constructor-for-constructor except that `lam`/`let_` descend to a stored fresh sublevel and
`let_poly` generalizes at exactly `lvl` (no `noLambdaLet`). -/
inductive HasTypeAt {m : Type} : Nat → Ctx → Tree.Node m → Ty → Ty → Prop where
  | var {lvl Γ x s args ε a} :
      Γ.lookup x = some s →
      HasTypeAt lvl Γ ⟨.Variable x, a⟩ (s.instantiate args) ε
  /-- Lambda: descend under the mono binding at a stored sublevel `lvl' ≥ lvl` covering `argTy`'s free
  variables (so `CtxWf lvl'` holds for the extended context). -/
  | lam {lvl lvl' Γ x body argTy εb retTy ε a} :
      lvl ≤ lvl' →
      (∀ i ∈ argTy.freeVars, i < lvl') →
      HasTypeAt lvl' ((x, .mono argTy) :: Γ) body retTy εb →
      HasTypeAt lvl Γ ⟨.Lambda x body, a⟩ (.fun argTy εb retTy) ε
  | app {lvl Γ f arg argTy εf retTy ε a} :
      HasTypeAt lvl Γ f (.fun argTy εf retTy) ε →
      Ty.EffWeaken εf ε →
      HasTypeAt lvl Γ arg argTy ε →
      HasTypeAt lvl Γ ⟨.Apply f arg, a⟩ retTy ε
  /-- Monomorphic `let`: like `lam`, descend under the mono binding at a stored sublevel. -/
  | let_ {lvl lvl' Γ x defn body defnTy bodyTy ε a} :
      HasTypeAt lvl Γ defn defnTy ε →
      lvl ≤ lvl' →
      (∀ i ∈ defnTy.freeVars, i < lvl') →
      HasTypeAt lvl' ((x, .mono defnTy) :: Γ) body bodyTy ε →
      HasTypeAt lvl Γ ⟨.Let x defn body, a⟩ bodyTy ε
  /-- **Polymorphic `let`**, generalizing at **exactly** `lvl` (so the stored generalization
  level is the ambient level *by construction*), recording `CtxWf lvl Γ`, and typing its body at
  the fresh level `lvl + 1`. **No `noLambdaLet`** — nested `Let`-binds-`Lambda` bodies are accepted. -/
  | let_poly {lvl Γ x lx lbody la body defnTy bodyTy ε a} :
      HasTypeAt lvl Γ ⟨.Lambda lx lbody, la⟩ defnTy ε →
      CtxWf lvl Γ →
      HasTypeAt (lvl + 1) ((x, Scheme.genAt lvl defnTy) :: Γ) body bodyTy ε →
      HasTypeAt lvl Γ ⟨.Let x ⟨.Lambda lx lbody, la⟩ body, a⟩ bodyTy ε
  | int {lvl Γ n ε a} : HasTypeAt lvl Γ ⟨.Integer n, a⟩ .integer ε
  | str {lvl Γ s ε a} : HasTypeAt lvl Γ ⟨.String s, a⟩ .string ε
  | bin {lvl Γ b ε a} : HasTypeAt lvl Γ ⟨.Binary b, a⟩ .binary ε
  | builtin {lvl Γ id s args ε a} :
      Builtins.scheme id = some s →
      HasTypeAt lvl Γ ⟨.Builtin id, a⟩ (s.instantiate args) ε
  | tail {lvl Γ elem ε a} : HasTypeAt lvl Γ ⟨.Tail, a⟩ (.list elem) ε
  | cons {lvl Γ elem ε a} :
      HasTypeAt lvl Γ ⟨.Cons, a⟩ (.fun elem .empty (.fun (.list elem) .empty (.list elem))) ε
  | tag {lvl Γ l elem tail ε a} :
      HasTypeAt lvl Γ ⟨.Tag l, a⟩ (.fun elem .empty (.union (.rowExtend l elem tail))) ε
  | nocases {lvl Γ ret ε a} :
      HasTypeAt lvl Γ ⟨.NoCases, a⟩ (.fun (.union .empty) .empty ret) ε
  | case_ {lvl Γ l inner eff ret tail ε a} :
      HasTypeAt lvl Γ ⟨.Case l, a⟩
        (.fun (.fun inner eff ret) .empty
          (.fun (.fun (.union tail) eff ret) .empty
            (.fun (.union (.rowExtend l inner tail)) eff ret))) ε
  | select {lvl Γ l fieldTy tail ε a} :
      HasTypeAt lvl Γ ⟨.Select l, a⟩ (.fun (.record (.rowExtend l fieldTy tail)) .empty fieldTy) ε
  | extend {lvl Γ l fieldTy row ε a} :
      HasTypeAt lvl Γ ⟨.Extend l, a⟩ (.fun fieldTy .empty
        (.fun (.record row) .empty (.record (.rowExtend l fieldTy row)))) ε
  | overwrite {lvl Γ l newTy oldTy tail ε a} :
      HasTypeAt lvl Γ ⟨.Overwrite l, a⟩ (.fun newTy .empty
        (.fun (.record (.rowExtend l oldTy tail)) .empty
          (.record (.rowExtend l newTy tail)))) ε
  | empty {lvl Γ ε a} : HasTypeAt lvl Γ ⟨.Empty, a⟩ (.record .empty) ε
  | perform {lvl Γ l a b μ ε ann} :
      HasTypeAt lvl Γ ⟨.Perform l, ann⟩ (.fun a (.effectExtend l a b μ) b) ε
  | handle {lvl Γ l lift reply tail ret ε ann} :
      HasTypeAt lvl Γ ⟨.Handle l, ann⟩ (handleTy l lift reply tail ret) ε
  | conv {lvl Γ e τ τ' ε ε'} :
      HasTypeAt lvl Γ e τ ε → Ty.TyEquiv τ τ' → Ty.TyEquiv ε ε' →
      HasTypeAt lvl Γ e τ' ε'

/-! ## Level-parameterized type substitution — the non-vacuous nested `let_poly` arm -/

/-- **Type substitution for `HasTypeAt`.** A well-typed term stays well-typed under a
`LevelMap lvl σ` ambient substitution, *including* the `let_poly` arm for arbitrarily deep nesting —
`noLambdaLet`-free analog of `hasType_subst`. The `let_poly` arm fires non-vacuously: with the
generalization level equal to the ambient level by construction, `substCtx_cons_genAt` /
`ctxWf_substCtx` reconstruct the node from the substituted sub-derivations (the
`hasType_substLM_letPoly` pattern, here on the level-tracking judgment). -/
theorem hasTypeAt_subst {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty} (σ : Nat → Ty)
    (h : HasTypeAt lvl Γ e τ ε) (hσ : Ty.LevelMap lvl σ) (hΓ : CtxWf lvl Γ) :
    HasTypeAt lvl (substCtx σ Γ) e (Ty.subst σ τ) (Ty.subst σ ε) := by
  revert hσ hΓ
  induction h with
  | @var lvl Γ x s args ε a hl =>
      intro hσ hΓ
      rw [Scheme.subst_instantiate' σ s args]
      exact HasTypeAt.var (substCtx_lookup hl)
  | @builtin lvl Γ id s args ε a hs =>
      intro hσ hΓ
      rw [Scheme.subst_instantiate' σ s args, Builtins.scheme_substScheme σ hs]
      exact HasTypeAt.builtin hs
  | @lam lvl lvl' Γ x body argTy εb retTy ε a hle hfv hbody ih =>
      intro hσ hΓ
      simp only [Ty.subst]
      refine HasTypeAt.lam hle ?_ ?_
      · intro i hi
        rw [Ty.mem_freeVars_subst] at hi
        obtain ⟨w, hw, hwi⟩ := hi
        obtain ⟨hfix, hamb⟩ := hσ
        by_cases hwlvl : w < lvl
        · exact Nat.lt_of_lt_of_le (hamb w hwlvl i hwi) hle
        · rw [hfix w (Nat.le_of_not_lt hwlvl), Ty.freeVars, List.mem_singleton] at hwi
          rw [hwi]; exact hfv w hw
      · have hΓ' : CtxWf lvl' ((x, .mono argTy) :: Γ) := by
          rw [ctxWf_cons]
          exact ⟨by rw [Scheme.freeVars_mono]; exact hfv, hΓ.mono hle⟩
        have hb := ih (hσ.mono hle) hΓ'
        simpa only [substCtx_cons, Scheme.substScheme_mono] using hb
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg ihf iharg =>
      intro hσ hΓ
      have hf' := ihf hσ hΓ
      simp only [Ty.subst] at hf'
      exact HasTypeAt.app hf' (Ty.subst_effWeaken σ hw) (iharg hσ hΓ)
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody ihdefn ihbody =>
      intro hσ hΓ
      have hΓ' : CtxWf lvl' ((x, .mono defnTy) :: Γ) := by
        rw [ctxWf_cons]
        exact ⟨by rw [Scheme.freeVars_mono]; exact hfv, hΓ.mono hle⟩
      have hb := ihbody (hσ.mono hle) hΓ'
      simp only [substCtx_cons, Scheme.substScheme_mono] at hb
      exact HasTypeAt.let_ (ihdefn hσ hΓ) hle
        (by intro i hi
            rw [Ty.mem_freeVars_subst] at hi
            obtain ⟨w, hw, hwi⟩ := hi
            obtain ⟨hfix, hamb⟩ := hσ
            by_cases hwlvl : w < lvl
            · exact Nat.lt_of_lt_of_le (hamb w hwlvl i hwi) hle
            · rw [hfix w (Nat.le_of_not_lt hwlvl), Ty.freeVars, List.mem_singleton] at hwi
              rw [hwi]; exact hfv w hw)
        hb
  | @let_poly lvl Γ x lx lbody la body defnTy bodyTy ε a hdefn hcw hbody ihdefn ihbody =>
      intro hσ hΓ
      have hdefn' := ihdefn hσ hΓ
      have hΓ1 : CtxWf (lvl + 1) ((x, Scheme.genAt lvl defnTy) :: Γ) := by
        rw [ctxWf_cons]
        exact ⟨fun i hi => Nat.lt_succ_of_lt (genAt_freeVars_lt i hi), hcw.mono (Nat.le_succ lvl)⟩
      have hb := ihbody (hσ.mono (Nat.le_succ lvl)) hΓ1
      rw [substCtx_cons_genAt hσ x defnTy Γ] at hb
      exact HasTypeAt.let_poly hdefn' (ctxWf_substCtx hcw hσ) hb
  | int => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.int
  | str => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.str
  | bin => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.bin
  | tail => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.tail
  | cons => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.cons
  | tag => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.tag
  | nocases => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.nocases
  | case_ => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.case_
  | select => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.select
  | extend => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.extend
  | overwrite => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.overwrite
  | empty => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.empty
  | perform => intro hσ hΓ; simp only [Ty.subst]; exact HasTypeAt.perform
  | @handle lvl Γ l lift reply tail ret ε a =>
      intro hσ hΓ
      have heq : Ty.subst σ (handleTy l lift reply tail ret)
          = handleTy l (Ty.subst σ lift) (Ty.subst σ reply) (Ty.subst σ tail)
              (Ty.subst σ ret) := by
        simp [handleTy, handlerTy, execTy, kontTy, Ty.subst]
      rw [heq]; exact HasTypeAt.handle
  | conv _ hτ hε ih =>
      intro hσ hΓ
      exact HasTypeAt.conv (ih hσ hΓ) (Ty.subst_tyEquiv σ hτ) (Ty.subst_tyEquiv σ hε)

/-! ## The nested-`let_poly` deliverable: a term `noLambdaLet` rejects, typed and re-substituted

The exact shape Caveat 5 / `Tree.Node.noLambdaLet` reject: a `let` binding a `Lambda`, nested inside
another generalized lambda's body — `let outer = \x. (let inner = \y. y in inner x) in outer 1`,
generalized twice. `HasTypeAt` accepts it (no `noLambdaLet`), and `hasTypeAt_subst` re-types it
under a genuine, non-identity ambient substitution — the "does the wall fall" check. -/

section NestedExample
open Eyg.Ir.Tree

/-- The **inner core**, at ambient level `1`, inside the outer lambda's body: a generalized `let`
binding the polymorphic identity `\y. y`, applied to the ambient (polymorphic) `x : α`. This is a
`Let`-binds-`Lambda` node — `noLambdaLet` of it is `False`, so `hasType_subst` cannot reach it; it
generalizes `inner` to `∀β. β → β` at level `1` and instantiates it at `x`'s type. -/
theorem hInner :
    HasTypeAt (m := Unit) 1 [("x", .mono (.var 0 0))]
      (let_ "inner" (lambda "y" (variable_ "y")) (apply (variable_ "inner") (variable_ "x")))
      (.var 0 0) .empty := by
  refine HasTypeAt.let_poly (defnTy := .fun (.var 0 1) .empty (.var 0 1)) ?_ ?_ ?_
  · refine HasTypeAt.lam (lvl' := 2) (by omega) ?_ ?_
    · intro i hi; simp only [Ty.freeVars, List.mem_singleton] at hi; omega
    · exact HasTypeAt.var (s := .mono (.var 0 1)) (args := []) rfl
  · intro b hb i hi
    simp only [List.mem_singleton] at hb; subst hb
    simp only [Scheme.freeVars_mono, Ty.freeVars, List.mem_singleton] at hi; omega
  · refine HasTypeAt.app (argTy := .var 0 0) (εf := .empty) ?_ (Ty.effWeaken_refl _) ?_
    · exact HasTypeAt.var (s := Scheme.genAt 1 (.fun (.var 0 1) .empty (.var 0 1)))
        (args := [.var 0 0]) rfl
    · exact HasTypeAt.var (s := .mono (.var 0 0)) (args := []) rfl

/-- The **whole nested term** type-checks under `HasTypeAt` at level `0`: `outer` is generalized to
`∀α. α → α` (its body itself contains the generalized `inner` `let`, nested under the `\x` binder),
then instantiated at `integer` by `outer 1`. Reuses `hInner` verbatim as the outer lambda's body. -/
theorem hOuter :
    HasTypeAt (m := Unit) 0 []
      (let_ "outer"
        (lambda "x" (let_ "inner" (lambda "y" (variable_ "y"))
          (apply (variable_ "inner") (variable_ "x"))))
        (apply (variable_ "outer") (integer 1)))
      .integer .empty := by
  refine HasTypeAt.let_poly (defnTy := .fun (.var 0 0) .empty (.var 0 0)) ?_ ?_ ?_
  · refine HasTypeAt.lam (lvl' := 1) (by omega) ?_ hInner
    intro i hi; simp only [Ty.freeVars, List.mem_singleton] at hi; omega
  · intro b hb; exact absurd hb (by simp)
  · refine HasTypeAt.app (argTy := .integer) (εf := .empty) ?_ (Ty.effWeaken_refl _) ?_
    · exact HasTypeAt.var (s := Scheme.genAt 0 (.fun (.var 0 0) .empty (.var 0 0)))
        (args := [.integer]) rfl
    · exact HasTypeAt.int

/-- The genuine, non-identity ambient substitution `α ↦ integer` (level-`0` variable `0`), the
identity elsewhere — a `LevelMap 1` (so `hasTypeAt_subst` applies at the inner core's level `1`). -/
def σα : Nat → Ty := fun i => if i = 0 then .integer else .var 0 i

/-- **`hasTypeAt_subst` re-types the nested `let_poly` term non-vacuously.** Applying the
substitution `α ↦ integer` to `hInner` (via `hasTypeAt_subst`) produces the *substituted* re-typing:
the `Let`-binds-`Lambda` term now types at `integer` under `x : integer` — the ambient variable `α`
is genuinely replaced, and the polymorphic `inner` `let` is re-generalized in the new context.
This is the "wall falls" check: the arm fires for a term `noLambdaLet` rejects, under a substitution
that is not the identity. -/
theorem hInner_subst :
    HasTypeAt (m := Unit) 1 [("x", .mono .integer)]
      (let_ "inner" (lambda "y" (variable_ "y")) (apply (variable_ "inner") (variable_ "x")))
      .integer .empty := by
  have hσ : Ty.LevelMap 1 σα := by
    refine ⟨fun i hi => ?_, fun i hi w hw => ?_⟩
    · simp only [σα, if_neg (by omega : ¬ i = 0)]
    · have : i = 0 := by omega
      subst this
      exact absurd hw (by simp [σα, Ty.freeVars])
  have hΓ : CtxWf 1 [("x", Scheme.mono (.var 0 0))] := by
    intro b hb i hi
    simp only [List.mem_singleton] at hb; subst hb
    simp only [Scheme.freeVars_mono, Ty.freeVars, List.mem_singleton] at hi; omega
  have h := hasTypeAt_subst σα hInner hσ hΓ
  have e2 : substCtx σα [("x", Scheme.mono (.var 0 0))] = [("x", Scheme.mono .integer)] := rfl
  rw [e2] at h
  exact h

end NestedExample

end Eyg.Types
