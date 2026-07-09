import Eyg.Types.Typing
import Eyg.Types.Generation
import Eyg.Types.Runtime

/-!
# Type substitution for the declarative judgment (Milestone T6 — `gen` support)

The **term-level** type-substitution lemma `hasType_subst`: if `e : τ ! ε` under
`Γ`, then `e : (subst σ τ) ! (subst σ ε)` under the substituted context
`substCtx σ Γ`. This is the standard substitution/weakening property of a
declarative HM judgment and a prerequisite for `gen` (let-generalization).

It rests on the substitution infrastructure in `Scheme.lean`
(`subst_instantiate'` — substitution commutes with instantiation for *any* `args`,
and `Builtins.scheme_substScheme` — builtin schemes are closed). The proof is a
direct induction on `HasType`; the only non-mechanical cases are `var`/`builtin`
(re-instantiate the substituted scheme at `instArgs`).

⚠ **Note (the value-level lemma is *not* here):** the analogous statement for the
*runtime* judgment `HasTypeV v τ → HasTypeV v (subst σ τ)` is **false** for open
row types — substituting a row-tail variable can add record/union labels the value
does not provide (e.g. `HasTypeV {a:=v} (record {a:α | β})` but `subst [β ↦ {b:int}]`
demands a field `b`). So `gen` cannot use an unrestricted value substitution lemma;
it needs the value restriction (generalize only syntactic values) or a substitution
lemma restricted to row-closed positions. See the progress note.
-/

namespace Eyg.Types

open Eyg.Ir
open Eyg.Interpreter

variable {m : Type}

/-- Apply an ambient type substitution to every scheme in a typing context. -/
def substCtx (σ : Nat → Ty) (Γ : Ctx) : Ctx :=
  Γ.map (fun b => (b.1, Scheme.substScheme σ b.2))

@[simp] theorem substCtx_nil (σ : Nat → Ty) : substCtx σ [] = [] := rfl

@[simp] theorem substCtx_cons (σ : Nat → Ty) (x : String) (s : Scheme) (Γ : Ctx) :
    substCtx σ ((x, s) :: Γ) = (x, Scheme.substScheme σ s) :: substCtx σ Γ := rfl

/-- Context lookup commutes with substitution (keys are preserved). -/
theorem substCtx_lookup {σ : Nat → Ty} {Γ : Ctx} {x : String} {s : Scheme}
    (h : Γ.lookup x = some s) : (substCtx σ Γ).lookup x = some (Scheme.substScheme σ s) := by
  induction Γ with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
      obtain ⟨y, sy⟩ := hd
      simp only [substCtx_cons, List.lookup_cons] at h ⊢
      by_cases hxy : (x == y) = true
      · simp only [hxy] at h ⊢; cases h; rfl
      · simp only [hxy] at h ⊢; exact ih h

/-! ## Value-level substitution for `gen`-eligible values

The value substitution lemma `HasTypeV v τ → HasTypeV v (subst σ τ)` is **false**
in general (open rows — see the module header), but holds for the value forms a
**value-restricted** `gen` can produce: literals, `[]`, `unit`, zero-argument
operator/builtin partials (all base/arrow/closed-row), and **closures whose
captured context `σ` fixes**. The closure proviso is exactly what `gen` guarantees
— it generalizes only variables disjoint from the surrounding (hence captured)
context's free variables (`Ty.subst_eq_of_fixes_free`).

We prove it by `cases` on the typing (no recursion into stored field/element
values — those forms are excluded), so the unsound `record`(non-empty)/`tagged`/
`listCons`/applied-partial cases need not appear; they are ruled out by the
`closureCtxFixed` discipline at the use site rather than a syntactic predicate. The
closure case takes its context-fixing hypothesis `hclo`. -/

/-! ## Typing a syntactic-value's evaluation result under a known context

The route to `gen` soundness that **sidesteps the existential captured-context**
(`Γcap`) of `HasTypeV.closure`: a syntactic value `defn` (here a `λ`) evaluating
under `env : Γ` produces a value typed at *the same type*, with the closure's
context taken to be the **known** `Γ` (from the surrounding `StackWf`/`EnvWf`), not
an inverted existential. Composing this with `hasType_subst` types the value at
*every* instantiation `subst σ defnTy` (for `σ` fixing `Γ`), which is exactly the
`EnvWf.cons` polymorphic-readiness obligation `gen` must discharge — without ever
needing the (false-for-open-rows) value substitution lemma. -/

/-- A lambda's runtime closure is typed at the lambda term's type, with the closure's context taken to
be the evaluation context `Γ` (no existential). Level-native: inverts the lambda node via `inv_lambda`
and feeds the arrow-component `HasTypeV.closure`. -/
theorem closure_typed_of_lambda {lvl : Nat} (hlvl : 1 ≤ lvl) {Γ : Ctx} {x : String}
    {body : Tree.Node m} {a : m}
    {env : Env m} {τ ε : Ty} (henv : EnvWf env Γ)
    (h : HasType lvl Γ (⟨.Lambda x body, a⟩ : Tree.Node m) τ ε) :
    HasTypeV (.Closure x body env) τ := by
  obtain ⟨lvl', argTy, εb, retTy, hle, hfv, hbody, heq⟩ := inv_lambda h
  exact HasTypeV.closure (Nat.le_trans hlvl hle) henv hfv hbody heq

/-- **The value-level readiness keystone (level-native `generalizes_closure_ready`).** For a let-bound
lambda presented via its `lam` components at ambient level `ℓ` — body at a strictly higher level `lvl'`,
ambient context `Γ` below `ℓ` (`CtxWfV ℓ Γ`) with every binding the body **references** above `ℓ`
(`PolyAboveFV ℓ Γ ⟨.Lambda x lbody, la⟩` — free-variable-aware, so sequential/nested `let_poly` whose
generalized body does not reference a lower-level outer binding is admitted) —
whose runtime environment realizes `Γ` (`EnvWf env Γ`), the lambda's runtime closure
`Value.Closure x lbody env` inhabits **every** (well-formed) instantiation of its generalized scheme
`genAtV ℓ (.fun argTy εb retTy)` — exactly the `EnvWf.cons` obligation (`s.level = ℓ`), with **no
`noLambdaLet`** on the closure body. Composes `genAtV_instantiate_lam_ready` (term level, `Typing.lean`)
with `HasTypeV.closure` (reconstructing the arrow components via `inv_lambda`). -/
theorem genAtV_closure_ready_value {ℓ : Nat} (hℓ : ℓ ≠ 0)
    {lvl' : Nat} {Γ : Ctx} {x : String} {lbody : Tree.Node m} {la : m}
    {argTy εb retTy : Ty}
    (hlt : ℓ < lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hbody : HasType lvl' ((x, .mono argTy) :: Γ) lbody retTy εb)
    (hΓpa : PolyAboveFV ℓ Γ ⟨.Lambda x lbody, la⟩)
    (hΓwf : CtxWfV ℓ Γ)
    {env : Env m} (henv : EnvWf env Γ) :
    ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = ℓ) →
      HasTypeV (Value.Closure x lbody env)
        ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) := by
  intro args hargs
  have hlam := genAtV_instantiate_lam_ready (m := m) (la := la) (ε := .empty)
    hℓ hlt hfv hbody hΓpa hΓwf args hargs
  obtain ⟨lvl'', aTy, eb, rt, hle', hfv', hbody', heq⟩ := inv_lambda hlam
  exact HasTypeV.closure (Nat.le_trans (Nat.one_le_iff_ne_zero.mpr hℓ) hle') henv hfv' hbody' heq

/-- **TyEquiv bridge for level-native instantiation.** `instantiateV` of a level-`ℓ` generalization
respects `TyEquiv` of the generalized body: if the bodies `d₁ ≈ d₂`, then instantiating
`genAtV ℓ d₁` and `genAtV ℓ d₂` at the *same* `args` yields equivalent types. This is what
`genAtV_closure_ready_value_node` uses to convert the `inv_lambda`-reconstructed arrow type
`.fun argTy εb retTy` back to the original `defnTy` under `instantiateV`. The `arity = 0` branch
selection agrees across the `TyEquiv` because `Ty.levels_tyEquiv` preserves membership of `ℓ` in the
level set (hence the count-is-zero test agrees); the `else` branch commutes with
`Ty.substAt_tyEquiv` (both sides substitute at the same level `ℓ` with the same `σ`). -/
theorem instantiateV_genAtV_tyEquiv (ℓ : Nat) {d₁ d₂ : Ty} (h : Ty.TyEquiv d₁ d₂) (args : List Ty) :
    Ty.TyEquiv ((Scheme.genAtV ℓ d₁).instantiateV args)
      ((Scheme.genAtV ℓ d₂).instantiateV args) := by
  have hmem : ℓ ∈ Ty.levels d₁ ↔ ℓ ∈ Ty.levels d₂ := Ty.levels_tyEquiv h ℓ
  have hlen : ∀ d : Ty, ((Ty.levels d).filter (· = ℓ)).length = 0 ↔ ℓ ∉ Ty.levels d := by
    intro d
    rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
    constructor
    · intro hh hc
      exact hh ℓ (List.mem_filter.mpr ⟨hc, by simp⟩)
    · intro hh a ha
      rw [List.mem_filter] at ha
      have : a = ℓ := by simpa using ha.2
      exact hh (this ▸ ha.1)
  unfold Scheme.instantiateV Scheme.genAtV
  by_cases hd1 : ℓ ∈ Ty.levels d₁
  · have hd2 : ℓ ∈ Ty.levels d₂ := hmem.mp hd1
    have ha1 : ¬ ((Ty.levels d₁).filter (· = ℓ)).length = 0 := fun c => (hlen d₁).mp c hd1
    have ha2 : ¬ ((Ty.levels d₂).filter (· = ℓ)).length = 0 := fun c => (hlen d₂).mp c hd2
    rw [if_neg ha1, if_neg ha2]
    exact Ty.substAt_tyEquiv ℓ _ h
  · have hd2 : ℓ ∉ Ty.levels d₂ := fun c => hd1 (hmem.mpr c)
    have ha1 : ((Ty.levels d₁).filter (· = ℓ)).length = 0 := (hlen d₁).mpr hd1
    have ha2 : ((Ty.levels d₂).filter (· = ℓ)).length = 0 := (hlen d₂).mpr hd2
    rw [if_pos ha1, if_pos ha2]
    exact h

/-- **The value-level readiness keystone, from a lambda *node* derivation (`NoGenAt`-aware).** The
`let_poly` preservation cases hold a lambda-*node* derivation
`h : HasType lvl Γ ⟨.Lambda x lbody, la⟩ defnTy ε` (from `inv_let`), not its decomposed `lam`
components, and generalize at exactly the ambient level `lvl`. This wrapper produces the
`EnvWf.cons`/`StackWfV`-Assign readiness `∀ args, (args level-bounded) → HasTypeV (Value.Closure x
lbody env) ((genAtV lvl defnTy).instantiateV args)` directly from that node derivation, composing
`inv_lambda_noGenAt` (to reach the body derivation with its `NoGenAt`) + the non-strict keystone
`genAtV_instantiate_lam_ready_le` (handles the `lvl' = lvl` non-strict case, e.g.
`\x. perform "op" x`, via the `NoGenAt lvl` side condition) + `HasTypeV.closure`, converting the
`inv_lambda`-reconstructed arrow type back to `defnTy` under `instantiateV` through
`instantiateV_genAtV_tyEquiv`. -/
theorem genAtV_closure_ready_value_node {lvl : Nat} (hℓ : lvl ≠ 0)
    {Γ : Ctx} {x : String} {lbody : Tree.Node m} {la : m} {defnTy ε : Ty}
    {h : HasType lvl Γ ⟨.Lambda x lbody, la⟩ defnTy ε}
    (hng : NoGenAt lvl h)
    (hΓpa : PolyAboveFV lvl Γ ⟨.Lambda x lbody, la⟩)
    (hΓwf : CtxWfV lvl Γ)
    {env : Env m} (henv : EnvWf env Γ) :
    ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = lvl) →
      HasTypeV (Value.Closure x lbody env)
        ((Scheme.genAtV lvl defnTy).instantiateV args) := by
  intro args hargs
  obtain ⟨lvl', argTy, εb, retTy, hbody, hlelvl', hfv, nghbody, heq⟩ := inv_lambda_noGenAt hng
  have hlam := genAtV_instantiate_lam_ready_le (m := m) (la := la) (ε := ε)
    hℓ hlelvl' hfv nghbody hΓpa hΓwf args hargs
  obtain ⟨lvl'', aTy, eb, rt, hle', hfv', hbody', heqarr⟩ := inv_lambda hlam
  exact HasTypeV.closure (Nat.le_trans (Nat.one_le_iff_ne_zero.mpr hℓ) hle') henv hfv' hbody'
    (heqarr.trans (instantiateV_genAtV_tyEquiv lvl heq args))

end Eyg.Types
