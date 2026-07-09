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
theorem closure_typed_of_lambda {lvl : Nat} {Γ : Ctx} {x : String} {body : Tree.Node m} {a : m}
    {env : Env m} {τ ε : Ty} (henv : EnvWf env Γ)
    (h : HasType lvl Γ (⟨.Lambda x body, a⟩ : Tree.Node m) τ ε) :
    HasTypeV (.Closure x body env) τ := by
  obtain ⟨lvl', argTy, εb, retTy, hle, hfv, hbody, heq⟩ := inv_lambda h
  exact HasTypeV.closure henv hfv hbody heq

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
    ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l ≤ ℓ) →
      HasTypeV (Value.Closure x lbody env)
        ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) := by
  intro args hargs
  have hlam := genAtV_instantiate_lam_ready (m := m) (la := la) (ε := .empty)
    hℓ hlt hfv hbody hΓpa hΓwf args hargs
  obtain ⟨lvl'', aTy, eb, rt, hle', hfv', hbody', heq⟩ := inv_lambda hlam
  exact HasTypeV.closure henv hfv' hbody' heq

end Eyg.Types
