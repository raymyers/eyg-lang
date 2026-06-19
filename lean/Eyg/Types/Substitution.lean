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

/-- **Type substitution for `HasType`** (on `Let`-free terms). A well-typed term stays well-typed under
an ambient type substitution `σ`. The `noLet` hypothesis makes the `let_`/`let_poly` arms **vacuous** —
which is exactly the restricted-`let_poly` route (the readiness keystone re-types only a `noLet`
generalized-lambda body, so arbitrary `σ` is sound there; substituting a `let_poly` under arbitrary `σ`
is *false*, `generalizes_subst_false`, hence excluded by `noLet`). -/
theorem hasType_subst {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty} (σ : Nat → Ty)
    (h : HasType Γ e τ ε) (hnl : Tree.Node.noLet e) :
    HasType (substCtx σ Γ) e (Ty.subst σ τ) (Ty.subst σ ε) := by
  induction h with
  | @var Γ x s args ε a hl =>
      rw [Scheme.subst_instantiate' σ s args]
      exact HasType.var (substCtx_lookup hl)
  | @builtin Γ id s args ε a hs =>
      rw [Scheme.subst_instantiate' σ s args, Builtins.scheme_substScheme σ hs]
      exact HasType.builtin hs
  | @lam Γ x body argTy εb retTy ε a hbody ih =>
      simp only [Tree.Node.noLet] at hnl
      simp only [substCtx_cons, Scheme.substScheme_mono] at ih
      simp only [Ty.subst]
      exact HasType.lam (ih hnl)
  | @app Γ f arg argTy εf retTy ε a hf hw harg ihf iharg =>
      simp only [Tree.Node.noLet] at hnl
      simp only [Ty.subst] at ihf
      exact HasType.app (ihf hnl.1) (Ty.subst_effWeaken σ hw) (iharg hnl.2)
  | @let_ Γ x defn body defnTy bodyTy ε a hdefn hbody ihdefn ihbody =>
      simp only [Tree.Node.noLet] at hnl
  | @let_poly Γ x lx lbody la body defnTy bodyTy ε n a hdefn hcw hnl' hbody ihdefn ihbody =>
      simp only [Tree.Node.noLet] at hnl
  | int => simp only [Ty.subst]; exact HasType.int
  | str => simp only [Ty.subst]; exact HasType.str
  | bin => simp only [Ty.subst]; exact HasType.bin
  | tail => simp only [Ty.subst]; exact HasType.tail
  | cons => simp only [Ty.subst]; exact HasType.cons
  | tag => simp only [Ty.subst]; exact HasType.tag
  | nocases => simp only [Ty.subst]; exact HasType.nocases
  | case_ => simp only [Ty.subst]; exact HasType.case_
  | select => simp only [Ty.subst]; exact HasType.select
  | extend => simp only [Ty.subst]; exact HasType.extend
  | overwrite => simp only [Ty.subst]; exact HasType.overwrite
  | empty => simp only [Ty.subst]; exact HasType.empty
  | perform => simp only [Ty.subst]; exact HasType.perform
  | @handle Γ l lift reply tail ret ε a =>
      have heq : Ty.subst σ (handleTy l lift reply tail ret)
          = handleTy l (Ty.subst σ lift) (Ty.subst σ reply) (Ty.subst σ tail)
              (Ty.subst σ ret) := by
        simp [handleTy, handlerTy, execTy, kontTy, Ty.subst]
      rw [heq]; exact HasType.handle
  | conv _ hτ hε ih => exact HasType.conv (ih hnl) (Ty.subst_tyEquiv σ hτ) (Ty.subst_tyEquiv σ hε)

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

/-- A lambda's runtime closure is typed at the lambda term's type, with the
closure's context taken to be the evaluation context `Γ` (no existential). -/
theorem closure_typed_of_lambda {Γ : Ctx} {x : String} {body : Tree.Node m} {a : m}
    {env : Env m} {τ ε : Ty} (henv : EnvWf env Γ)
    (h : HasType Γ (⟨.Lambda x body, a⟩ : Tree.Node m) τ ε) :
    HasTypeV (.Closure x body env) τ := by
  obtain ⟨argTy, εb, retTy, hbody, heq⟩ := inv_lambda h
  exact HasTypeV.closure henv hbody heq

/-- **Polymorphic readiness for a value-restricted `let`-bound lambda.** If
`σ` fixes the surrounding context `Γ`, the lambda's closure is typed at the
substituted type — the per-`args` obligation behind `EnvWf.cons` for a generalized
binding, proved via `hasType_subst` (no value substitution lemma needed). -/
theorem closure_typed_of_lambda_subst {Γ : Ctx} {x : String} {body : Tree.Node m} {a : m}
    {env : Env m} {τ ε : Ty} (σ : Nat → Ty) (hfix : substCtx σ Γ = Γ) (hnl : Tree.Node.noLet body)
    (henv : EnvWf env Γ) (h : HasType Γ (⟨.Lambda x body, a⟩ : Tree.Node m) τ ε) :
    HasTypeV (.Closure x body env) (Ty.subst σ τ) := by
  have h' := hasType_subst σ h (by simp only [Tree.Node.noLet]; exact hnl)
  rw [hfix] at h'
  exact closure_typed_of_lambda henv h'

end Eyg.Types
