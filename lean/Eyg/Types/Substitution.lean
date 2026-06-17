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

/-- **Type substitution for `HasType`.** A well-typed term stays well-typed under an
ambient type substitution `σ`, with the type, effect row, and context all
substituted. -/
theorem hasType_subst {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty} (σ : Nat → Ty)
    (h : HasType Γ e τ ε) :
    HasType (substCtx σ Γ) e (Ty.subst σ τ) (Ty.subst σ ε) := by
  induction h with
  | @var Γ x s args ε a hl =>
      rw [Scheme.subst_instantiate' σ s args]
      exact HasType.var (substCtx_lookup hl)
  | @builtin Γ id s args ε a hs =>
      rw [Scheme.subst_instantiate' σ s args, Builtins.scheme_substScheme σ hs]
      exact HasType.builtin hs
  | @lam Γ x body argTy εb retTy ε a hbody ih =>
      simp only [substCtx_cons, Scheme.substScheme_mono] at ih
      simp only [Ty.subst]
      exact HasType.lam ih
  | @app Γ f arg argTy retTy ε a hf harg ihf iharg =>
      simp only [Ty.subst] at ihf
      exact HasType.app ihf iharg
  | @let_ Γ x defn body defnTy bodyTy ε a hdefn hbody ihdefn ihbody =>
      simp only [substCtx_cons, Scheme.substScheme_mono] at ihbody
      exact HasType.let_ ihdefn ihbody
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
  | conv _ hτ hε ih => exact HasType.conv ih (Ty.subst_tyEquiv σ hτ) (Ty.subst_tyEquiv σ hε)

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

/-- Value-substitution for a **closure** whose captured context `σ` fixes. The
heart of `gen` soundness: re-type the closure at the substituted arrow, reusing the
term-level `hasType_subst` for the body and the unchanged `EnvWf` for the env. -/
theorem hasTypeV_subst_closure {x : String} {body : Tree.Node m} {env : Env m} {τ : Ty}
    (σ : Nat → Ty) (h : HasTypeV (.Closure x body env) τ)
    (hclo : ∀ Γc, EnvWf env Γc → substCtx σ Γc = Γc) :
    HasTypeV (.Closure x body env) (Ty.subst σ τ) := by
  cases h with
  | closure henv hbody he =>
      have hfix := hclo _ henv
      refine HasTypeV.closure henv ?_ (Ty.subst_tyEquiv σ he)
      have hb := hasType_subst σ hbody
      rw [substCtx_cons, Scheme.substScheme_mono, hfix] at hb
      exact hb

end Eyg.Types
