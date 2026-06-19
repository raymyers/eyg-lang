import Eyg.Types.Substitution

/-!
# Let-generalization, declaratively (Milestone T6 — `gen`)

The remaining T6 let-polymorphism work needs a `gen`: bind a let's value at a
*scheme* instead of a `.mono` type, so the body can use it at many instances. The
de Bruijn route of *computing* a principal generalizing scheme (re-index the
generalizable variables to `0 … arity-1`, shift the ambient ones up) is the
fiddly part flagged in `progress/2026-06-16-T6-gen-scoping.md`.

This file takes the **declarative** route the whole judgment uses elsewhere
(`HasType.var`/`builtin` quantify over *arbitrary* instantiation `args` rather
than computing principal types): we do **not** compute `gen`. Instead a
`let_poly` rule will quantify over **any** scheme `s` that is a sound
generalization of the let's type away from the surrounding context — captured by
the predicate `Generalizes s Γ defnTy` below. Soundness needs only the predicate's
defining property; an algorithm that *produces* such a scheme is the (separate,
T8) inference layer.

The key payoff (`generalizes_closure_ready`): for a **value-restricted** `let`
(the bound `defn` is a `λ`), the predicate discharges exactly the polymorphic
readiness obligation `EnvWf.cons` demands — `∀ args, HasTypeV v (s.instantiate
args)` — by composing `Generalizes` with the already-delivered
`closure_typed_of_lambda_subst` (`Substitution.lean`). This sidesteps the
existential captured-context / `MStateWf`-freshness blocker entirely: the closure
is typed at the **known** evaluation context `Γ`, and `Generalizes` guarantees
each instantiation is a `Γ`-fixing substitution instance of `defnTy`.
-/

namespace Eyg.Types

open Eyg.Ir
open Eyg.Interpreter

variable {m : Type}

/-! ## The identity substitution fixes schemes and contexts -/

/-- The identity ambient substitution leaves a scheme unchanged: the quantifier
prefix shift cancels (`shift arity (var (i - arity)) = var i` for `i ≥ arity`). -/
@[simp] theorem substScheme_id (s : Scheme) :
    Scheme.substScheme (fun i => .var i) s = s := by
  unfold Scheme.substScheme
  have hfun : (fun i => if i < s.arity then (Ty.var i)
        else Ty.shift s.arity (Ty.var (i - s.arity)))
      = (fun i => (Ty.var i : Ty)) := by
    funext i
    by_cases hi : i < s.arity
    · simp [hi]
    · simp only [hi, if_false, Ty.shift, Ty.subst]
      congr 1
      omega
  rw [hfun, Ty.subst_id]

/-- The identity ambient substitution leaves a typing context unchanged. -/
@[simp] theorem substCtx_id (Γ : Ctx) : substCtx (fun i => .var i) Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨x, s⟩ := hd
      simp only [substCtx_cons, substScheme_id, ih]

/-! ## `Generalizes` — a sound generalization of `defnTy` away from `Γ` -/

/-- `Generalizes s Γ defnTy` holds when the scheme `s` is a sound generalization of
`defnTy` over the surrounding context `Γ`: **every** instantiation of `s` is a
substitution instance `subst σ defnTy` where `σ` **fixes `Γ`** (the substitution
only touches variables generalized away from the context). This is exactly the
property that makes binding `(x, s)` sound for a value of type `defnTy` whose
captured context is `Γ` — and it is satisfied trivially by the monomorphic scheme
(`generalizes_mono`) and, for inference, by `binding.gen`'s output (T8). -/
def Generalizes (s : Scheme) (Γ : Ctx) (defnTy : Ty) : Prop :=
  ∀ args, ∃ σ, s.instantiate args = Ty.subst σ defnTy ∧ substCtx σ Γ = Γ

/-- The monomorphic scheme is the trivial generalization (no variables quantified;
the witnessing substitution is the identity, which fixes everything). So the
monomorphic `let` is the `arity = 0` special case of a `let_poly`. -/
theorem generalizes_mono (Γ : Ctx) (τ : Ty) : Generalizes (Scheme.mono τ) Γ τ := by
  intro args
  refine ⟨fun i => .var i, ?_, substCtx_id Γ⟩
  rw [Scheme.instantiate_mono, Ty.subst_id]

/-- `substCtx σ` fixes a context iff it fixes every binding's scheme. -/
theorem substCtx_eq_self_iff (σ : Nat → Ty) (Γ : Ctx) :
    substCtx σ Γ = Γ ↔ ∀ b ∈ Γ, Scheme.substScheme σ b.2 = b.2 := by
  induction Γ with
  | nil => simp [substCtx]
  | cons hd tl ih =>
      obtain ⟨y, sy⟩ := hd
      simp only [substCtx_cons, List.cons.injEq, Prod.mk.injEq, true_and,
        List.mem_cons, forall_eq_or_imp, ih]

/-- **`Generalizes` survives a `TyEquiv` context-binding rewrite.** Rewriting one
binding's monomorphic type `.mono σ → .mono σ'` for `TyEquiv σ' σ` preserves
`Generalizes`, because a context-fixing substitution fixes the binding's free
variables (`Ty.fixes_free_of_subst_eq`), which `TyEquiv` preserves
(`Ty.freeVars_tyEquiv`), so it still fixes the rewritten binding
(`Ty.subst_eq_of_fixes_free`). This is the helper `hasType_ctxConv`'s `let_poly`
arm needs (the converted binding lives inside the generalization context). -/
theorem generalizes_ctxConv {s : Scheme} {Δ Γ : Ctx} {x : String} {σ σ' d : Ty}
    (hc : Ty.TyEquiv σ' σ)
    (hg : Generalizes s (Δ ++ (x, .mono σ) :: Γ) d) :
    Generalizes s (Δ ++ (x, .mono σ') :: Γ) d := by
  -- the per-binding bridge: `σg` fixing `.mono σ` ⇒ fixing `.mono σ'`
  have key : ∀ (σg : Nat → Ty), Ty.subst σg σ = σ → Ty.subst σg σ' = σ' := by
    intro σg ha
    exact Ty.subst_eq_of_fixes_free (fun i hi =>
      Ty.fixes_free_of_subst_eq ha i ((Ty.freeVars_tyEquiv hc i).mp hi))
  intro args
  obtain ⟨σg, heq, hfix⟩ := hg args
  refine ⟨σg, heq, ?_⟩
  rw [substCtx_eq_self_iff] at hfix ⊢
  intro b hb
  rcases List.mem_append.mp hb with hbΔ | hbcons
  · exact hfix b (List.mem_append.mpr (Or.inl hbΔ))
  · rcases List.mem_cons.mp hbcons with hbx | hbΓ
    · subst hbx
      have hb2 := hfix (x, Scheme.mono σ) (by simp)
      simp only [Scheme.substScheme_mono] at hb2
      have hσ : Ty.subst σg σ = σ := by
        simp only [Scheme.mono, Scheme.mk.injEq] at hb2; exact hb2.2
      simp only [Scheme.substScheme_mono]
      exact congrArg Scheme.mono (key σg hσ)
    · exact hfix b (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hbΓ)))

/-- **The polymorphic-readiness keystone for a value-restricted `let`.** If `s`
generalizes the lambda's type `defnTy` away from the evaluation context `Γ`, then
the lambda's runtime closure inhabits **every** instantiation of `s` — exactly the
`∀ args, HasTypeV v (s.instantiate args)` clause `EnvWf.cons` requires to bind the
generalized scheme. Proved by composing `Generalizes` (each instantiation is a
`Γ`-fixing instance) with `closure_typed_of_lambda_subst` (a `Γ`-fixing
substitution re-types the closure), with **no** value-substitution lemma and **no**
existential captured context. -/
theorem generalizes_closure_ready {Γ : Ctx} {x : String} {body : Tree.Node m} {a : m}
    {env : Env m} {defnTy ε : Ty} {s : Scheme}
    (hgen : Generalizes s Γ defnTy)
    (henv : EnvWf env Γ)
    (hlam : HasType Γ (⟨.Lambda x body, a⟩ : Tree.Node m) defnTy ε) :
    ∀ args, HasTypeV (Value.Closure x body env) (s.instantiate args) := by
  intro args
  obtain ⟨σ, heq, hfix⟩ := hgen args
  rw [heq]
  exact closure_typed_of_lambda_subst σ hfix henv hlam

/-! ## `Generalizes` is NOT substitution-stable — the `hasType_subst` blocker, machine-checked

The `let_poly` implementation attempt (2026-06-18) stalled because the term-level substitution
lemma `hasType_subst` (`HasType Γ e τ ε → HasType (substCtx σ Γ) e (subst σ τ) (subst σ ε)`, for an
**arbitrary** `σ`) is **false** for `let_poly`: its arm needs
`Generalizes (substScheme σ s) (substCtx σ Γ) (subst σ defnTy)` from `Generalizes s Γ defnTy`, and
that implication ("`generalizes_subst`") does not hold — `σ` can collide a generalized variable into
`FV(Γ)`, destroying the generalization. The three lemmas below **prove the counterexample in Lean**,
so the blocker is rigorous, not hand-argued. Resolution (next session): a de-Bruijn-**level**
discipline (index `Generalizes` by a level `n`, constrain `σ` below `n`) threaded through
`HasType`/`hasType_subst`/the `StackWf.assign` frame. See
`progress/2026-06-18-T6-let_poly-hasType_subst-blocker.md`. -/

/-- The witness scheme/context: `∀α. α` generalized away from a context whose only free variable is
`var 1`, at let-site type `var 0`. -/
private def cexΓ : Ctx := [("y", Scheme.mono (.var 1))]

/-- The generalization **holds** before substitution: every instance `t` of `⟨1, var 0⟩` is
`subst [0↦t] (var 0)` with `[0↦t]` fixing `cexΓ` (it touches only `var 0`, and `FV(cexΓ) = {1}`). -/
private theorem cex_pos : Generalizes ⟨1, .var 0⟩ cexΓ (.var 0) := by
  intro args
  refine ⟨fun i => if i = 0 then args.getD 0 (.var 0) else .var i, ?_, ?_⟩
  · simp [Scheme.instantiate, Ty.subst]
  · simp [cexΓ, substCtx, Scheme.substScheme_mono, Ty.subst]

/-- The generalization **fails** at let-site type `var 1` (the same scheme, but the let-site type is
now a context variable): instantiating to `var 0` would need a `σ'` with `σ' 1 = var 0` *and* (to fix
`cexΓ`) `σ' 1 = var 1`. -/
private theorem cex_neg : ¬ Generalizes ⟨1, .var 0⟩ cexΓ (.var 1) := by
  intro H
  obtain ⟨σ', heq, hfix⟩ := H [.var 0]
  -- hfix : substCtx σ' cexΓ = cexΓ  ⟹  subst σ' (var 1) = var 1
  have hsub : Ty.subst σ' (.var 1) = .var 1 := by
    have e := hfix
    unfold cexΓ substCtx at e
    simp only [List.map_cons, List.map_nil, Scheme.substScheme_mono, List.cons.injEq,
      Prod.mk.injEq, true_and, and_true] at e
    exact congrArg Scheme.body e
  have hinst : Scheme.instantiate ⟨1, .var 0⟩ [Ty.var 0] = Ty.var 0 := by
    simp [Scheme.instantiate, Ty.subst, List.getD_cons_zero]
  rw [hinst, hsub] at heq
  exact absurd heq (by decide)

/-- **`generalizes_subst` is FALSE** — the load-bearing blocker. Applying `σ = [0 ↦ var 1]` to the
`cex_pos` witness lands on the `cex_neg` failing instance (`substScheme σ ⟨1,var0⟩ = ⟨1,var0⟩`,
`substCtx σ cexΓ = cexΓ`, `subst σ (var 0) = var 1`). So no `hasType_subst` can be total over
`let_poly` with the declarative `Generalizes`; the value-restriction keystone alone does not close
the slice. -/
theorem generalizes_subst_false :
    ¬ ∀ (s : Scheme) (Γ : Ctx) (d : Ty) (σ : Nat → Ty),
        Generalizes s Γ d →
        Generalizes (Scheme.substScheme σ s) (substCtx σ Γ) (Ty.subst σ d) := by
  intro H
  have h := H ⟨1, .var 0⟩ cexΓ (.var 0) (fun i => if i = 0 then .var 1 else .var i) cex_pos
  -- normalize the substituted witness back to the `cex_neg` shape, then contradict
  have hs : Scheme.substScheme (fun i => if i = 0 then (.var 1 : Ty) else .var i) ⟨1, .var 0⟩
      = ⟨1, .var 0⟩ := by
    simp [Scheme.substScheme, Ty.subst]
  have hc : substCtx (fun i => if i = 0 then (.var 1 : Ty) else .var i) cexΓ = cexΓ := by
    simp [cexΓ, substCtx, Scheme.substScheme_mono, Ty.subst]
  have hd : Ty.subst (fun i => if i = 0 then (.var 1 : Ty) else .var i) (.var 0) = .var 1 := rfl
  rw [hs, hc, hd] at h
  exact cex_neg h

end Eyg.Types
