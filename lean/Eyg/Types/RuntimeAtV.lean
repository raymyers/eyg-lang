import Eyg.Types.TypingAtV
import Eyg.Interpreter.State

/-!
# Level-native value typing `HasTypeVAt` / `EnvWfAt` (G1 Phase 3b — obstruction (B), the value side)

This is the **value-typing sibling** of `HasTypeAtV`/`hasTypeAtV_substAt`/`genAtV_instantiate_lam_ready`
(`TypingAtV.lean`), closing the last gap in the Caveat-5 (nested let-polymorphism) soundness argument.

## The gap this closes

`Runtime.lean`'s `HasTypeV.closure` requires a **magnitude** `HasType` derivation of the closure's
lambda body, and — because `HasType.let_poly` carries a `noLambdaLet` restriction — no such magnitude
derivation exists once the body itself contains generalization nested ≥ 2 deep (the exact Caveat-5
shape). So even with the term-level re-typing machinery of `TypingAtV.lean` in hand, there was no way
to reach an actual `HasTypeV (Value.Closure …)` judgment: `HasTypeV.closure` demands the wrong premise.

`HasTypeVAt` mirrors `HasTypeV` but its `closure` constructor consumes a **level-native**
`HasTypeAtV lvl Γ ⟨.Lambda x body, a⟩ τ ε` derivation (`TypingAtV.lean`) — which *does* exist for
arbitrarily nested generalization (no `noLambdaLet`). `EnvWfAt` mirrors `EnvWf` with its readiness
obligation stated over `HasTypeVAt`/`instantiateV` instead of `HasTypeV`/magnitude `instantiate`.

The value-level keystone `genAtV_closure_ready_value` then composes `genAtV_instantiate_lam_ready`
(term level) with `HasTypeVAt.closure` to discharge exactly what `EnvWfAt.cons` needs: a let-bound
lambda's runtime closure inhabits **every** instantiation of its generalized scheme `genAtV ℓ defnTy`.
The nested demonstration reuses `hInnerV`/`hOuterV_instantiate` and produces a genuine
`Value.Closure` typed at `Integer → Integer`, completing the whole chain
`term derivation → closure value → typed-at-every-instantiation` for the doubly-nested case the
original `HasType`/`HasTypeV`/`generalizes_closure_ready` chain reaches only vacuously.

## Scope

Purely additive. `HasTypeV`, `EnvWf`, `HasType`, and every soundness declaration are untouched.
Only the value shapes with actual generalization content are mirrored here (the base literals, to
realize ground-typed environments, and the crux `closure`). The runtime-continuation / partial value
shapes (`partialBuiltin`, `partialResume`, and the data/partial constructors) carry **zero**
generalization content — each is a mechanical `HasTypeV → HasTypeVAt lvl` transliteration threading
`Ty.TyEquiv` unchanged — and are deliberately out of scope for this deliverable (they belong to the
Phase-5 `Machine`/`Runtime` re-green, not the Caveat-5 mathematics).

## The instantiation-arguments side-condition

`EnvWfAt.cons`'s readiness (and the keystone) carries the natural well-formedness bound
`∀ t ∈ args, ∀ l ∈ t.levels, l ≤ s.level`: a level-`ℓ` scheme is instantiated with types whose levels
do not exceed `ℓ` (types mentioning *deeper* generalization levels do not exist at the point the
scheme is opened). This is exactly `hasTypeAtV_substAt`'s `hσ` bound, threaded to the value side. It is
discharged trivially for ground instantiation arguments (the demonstration instantiates at `integer`,
whose `levels` are `[]`).
-/

namespace Eyg.Types

open Eyg.Interpreter
open Eyg.Ir

variable {m : Type}

/-! ## The level-native value / environment judgment -/

mutual

/-- **Level-native value typing.** The sibling of `HasTypeV` whose `closure` constructor consumes a
level-native `HasTypeAtV` lambda derivation (existing for arbitrarily nested generalization) instead of
the `noLambdaLet`-restricted magnitude `HasType` body derivation `HasTypeV.closure` demands. The base
literals thread `Ty.TyEquiv` exactly as in `HasTypeV` (the `lvl` index is irrelevant to them). -/
inductive HasTypeVAt {m : Type} : Nat → Value m → Ty → Prop where
  | int {lvl n τ} : Ty.TyEquiv .integer τ → HasTypeVAt lvl (.Integer n) τ
  | str {lvl s τ} : Ty.TyEquiv .string τ → HasTypeVAt lvl (.String s) τ
  | bin {lvl b τ} : Ty.TyEquiv .binary τ → HasTypeVAt lvl (.Binary b) τ
  /-- A closure inhabits (a type equivalent to) an arrow, provided its captured env realizes a context
  under which the **lambda** type-checks *level-natively* (`HasTypeAtV`), at the closure's level `lvl`.
  This is the constructor that differs from `HasTypeV.closure`: the premise is the level-native lambda
  derivation, which exists for nested-generalized bodies the magnitude judgment cannot express. -/
  | closure {lvl x body env Γ τ τ' ε a} :
      EnvWfAt env Γ →
      HasTypeAtV lvl Γ ⟨.Lambda x body, a⟩ τ ε →
      Ty.TyEquiv τ τ' →
      HasTypeVAt lvl (.Closure x body env) τ'

/-- **Level-native environment well-formedness.** The sibling of `EnvWf`: the value bound to a scheme
must inhabit *every* (well-formed) instantiation of it, stated over the level-native `instantiateV` at
the scheme's own generalization level `s.level`. The `args`-level side-condition
`∀ t ∈ args, ∀ l ∈ t.levels, l ≤ s.level` is `hasTypeAtV_substAt`'s `hσ` bound on the value side. -/
inductive EnvWfAt {m : Type} : Env m → Ctx → Prop where
  | nil : EnvWfAt [] []
  | cons {y v s env Γ} :
      (∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l ≤ s.level) →
        HasTypeVAt s.level v (s.instantiateV args)) →
      EnvWfAt env Γ →
      EnvWfAt ((y, v) :: env) ((y, s) :: Γ)

end

/-- **Value conversion** (derived): a value's type may be replaced by a `TyEquiv`-equal one, mirroring
`HasTypeV.conv`. -/
theorem HasTypeVAt.conv {lvl : Nat} {v : Value m} {τ τ' : Ty}
    (h : HasTypeVAt lvl v τ) (heq : Ty.TyEquiv τ τ') : HasTypeVAt lvl v τ' := by
  cases h with
  | int he => exact .int (he.trans heq)
  | str he => exact .str (he.trans heq)
  | bin he => exact .bin (he.trans heq)
  | closure henv hlam he => exact .closure henv hlam (he.trans heq)

/-! ## The value-level readiness keystone (level-native `generalizes_closure_ready`) -/

/-- **The polymorphic-readiness keystone for a value-restricted `let`, level-native.** For a let-bound
lambda presented via its `lam` components at ambient level `ℓ` — body at a strictly higher level `lvl'`,
ambient context `Γ` below `ℓ` (`CtxWfV ℓ Γ`, so `substAt ℓ` fixes it), polymorphic bindings above `ℓ`
(`PolyAbove ℓ Γ`) — whose runtime environment realizes `Γ` level-natively (`EnvWfAt env Γ`), the
lambda's runtime closure `Value.Closure x lbody env` inhabits **every** (well-formed) instantiation of
its generalized scheme `genAtV ℓ (.fun argTy εb retTy)`.

This is the exact obligation `EnvWfAt.cons` requires to bind the generalized scheme (`s.level = ℓ`,
`s = genAtV ℓ defnTy`), and the level-native analog of `generalizes_closure_ready`. It composes
`genAtV_instantiate_lam_ready` (each instantiation is a genuine `substAt ℓ` re-typing of the lambda's
own `HasTypeAtV` derivation) with `HasTypeVAt.closure`. Crucially it carries **no `noLambdaLet`**: the
lambda body `lbody` may itself bind a polymorphically-used lambda-`let` (the Caveat-5 shape), which is
precisely what the magnitude `generalizes_closure_ready` cannot reach. -/
theorem genAtV_closure_ready_value {ℓ : Nat} (hℓ : ℓ ≠ 0)
    {lvl' : Nat} {Γ : Ctx} {x : String} {lbody : Tree.Node m} {la : m}
    {argTy εb retTy : Ty}
    (hlt : ℓ < lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hbody : HasTypeAtV lvl' ((x, .mono argTy) :: Γ) lbody retTy εb)
    (hΓpa : PolyAbove ℓ Γ)
    (hΓwf : CtxWfV ℓ Γ)
    {env : Env m} (henv : EnvWfAt env Γ) :
    ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l ≤ ℓ) →
      HasTypeVAt ℓ (Value.Closure x lbody env)
        ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) := by
  intro args hargs
  have hlam := genAtV_instantiate_lam_ready (m := m) (la := la) (ε := .empty)
    hℓ hlt hfv hbody hΓpa hΓwf args hargs
  exact HasTypeVAt.closure henv hlam (Ty.TyEquiv.refl _)

/-! ## The nested demonstration: the whole chain, term derivation → closure value → typed at integer

Reusing `hInnerV`/`hOuterV_instantiate` (`TypingAtV.lean`), we build the *actual runtime closure* for
the outer lambda `\x. (let inner = \y.y in inner x)` and show it is `HasTypeVAt`-typed at a concrete
instantiation `Integer → Integer` via the value keystone — a genuine `Value.Closure` inhabiting the
opened scheme, for the doubly-nested case `HasType`/`HasTypeV`/`generalizes_closure_ready` cannot
express. This closes both the term-typing and value-typing sides of nested let-polymorphism, all the
way down to a concrete runtime closure. -/

section NestedValueExample
open Eyg.Ir.Tree

/-- The outer lambda's stored closure body (the `let inner = \y.y in inner x` node). -/
private def outerBody : Tree.Node Unit :=
  let_ "inner" (lambda "y" (variable_ "y")) (apply (variable_ "inner") (variable_ "x"))

/-- **The closure is ready at every (well-formed) instantiation of the outer scheme.** Applying the
value keystone to the outer lambda (body = `hInnerV` at the strictly higher level `2`) over the empty
environment yields: the runtime closure `Value.Closure "x" outerBody []` inhabits **every**
instantiation of `genAtV 1 (α → α)` — the `EnvWfAt.cons` obligation, discharged non-vacuously for a
term binding a `Lambda` in a nested `let`. -/
theorem hOuterVClosure_ready :
    ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l ≤ 1) →
      HasTypeVAt (m := Unit) 1 (Value.Closure "x" outerBody [])
        ((Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0))).instantiateV args) :=
  genAtV_closure_ready_value (ℓ := 1) (by omega) (lvl' := 2) (la := ()) (by omega)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hInnerV
    (by intro b hb; simp at hb)
    (by intro b hb; simp at hb)
    EnvWfAt.nil

/-- **The genuine runtime closure, typed at `Integer → Integer`.** Instantiating the ready closure at
`[integer]` (whose levels are `[]`, so the side-condition is trivial) and reducing
`(genAtV 1 (α → α)).instantiateV [integer] = integer → integer` (by `rfl`) gives an actual
`Value.Closure` inhabiting `Integer → Integer`. The outer type variable `α` (level `1`) is genuinely
replaced by `integer`; the **nested inner** scheme (level `2` ≠ `1`) was correctly re-generalized during
the re-typing. This is the value-side "wall falls" check — the complete chain closes non-vacuously. -/
theorem hOuterVClosure_typed_integer_arrow :
    HasTypeVAt (m := Unit) 1 (Value.Closure "x" outerBody [])
      (.fun .integer .empty .integer) := by
  have h := hOuterVClosure_ready [.integer]
    (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; intro l hl;
        simp only [Ty.levels] at hl; exact absurd hl (by simp))
  have heq : (Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0))).instantiateV [.integer]
      = (.fun .integer .empty .integer : Ty) := rfl
  rwa [heq] at h

/-- **The full chain, stated directly.** The outer lambda's runtime closure over the empty env
inhabits `Integer → Integer` — starting from the plain closure constructor fed the keystone's
instantiated lambda derivation (`hOuterV_instantiate`), an alternative route to the same conclusion
that makes the `term derivation → closure value` step fully explicit. -/
theorem hOuterVClosure_via_constructor :
    HasTypeVAt (m := Unit) 1 (Value.Closure "x" outerBody [])
      (.fun .integer .empty .integer) := by
  have hlam := hOuterV_instantiate
  have heq : (Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0))).instantiateV [.integer]
      = (.fun .integer .empty .integer : Ty) := rfl
  rw [heq] at hlam
  exact HasTypeVAt.closure EnvWfAt.nil hlam (Ty.TyEquiv.refl _)

end NestedValueExample

end Eyg.Types
