import Eyg.Types.Ty

/-!
# Type substitution, schemes & the builtin table (Milestone T2)

Type substitution (`Ty.subst`), polymorphic schemes (`Scheme`) with
`instantiate`, and the primitive/builtin scheme tables — transcribed from
`packages/gleam_analysis/src/eyg/analysis/inference/levels_j/contextual.gleam`
(`pure1`/`pure2`/`pure3`, `q`, `builtins()`) and `.../type_/binding.gleam`
(`instantiate`).

## Substitution is capture-free *by construction*

EYG `Ty` has **no internal binders** — every `var i` (de Bruijn) refers to one
flat scope (a `Scheme`'s quantifier prefix, or the ambient typing context).
Quantification lives only at the `Scheme` boundary. So substitution is a plain
structural `var`-replacement with **no index shifting and no capture-avoidance** —
the simplification de Bruijn-at-the-leaves buys us.

## Monomorphic first (plan T2/T6)

`instantiate` (open a scheme by substituting its quantified vars) is delivered
here; **generalization `gen` is deferred to T6**. Slices T3–T5 use monomorphic
`let` plus these polymorphic *builtin* schemes, which exercises everything except
let-polymorphism.
-/

namespace Eyg.Types

namespace Ty

/-! ## Type substitution -/

/-- Apply a type-variable substitution `σ` structurally. No shifting is needed
(`Ty` has no internal binders). -/
def subst (σ : Nat → Ty) : Ty → Ty
  | .var i => σ i
  | .fun a e r => .fun (subst σ a) (subst σ e) (subst σ r)
  | .binary => .binary
  | .integer => .integer
  | .string => .string
  | .list a => .list (subst σ a)
  | .record r => .record (subst σ r)
  | .union r => .union (subst σ r)
  | .empty => .empty
  | .rowExtend l f t => .rowExtend l (subst σ f) (subst σ t)
  | .effectExtend l a b t => .effectExtend l (subst σ a) (subst σ b) (subst σ t)
  | .never => .never
  | .promise a => .promise (subst σ a)

@[simp] theorem subst_var (σ : Nat → Ty) (i : Nat) : subst σ (.var i) = σ i := rfl

/-- Composition of substitutions (`subst` is functorial in `σ`). -/
theorem subst_subst (σ τ : Nat → Ty) (t : Ty) :
    subst σ (subst τ t) = subst (fun i => subst σ (τ i)) t := by
  induction t with
  | var i => rfl
  | _ => simp_all [subst]

/-- Identity substitution is the identity. -/
theorem subst_id (t : Ty) : subst (fun i => .var i) t = t := by
  induction t with
  | var i => rfl
  | _ => simp_all [subst]

/-- **Substitution preserves row equivalence** (plan T2: `subst` commutes with
`RowEquiv`). Labels and the `l ≠ l'` swap guards are untouched by `subst`, so
every `TyEquiv` derivation transports through it. -/
theorem subst_tyEquiv (σ : Nat → Ty) {s t : Ty} (h : TyEquiv s t) :
    TyEquiv (subst σ s) (subst σ t) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congrFun _ _ _ iha ihe ihr => exact .congrFun iha ihe ihr
  | congrList _ ih => exact .congrList ih
  | congrRecord _ ih => exact .congrRecord ih
  | congrUnion _ ih => exact .congrUnion ih
  | congrPromise _ ih => exact .congrPromise ih
  | congrRow _ _ ihf iht => exact .congrRow ihf iht
  | congrEff _ _ _ iha ihb iht => exact .congrEff iha ihb iht
  | swapRow hne => simp only [subst]; exact .swapRow hne
  | swapEff hne => simp only [subst]; exact .swapEff hne

/-! ## Schemes & instantiation -/

end Ty

/-- A polymorphic type scheme: `∀ (arity de-Bruijn vars). body`. The quantified
variables are `var 0 … var (arity-1)` occurring in `body` (`binding.Poly`). -/
structure Scheme where
  arity : Nat
  body : Ty
  deriving DecidableEq, Repr, Inhabited

namespace Scheme

/-- A monomorphic scheme (no quantifiers). -/
def mono (t : Ty) : Scheme := ⟨0, t⟩

/-- Instantiate a scheme by substituting its quantified variables with `args`
(`binding.instantiate`). Only the `arity` **quantified** variables (`var i`,
`i < arity`) are substituted with `args[i]`; any other `var` (a free variable of
the ambient context) is left untouched. So a *monomorphic* scheme ignores `args`
entirely — the property `EnvWf`'s polymorphic-readiness clause relies on. The
declarative typing rules pick `args` with `args.length = arity`. -/
def instantiate (s : Scheme) (args : List Ty) : Ty :=
  Ty.subst (fun i => if i < s.arity then args.getD i (.var i) else .var i) s.body

/-- A monomorphic scheme instantiates to its body, ignoring `args`. -/
@[simp] theorem instantiate_mono (t : Ty) (args : List Ty) :
    (mono t).instantiate args = t := by
  unfold instantiate mono
  simp only [Nat.not_lt_zero, if_false]
  exact Ty.subst_id t

end Scheme

/-! ## Scheme builders (`contextual.q`/`pure1`/`pure2`/`pure3`) -/

namespace Ty

/-- Quantified type variable `i` (`contextual.q`). -/
abbrev q (i : Nat) : Ty := .var i

/-- A pure unary arrow `arg →⟨∅⟩ ret` (`contextual.pure1`). -/
def pure1 (arg ret : Ty) : Ty := .fun arg .empty ret

/-- A pure binary arrow (`contextual.pure2`). -/
def pure2 (a b ret : Ty) : Ty := .fun a .empty (.fun b .empty ret)

/-- A pure ternary arrow (`contextual.pure3`). -/
def pure3 (a b c ret : Ty) : Ty := .fun a .empty (.fun b .empty (.fun c .empty ret))

end Ty

/-! ## Builtin scheme table (`contextual.builtins()`)

Transcribed from `builtins()`. The arity is the count of distinct `q`-vars: the
`int_*`/`string_*` arithmetic and string builtins are monomorphic (arity 0);
`equal` is `∀α. α → α → bool` (arity 1); `fix` is `∀α β. (α →⟨β⟩ α) →⟨β⟩ α`
(arity 2). Grown per slice; completed in T6. -/

namespace Builtins

open Eyg.Types.Ty

/-- `int_compare`'s return: `Union(|Lt :: unit, Eq :: unit, Gt :: unit|)`. -/
def intCompareResult : Ty := union' [("Lt", unit), ("Eq", unit), ("Gt", unit)]

/-- The (partial) builtin scheme table — the T2 arithmetic/string/core subset of
`contextual.builtins()`. Returns `none` for builtins not yet transcribed. -/
def scheme : String → Option Scheme
  | "equal" => some ⟨1, pure2 (q 0) (q 0) boolean⟩
  | "fix" => some ⟨2, .fun (.fun (q 0) (q 1) (q 0)) (q 1) (q 0)⟩
  | "int_compare" => some (.mono (pure2 integer integer intCompareResult))
  | "int_add" => some (.mono (pure2 integer integer integer))
  | "int_subtract" => some (.mono (pure2 integer integer integer))
  | "int_multiply" => some (.mono (pure2 integer integer integer))
  | "int_divide" => some (.mono (pure2 integer integer (result integer unit)))
  | "int_absolute" => some (.mono (pure1 integer integer))
  | "int_parse" => some (.mono (pure1 string (result integer unit)))
  | "int_to_string" => some (.mono (pure1 integer string))
  | "string_append" => some (.mono (pure2 string string string))
  | "string_length" => some (.mono (pure1 string integer))
  | "string_uppercase" => some (.mono (pure1 string string))
  | "string_lowercase" => some (.mono (pure1 string string))
  | "string_starts_with" => some (.mono (pure2 string string boolean))
  | "string_ends_with" => some (.mono (pure2 string string boolean))
  | _ => none

/-! ## Sanity checks -/

-- `int_add : Integer → Integer → Integer`, monomorphic.
example : scheme "int_add" = some (.mono (.fun .integer .empty (.fun .integer .empty .integer))) :=
  rfl

-- Instantiating `equal` at `Integer` gives `Integer → Integer → boolean`.
example : (Scheme.instantiate ⟨1, Ty.pure2 (Ty.q 0) (Ty.q 0) Ty.boolean⟩ [Ty.integer])
    = Ty.pure2 Ty.integer Ty.integer Ty.boolean := rfl

-- `fix` instantiated at `α := Integer, β := ∅`: `(Integer →⟨∅⟩ Integer) →⟨∅⟩ Integer`.
example : (Scheme.instantiate ⟨2, .fun (.fun (Ty.q 0) (Ty.q 1) (Ty.q 0)) (Ty.q 1) (Ty.q 0)⟩
    [Ty.integer, Ty.empty])
    = .fun (.fun Ty.integer Ty.empty Ty.integer) Ty.empty Ty.integer := rfl

end Builtins

end Eyg.Types
