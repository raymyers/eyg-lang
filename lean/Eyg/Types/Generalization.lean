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
    Scheme.substScheme (fun i => .var 0 i) s = s := by
  unfold Scheme.substScheme
  have hfun : (fun i => if i < s.arity then (Ty.var 0 i)
        else Ty.shift s.arity (Ty.var 0 (i - s.arity)))
      = (fun i => (Ty.var 0 i : Ty)) := by
    funext i
    by_cases hi : i < s.arity
    · simp [hi]
    · simp only [hi, if_false, Ty.shift, Ty.subst]
      congr 1
      omega
  rw [hfun, Ty.subst_id]

/-- The identity ambient substitution leaves a typing context unchanged. -/
@[simp] theorem substCtx_id (Γ : Ctx) : substCtx (fun i => .var 0 i) Γ = Γ := by
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
  refine ⟨fun i => .var 0 i, ?_, substCtx_id Γ⟩
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
        simp only [Scheme.mono, Scheme.mk.injEq] at hb2; exact hb2.2.2
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
    (hnl : Tree.Node.noLambdaLet body)
    (henv : EnvWf env Γ)
    (hlam : HasType Γ (⟨.Lambda x body, a⟩ : Tree.Node m) defnTy ε) :
    ∀ args, HasTypeV (Value.Closure x body env) (s.instantiate args) := by
  intro args
  obtain ⟨σ, heq, hfix⟩ := hgen args
  rw [heq]
  exact closure_typed_of_lambda_subst σ hfix hnl henv hlam

/-! ## Level-indexed generalization `GeneralizesAt` (the substitution-stable redesign, T6 gen)

Since `generalizes_subst_false` (below) proves the bare `Generalizes` is not substitution-stable, the
resolution is a de-Bruijn-**level** discipline: generalize only variables `≥ n` (the fresh boundary
above the in-scope ambient `[0,n)`), with the witnessing `σ'` required to **fix `[0,n)`**. The full
redesign threads `n` through the judgment (`progress/2026-06-18-T6-let_poly-level-redesign-design.md`);
this is its declarative core plus the bridge that lets it slot into the existing keystone. The
substitution-stability theorem `generalizesAt_subst` (the involved scheme-algebra over arbitrary
instantiation args) is the remaining piece for the dedicated session. -/

/-- `GeneralizesAt n s d`: every instantiation of `s` is a `subst σ' d` whose witnessing `σ'` **fixes
the ambient region `[0,n)`** — so `σ'` only moves the *generalized* variables, which live at indices
`≥ n`. Strengthens `Generalizes` along the freshness axis it was missing. -/
def GeneralizesAt (n : Nat) (s : Scheme) (d : Ty) : Prop :=
  ∀ args, ∃ σ', s.instantiate args = Ty.subst σ' d ∧ ∀ i, i < n → σ' i = .var 0 i

/-- **Bridge: `GeneralizesAt n` implies the keystone's `Generalizes`** when the context `Γ` is below
level `n` (any `[0,n)`-fixing substitution fixes it). So the level-indexed predicate slots directly
into `generalizes_closure_ready` — the keystone is unchanged; only the freshness premise sharpens. -/
theorem generalizesAt_to_generalizes {n : Nat} {s : Scheme} {Γ : Ctx} {d : Ty}
    (hΓ : ∀ σ' : Nat → Ty, (∀ i, i < n → σ' i = .var 0 i) → substCtx σ' Γ = Γ)
    (hg : GeneralizesAt n s d) : Generalizes s Γ d := by
  intro args
  obtain ⟨σ', heq, hfix⟩ := hg args
  exact ⟨σ', heq, hΓ σ' hfix⟩

/-- The monomorphic scheme generalizes at **any** level (no variables are generalized, so the
identity `σ'` — which fixes `[0,n)` — witnesses every instantiation). The `arity = 0` base case. -/
theorem generalizesAt_mono (n : Nat) (τ : Ty) : GeneralizesAt n (Scheme.mono τ) τ := by
  intro args
  exact ⟨fun i => .var 0 i, by rw [Scheme.instantiate_mono, Ty.subst_id], fun i _ => rfl⟩

/-! ## Constructive generalization `genAt` — the substitution-stable witness (T6 gen, design fork)

`generalizesAt_subst` (the substitution-stability of `GeneralizesAt`) **resisted a direct proof for
an arbitrary scheme `s`**: the declarative `∃σ'` form gives no structural handle relating the
substituted scheme's arbitrary instantiations back to `subst σ d` (see the level-redesign note). The
fork's resolution: pin the `let_poly` rule's scheme to a **computed** generalization `genAt n d`, so
the scheme body is *structurally* `subst (reindexGen …) d` and substitution-stability becomes a
`subst`/`shift` **commutation** (`genAt_substScheme` below), not an existential chase.

`genAt n d` re-indexes `d` into a scheme at level `n`: the generalized variables (`≥ n`) become the
quantifier prefix `0 … arity-1` (via `v ↦ v - n`), and the ambient variables (`< n`) shift up past the
prefix (`v ↦ v + arity`) so instantiation shifts them back down. -/

namespace Ty

/-- An element of a `Nat` list is `≤` its `foldr max 0`. -/
theorem mem_le_foldr_max {x : Nat} {l : List Nat} (h : x ∈ l) :
    x ≤ l.foldr Nat.max 0 := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with h | h
      · subst h; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- `foldr max 0` is `≤ B` when every element is (`0 ≤ B` covers the empty list). -/
theorem foldr_max_le {l : List Nat} {B : Nat} (h : ∀ x ∈ l, x ≤ B) :
    l.foldr Nat.max 0 ≤ B := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a t ih =>
      simp only [List.foldr_cons]
      exact Nat.max_le.mpr ⟨h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

/-- A **level map** at level `n`: the identity on the fresh region `[n,∞)`, and maps each ambient
variable `< n` to a type whose free variables stay `< n`. This is exactly the class of substitutions
`hasType_subst` threads (the ambient-into-ambient condition pinned in the level-redesign note) — it
keeps the generalized region untouched, so generalization is stable under it. -/
def LevelMap (n : Nat) (σ : Nat → Ty) : Prop :=
  (∀ i, n ≤ i → σ i = .var 0 i) ∧ (∀ i, i < n → ∀ w ∈ (σ i).freeVars, w < n)

/-- **A level map is a level map at every higher level.** A `LevelMap n` fixes `[n,∞)` and keeps
`[0,n)` within `[0,n)`; raising the level to `n' ≥ n` still fixes `[n',∞)` (⊆ `[n,∞)`) and keeps
`[0,n')` within `[0,n')` — an ambient `i < n` lands in `[0,n) ⊆ [0,n')`, and a fixed `n ≤ i < n'`
maps to `var i` whose only free var is `i < n'`. **The glue for `hasType_subst`'s descent into a
nested `let_poly`:** the outer-scope `σ` (a `LevelMap n` for the outer level `n`) is automatically a
`LevelMap n'` for every deeper let's level `n' ≥ n`, so a *single* substitution serves all nested
generalizations without re-levelling. -/
theorem LevelMap.mono {n n' : Nat} {σ : Nat → Ty} (hσ : Ty.LevelMap n σ) (hle : n ≤ n') :
    Ty.LevelMap n' σ := by
  obtain ⟨hfix, hamb⟩ := hσ
  refine ⟨fun i hi => hfix i (Nat.le_trans hle hi), fun i hi w hw => ?_⟩
  by_cases hin : i < n
  · exact Nat.lt_of_lt_of_le (hamb i hin w hw) hle
  · rw [hfix i (Nat.le_of_not_lt hin)] at hw
    simp only [Ty.freeVars, List.mem_singleton] at hw
    omega

/-- On a type whose free variables all sit below `n`, the re-indexing `reindexGen n k` acts as a plain
`shift` by `k` (every such var is in the ambient `< n` branch `w ↦ var (w + k)`). The hinge of the
ambient case of `genAt_substScheme`. -/
theorem shift_eq_reindexGen {n k : Nat} {t : Ty} (ht : ∀ w ∈ t.freeVars, w < n) :
    Ty.shift k t = Ty.subst (Ty.reindexGen n k) t := by
  rw [Ty.shift]
  apply Ty.subst_congr_free
  intro w hw
  simp only [Ty.reindexGen, if_pos (ht w hw)]

/-- **A generalized variable fits in the quantifier prefix.** Every `v ≥ n` free in `d` satisfies
`v - n < genArity n d` — so `reindexGen` maps it to a quantifier that `instantiate` can fill. -/
theorem genArity_spec {n v : Nat} {d : Ty} (hv : v ∈ d.freeVars) (hn : n ≤ v) :
    v - n < d.genArity n := by
  have : v + 1 - n ≤ d.genArity n :=
    mem_le_foldr_max (List.mem_map.mpr ⟨v, hv, rfl⟩)
  omega

end Ty

/-- Componentwise scheme equality (the `body` field is non-dependent). -/
theorem Scheme.ext' {s t : Scheme} (ha : s.arity = t.arity) (hc : s.level = t.level)
    (hb : s.body = t.body) : s = t := by
  cases s; cases t; cases ha; cases hc; cases hb; rfl

/-- **`genAt` is a sound generalization** — every instantiation of `genAt n d` is a `subst`-instance
of `d` whose witnessing substitution fixes the ambient region `[0,n)`. (The witness fixes `[0,n)`
*regardless* of the arity: an ambient var `i < n` is reindexed to `i + arity ≥ arity`, which
`instantiate` shifts straight back to `var i`.) -/
theorem genAt_generalizesAt (n : Nat) (d : Ty) : GeneralizesAt n (Scheme.genAt n d) d := by
  intro args
  refine ⟨fun v => Ty.subst
      (fun j => if j < d.genArity n then args.getD j (.var 0 j) else .var 0 (j - d.genArity n))
      (Ty.reindexGen n (d.genArity n) v), ?_, ?_⟩
  · -- instantiate = subst (compose) d, definitionally (subst_subst)
    simp only [Scheme.instantiate, Scheme.genAt, Ty.subst_subst]
  · -- the witness fixes [0,n): an ambient var i < n round-trips to var i
    intro i hi
    simp only [Ty.reindexGen, if_pos hi, Ty.subst]
    rw [if_neg (by omega)]
    congr 1; omega

/-- **The computed `genAt` feeds the existing keystone.** For a context below level `n`, the computed
generalization satisfies the declarative `Generalizes` that `generalizes_closure_ready` consumes — so
the `let_poly` rule can store `genAt n defnTy` and discharge the `EnvWf.cons` readiness clause through
the unchanged keystone. The rule-facing connective for the threading session. -/
theorem genAt_generalizes {n : Nat} {Γ : Ctx} {d : Ty}
    (hΓ : ∀ σ' : Nat → Ty, (∀ i, i < n → σ' i = .var 0 i) → substCtx σ' Γ = Γ) :
    Generalizes (Scheme.genAt n d) Γ d :=
  generalizesAt_to_generalizes hΓ (genAt_generalizesAt n d)

/-- **Push-time polymorphic readiness for a `genAt`-generalized `let`.** Combines the rule-facing
bridge `genAt_generalizes` with the keystone `generalizes_closure_ready`: a let-bound lambda's runtime
closure inhabits **every** instantiation of its computed scheme `genAt n defnTy` (for a context below
level `n`). This is the closed readiness `Rdy` the `Assign`-push computes once, at the one coherent
point, and carries across the lambda→closure step (the coupling design's `StackWfV`). -/
theorem genAt_closure_ready {n : Nat} {Γ : Ctx} {x : String} {body : Tree.Node m} {a : m}
    {env : Env m} {defnTy ε : Ty}
    (hΓ : ∀ σ' : Nat → Ty, (∀ i, i < n → σ' i = .var 0 i) → substCtx σ' Γ = Γ)
    (hnl : Tree.Node.noLambdaLet body)
    (henv : EnvWf env Γ)
    (hlam : HasType Γ (⟨.Lambda x body, a⟩ : Tree.Node m) defnTy ε) :
    ∀ args, HasTypeV (Value.Closure x body env) ((Scheme.genAt n defnTy).instantiate args) :=
  generalizes_closure_ready (genAt_generalizes hΓ) hnl henv hlam

/-- **Generalization arity is stable under a level map.** A level map fixes the generalized region
`[n,∞)` and keeps the ambient region within `[0,n)` (weight `0`), so the weighted max defining the
arity is unchanged. The arity-equality half of the commutation `genAt_substScheme`. -/
theorem genArity_subst {n : Nat} {σ : Nat → Ty} (hσ : Ty.LevelMap n σ) (d : Ty) :
    (Ty.subst σ d).genArity n = d.genArity n := by
  obtain ⟨hfix, hamb⟩ := hσ
  apply Nat.le_antisymm
  · -- every weight of `subst σ d` is ≤ genArity d
    apply Ty.foldr_max_le
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [Ty.mem_freeVars_subst] at hw
    obtain ⟨v, hv, hwv⟩ := hw
    by_cases hvn : n ≤ v
    · -- v ≥ n: σ v = var v, so w = v
      rw [hfix v hvn, Ty.freeVars, List.mem_singleton] at hwv; subst hwv
      exact Ty.mem_le_foldr_max (List.mem_map.mpr ⟨w, hv, rfl⟩)
    · -- v < n: w < n, so weight = 0
      have := hamb v (Nat.lt_of_not_le hvn) w hwv
      omega
  · -- every weight of `d` is ≤ genArity (subst σ d)
    apply Ty.foldr_max_le
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    by_cases hvn : n ≤ v
    · -- v ≥ n: σ v = var v, so v ∈ FV(subst σ d)
      have hmem : v ∈ (Ty.subst σ d).freeVars :=
        Ty.mem_freeVars_subst.mpr
          ⟨v, hv, by rw [hfix v hvn, Ty.freeVars]; exact List.mem_singleton.mpr rfl⟩
      exact Ty.mem_le_foldr_max (List.mem_map.mpr ⟨v, hmem, rfl⟩)
    · -- v < n: weight = 0
      omega

/-- **`genAt` commutes with a level-map substitution** — the substitution-stability core. Pushing a
level map `σ` through the computed generalization equals generalizing the substituted type. This is
what makes `GeneralizesAt` substitution-stable once the `let_poly` rule pins its scheme to `genAt`
(the route `generalizes_subst_false` forces): the arms of `hasType_subst` match structurally instead
of chasing the unrecoverable existential witness. -/
theorem genAt_substScheme {n : Nat} {σ : Nat → Ty} (hσ : Ty.LevelMap n σ) (d : Ty) :
    Scheme.substScheme σ (Scheme.genAt n d) = Scheme.genAt n (Ty.subst σ d) := by
  have harity := genArity_subst hσ d
  obtain ⟨hfix, hamb⟩ := hσ
  -- both schemes have arity `d.genArity n`; equate componentwise
  refine Scheme.ext' ?_ rfl ?_
  · simp only [Scheme.substScheme_arity, Scheme.genAt_arity]; exact harity.symm
  -- body equality, via subst_subst on both sides + agreement on FV(d)
  simp only [Scheme.substScheme, Scheme.genAt, harity, Ty.subst_subst]
  apply Ty.subst_congr_free
  intro v hv
  by_cases hvn : n ≤ v
  · -- generalized var: reindexed to quantifier v - n (< arity), σ fixes it (σ v = var v)
    have hlt : v - n < d.genArity n := Ty.genArity_spec hv hvn
    have hvn' : ¬ v < n := by omega
    rw [hfix v hvn]
    simp only [Ty.reindexGen, if_neg hvn', Ty.subst_var, if_pos hlt]
  · -- ambient var: reindexed to v + arity (≥ arity); LHS shifts σ v, reindexGen acts as shift on it
    push_neg at hvn
    have hvk : ¬ v + d.genArity n < d.genArity n := by omega
    rw [show Ty.reindexGen n (d.genArity n) v = Ty.var 0 (v + d.genArity n) from by
      rw [Ty.reindexGen, if_pos hvn]]
    simp only [Ty.subst_var, if_neg hvk, Nat.add_sub_cancel]
    exact Ty.shift_eq_reindexGen (fun w hw => hamb v hvn w hw)

/-- **`GeneralizesAt` is substitution-stable for the computed witness** — substituting a level map
through `genAt n d` still generalizes `subst σ d` at level `n`. The `hasType_subst` `let_poly` arm
needs exactly this (with the rule's scheme pinned to `genAt`). Resolves the obstruction
`generalizes_subst_false` machine-checks for the declarative predicate. -/
theorem generalizesAt_subst {n : Nat} {σ : Nat → Ty} (hσ : Ty.LevelMap n σ) (d : Ty) :
    GeneralizesAt n (Scheme.substScheme σ (Scheme.genAt n d)) (Ty.subst σ d) := by
  rw [genAt_substScheme hσ]
  exact genAt_generalizesAt n (Ty.subst σ d)

/-! ## Scheme/context free-variable metatheory + `CtxWf` (the `hasType_subst` `let_poly` threading)

The level-redesign's `WfBelow n` route threads a **context-below-level-`n`** side-invariant `CtxWf n Γ`
through `hasType_subst` (NOT through the preservation engines — see
`progress/2026-06-18-T6-let_poly-levelmap-mono-and-wfbelow-decision.md`). The `let_poly` arm of
`hasType_subst` must (a) re-establish `CtxWf n (substCtx σ Γ)` from `CtxWf n Γ` + `LevelMap n σ`, and
(b) bridge `CtxWf n Γ` to the keystone's context-fixing premise `∀σ' fixing [0,n), substCtx σ' Γ = Γ`.
Both need a notion of a scheme's **ambient** free variables (those occurring above the quantifier
prefix), developed here. -/

namespace Ty

/-- The free variables of a `shift k t` are exactly those of `t` shifted up by `k`. -/
theorem mem_freeVars_shift {k i : Nat} {t : Ty} :
    i ∈ (Ty.shift k t).freeVars ↔ ∃ w ∈ t.freeVars, i = w + k := by
  rw [Ty.shift, Ty.mem_freeVars_subst]
  constructor
  · rintro ⟨v, hv, hi⟩
    rw [Ty.freeVars, List.mem_singleton] at hi
    exact ⟨v, hv, hi⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by rw [Ty.freeVars]; exact List.mem_singleton.mpr rfl⟩

end Ty

/-- Membership in a scheme's ambient free variables: `m` is ambient-free iff `m + arity` is a body
free variable. -/
theorem Scheme.mem_freeVars {s : Scheme} {m : Nat} :
    m ∈ s.freeVars ↔ (m + s.arity) ∈ s.body.freeVars := by
  simp only [Scheme.freeVars, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨j, ⟨hj, hle⟩, rfl⟩
    rwa [Nat.sub_add_cancel hle]
  · intro h
    exact ⟨m + s.arity, ⟨h, by omega⟩, by omega⟩

/-- **A substitution fixing a scheme's ambient free vars fixes the scheme.** (The quantifier prefix is
untouched by `substScheme`; each ambient occurrence `i ≥ arity` maps to `shift arity (σ (i-arity))`,
which collapses to `var i` exactly when `σ` fixes `i - arity`.) -/
theorem Scheme.substScheme_eq_of_fixes_free {σ : Nat → Ty} {s : Scheme}
    (h : ∀ i ∈ s.freeVars, σ i = .var 0 i) : Scheme.substScheme σ s = s := by
  rw [Scheme.substScheme]
  refine Scheme.ext' rfl rfl ?_
  apply Ty.subst_eq_of_fixes_free
  intro j hj
  by_cases hja : j < s.arity
  · simp only [if_pos hja]
  · have hle : s.arity ≤ j := Nat.le_of_not_lt hja
    have hmem : (j - s.arity) ∈ s.freeVars :=
      Scheme.mem_freeVars.mpr (by rwa [Nat.sub_add_cancel hle])
    simp only [if_neg hja, h _ hmem, Ty.shift, Ty.subst_var, Nat.sub_add_cancel hle]

/-- The ambient free vars of `substScheme σ s` come from substituting `σ` into the ambient free vars of
`s`: `m` is ambient-free in `substScheme σ s` iff `m ∈ FV(σ p)` for some ambient-free `p` of `s`. -/
theorem Scheme.mem_freeVars_substScheme {σ : Nat → Ty} {s : Scheme} {m : Nat} :
    m ∈ (Scheme.substScheme σ s).freeVars ↔ ∃ p ∈ s.freeVars, m ∈ (σ p).freeVars := by
  rw [Scheme.mem_freeVars]
  simp only [Scheme.substScheme, Ty.mem_freeVars_subst]
  constructor
  · rintro ⟨j, hj, hmem⟩
    by_cases hja : j < s.arity
    · rw [if_pos hja, Ty.freeVars, List.mem_singleton] at hmem; omega
    · have hle : s.arity ≤ j := Nat.le_of_not_lt hja
      rw [if_neg hja, Ty.mem_freeVars_shift] at hmem
      obtain ⟨w, hw, hmw⟩ := hmem
      refine ⟨j - s.arity, Scheme.mem_freeVars.mpr (by rwa [Nat.sub_add_cancel hle]), ?_⟩
      have : m = w := by omega
      rwa [this]
  · rintro ⟨p, hp, hmem⟩
    have hbody : (p + s.arity) ∈ s.body.freeVars := Scheme.mem_freeVars.mp hp
    refine ⟨p + s.arity, hbody, ?_⟩
    rw [if_neg (by omega : ¬ p + s.arity < s.arity), Nat.add_sub_cancel, Ty.mem_freeVars_shift]
    exact ⟨m, hmem, by omega⟩

/-- **`CtxWf` is monotone in the level.** A context below `n` is below any `n' ≥ n`. Pairs with
`Ty.LevelMap.mono` for `hasType_subst`'s bump-at-binders: descending into a `lam`/`let` body raises the
level to cover the bound type's free variables, and both the context and the substitution lift. -/
theorem CtxWf.mono {n n' : Nat} {Γ : Ctx} (hΓ : CtxWf n Γ) (hle : n ≤ n') : CtxWf n' Γ :=
  fun b hb i hi => Nat.lt_of_lt_of_le (hΓ b hb i hi) hle

/-- A `cons` is `CtxWf` iff both head scheme and tail are: the bookkeeping the binder arms of
`hasType_subst` use to (re)assemble `CtxWf n ((x,s)::Γ)`. -/
theorem ctxWf_cons {n : Nat} {x : String} {s : Scheme} {Γ : Ctx} :
    CtxWf n ((x, s) :: Γ) ↔ (∀ i ∈ Scheme.freeVars s, i < n) ∧ CtxWf n Γ := by
  constructor
  · intro h
    exact ⟨h (x, s) (List.mem_cons_self ..), fun b hb => h b (List.mem_cons_of_mem _ hb)⟩
  · rintro ⟨hs, hΓ⟩ b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hs
    · exact hΓ b hb

/-- **`CtxWf` is stable under a level-map substitution.** Substituting a `LevelMap n σ` keeps every
binding's ambient free vars below `n` (an ambient `p < n` maps to `σ p` with `FV(σ p) ⊆ [0,n)`). -/
theorem ctxWf_substCtx {n : Nat} {σ : Nat → Ty} {Γ : Ctx}
    (hΓ : CtxWf n Γ) (hσ : Ty.LevelMap n σ) : CtxWf n (substCtx σ Γ) := by
  obtain ⟨_, hamb⟩ := hσ
  intro b hb i hi
  simp only [substCtx, List.mem_map] at hb
  obtain ⟨⟨y, s⟩, hmem, rfl⟩ := hb
  obtain ⟨p, hp, hpi⟩ := Scheme.mem_freeVars_substScheme.mp hi
  exact hamb p (hΓ (y, s) hmem p hp) i hpi

/-- **`CtxWf n Γ` bridges to the keystone's context-fixing premise.** Any substitution fixing `[0,n)`
fixes a context all of whose ambient free vars are `< n` (`substScheme_eq_of_fixes_free` per binding).
This is the `hΓ` premise `genAt_generalizes`/`genAt_closure_ready` consume. -/
theorem ctxWf_fixed {n : Nat} {Γ : Ctx} (hΓ : CtxWf n Γ)
    {σ' : Nat → Ty} (hfix : ∀ i, i < n → σ' i = .var 0 i) : substCtx σ' Γ = Γ := by
  rw [substCtx_eq_self_iff]
  intro b hb
  exact Scheme.substScheme_eq_of_fixes_free (fun i hi => hfix i (hΓ b hb i hi))

/-! ## Level-native `CtxWfV` (Phase 3b prototype, not yet wired in)

The level-tag analog of `CtxWf` above, bounding a context's bindings' `Ty.levels` instead of
magnitude-based ambient free vars — ported from `LevelTagSpike.lean`'s `CtxWf2`/`ctxWf2_cons` onto the
real `Ctx`/`Scheme`. Confirms the *whole* freshness-threading discipline (not just the one-shot
`subst_instantiateV` commutation) survives on the real system, the same way the spike validated it on
the toy model. Not yet consumed by any rule — `Typing.lean`'s `let_poly` still allocates the old
magnitude-based `n`, not a level counter; that rewiring is Phase 4. -/

/-- **Context below level `ℓ`**: every level occurring in every binding's scheme body (quantifier
level *and* ambient references alike, via `Ty.levels`) is `< ℓ`. -/
def CtxWfV (ℓ : Nat) (Γ : Ctx) : Prop := ∀ b ∈ Γ, ∀ l ∈ b.2.body.levels, l < ℓ

/-- **Freshness extension**: a context below `ℓ`, extended with a new binding generalized (via
`Scheme.genAtV`) at exactly the fresh level `ℓ` (whose body's levels are all `≤ ℓ`, i.e. either
ambient-below-`ℓ` or the new binding's own quantifiers), is below `ℓ + 1`. `genAtV`'s body is `d`
itself (no reindexing), so this ports verbatim from the spike's `ctxWf2_cons`. -/
theorem ctxWfV_cons {ℓ : Nat} {x : String} {d : Ty} {Γ : Ctx}
    (hΓ : CtxWfV ℓ Γ) (hd : ∀ l ∈ d.levels, l ≤ ℓ) :
    CtxWfV (ℓ + 1) ((x, Scheme.genAtV ℓ d) :: Γ) := by
  intro b hb l hl
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Nat.lt_succ_of_le (hd l hl)
  · exact Nat.lt_succ_of_lt (hΓ b hb l hl)

/-- **The freshness bound feeds `subst_instantiateV`'s `hclean` at every deeper level.** If `Γ` is
below `ℓ` and an ambient substitution `σ`'s range only ever uses levels `< ℓ` (e.g. drawn from
`Γ`-typed terms), then `σ` is automatically clean for every level `ℓ' ≥ ℓ` — in particular for any
*even deeper* nested scheme's own level. End-to-end confirmation that the level-tag discipline threads
through arbitrarily deep nesting, ported from the spike's closing example. -/
example {ℓ : Nat} {Γ : Ctx} (_hΓ : CtxWfV ℓ Γ) {σ : Nat → Ty}
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l < ℓ) {ℓ' : Nat} (hge : ℓ ≤ ℓ') :
    ∀ i, ∀ j, j ∉ Ty.freeVarsAt ℓ' (σ i) :=
  Ty.clean_of_levels_lt hσ hge

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
private def cexΓ : Ctx := [("y", Scheme.mono (.var 0 1))]

/-- The generalization **holds** before substitution: every instance `t` of `⟨1, var 0⟩` is
`subst [0↦t] (var 0)` with `[0↦t]` fixing `cexΓ` (it touches only `var 0`, and `FV(cexΓ) = {1}`). -/
private theorem cex_pos : Generalizes ⟨1, 0, .var 0 0⟩ cexΓ (.var 0 0) := by
  intro args
  refine ⟨fun i => if i = 0 then args.getD 0 (.var 0 0) else .var 0 i, ?_, ?_⟩
  · simp [Scheme.instantiate, Ty.subst]
  · simp [cexΓ, substCtx, Scheme.substScheme_mono, Ty.subst]

/-- The generalization **fails** at let-site type `var 1` (the same scheme, but the let-site type is
now a context variable): instantiating to `var 0` would need a `σ'` with `σ' 1 = var 0` *and* (to fix
`cexΓ`) `σ' 1 = var 1`. -/
private theorem cex_neg : ¬ Generalizes ⟨1, 0, .var 0 0⟩ cexΓ (.var 0 1) := by
  intro H
  obtain ⟨σ', heq, hfix⟩ := H [.var 0 0]
  -- hfix : substCtx σ' cexΓ = cexΓ  ⟹  subst σ' (var 1) = var 1
  have hsub : Ty.subst σ' (.var 0 1) = .var 0 1 := by
    have e := hfix
    unfold cexΓ substCtx at e
    simp only [List.map_cons, List.map_nil, Scheme.substScheme_mono, List.cons.injEq,
      Prod.mk.injEq, true_and, and_true] at e
    exact congrArg Scheme.body e
  have hinst : Scheme.instantiate ⟨1, 0, .var 0 0⟩ [Ty.var 0 0] = Ty.var 0 0 := by
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
  have h := H ⟨1, 0, .var 0 0⟩ cexΓ (.var 0 0) (fun i => if i = 0 then .var 0 1 else .var 0 i) cex_pos
  -- normalize the substituted witness back to the `cex_neg` shape, then contradict
  have hs : Scheme.substScheme (fun i => if i = 0 then (.var 0 1 : Ty) else .var 0 i) ⟨1, 0, .var 0 0⟩
      = ⟨1, 0, .var 0 0⟩ := by
    simp [Scheme.substScheme, Ty.subst]
  have hc : substCtx (fun i => if i = 0 then (.var 0 1 : Ty) else .var 0 i) cexΓ = cexΓ := by
    simp [cexΓ, substCtx, Scheme.substScheme_mono, Ty.subst]
  have hd : Ty.subst (fun i => if i = 0 then (.var 0 1 : Ty) else .var 0 i) (.var 0 0) = .var 0 1 := rfl
  rw [hs, hc, hd] at h
  exact cex_neg h

/-! ## Sanity: a polymorphic `let` instantiates `id` at a base type -/

section
open Eyg.Ir.Tree

/-- `let id = \y. y in id 1` — the polymorphic `let` binds `id` at the generalized scheme
`∀α. α → α` (`genAt 0 (var0 → var0)`), and the body instantiates it at `Integer`. -/
example : HasType (m := Unit) []
    (let_ "id" (lambda "y" (variable_ "y")) (apply (variable_ "id") (integer 1)))
    .integer .empty := by
  refine HasType.let_poly (n := 0) (defnTy := .fun (.var 0 0) .empty (.var 0 0)) ?_ ?_ ?_ ?_
  · exact HasType.lam (HasType.var (s := .mono (.var 0 0)) (args := []) rfl)
  · intro b hb; cases hb
  · trivial
  · refine HasType.app (argTy := .integer) ?_ (Ty.effWeaken_refl _) HasType.int
    exact HasType.var (s := Scheme.genAt 0 (.fun (.var 0 0) .empty (.var 0 0)))
      (args := [.integer]) rfl

/-- **Nested-`let` polymorphism (the `noLambdaLet` relaxation).** The generalized lambda's body
contains an **internal mono `let`** (`let y = x in y`) — a binding the old `noLet` premise rejected
outright. With `noLambdaLet` it is accepted: `id' = \x. (let y = x in y)` generalizes to `∀α. α→α`
and the body instantiates it at `Integer`. The body's `let` binds a *variable* (not a `Lambda`), so
`noLambdaLet` holds and `hasType_subst`'s mono `let_` arm carries it. -/
example : HasType (m := Unit) []
    (let_ "id'" (lambda "x" (let_ "y" (variable_ "x") (variable_ "y")))
      (apply (variable_ "id'") (integer 1)))
    .integer .empty := by
  refine HasType.let_poly (n := 0) (defnTy := .fun (.var 0 0) .empty (.var 0 0)) ?_ ?_ ?_ ?_
  · exact HasType.lam (HasType.let_
      (HasType.var (s := .mono (.var 0 0)) (args := []) rfl)
      (HasType.var (s := .mono (.var 0 0)) (args := []) rfl))
  · intro b hb; cases hb
  · trivial
  · refine HasType.app (argTy := .integer) ?_ (Ty.effWeaken_refl _) HasType.int
    exact HasType.var (s := Scheme.genAt 0 (.fun (.var 0 0) .empty (.var 0 0)))
      (args := [.integer]) rfl

end

end Eyg.Types
