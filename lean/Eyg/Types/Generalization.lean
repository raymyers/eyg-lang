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
  ∀ args, ∃ σ', s.instantiate args = Ty.subst σ' d ∧ ∀ i, i < n → σ' i = .var i

/-- **Bridge: `GeneralizesAt n` implies the keystone's `Generalizes`** when the context `Γ` is below
level `n` (any `[0,n)`-fixing substitution fixes it). So the level-indexed predicate slots directly
into `generalizes_closure_ready` — the keystone is unchanged; only the freshness premise sharpens. -/
theorem generalizesAt_to_generalizes {n : Nat} {s : Scheme} {Γ : Ctx} {d : Ty}
    (hΓ : ∀ σ' : Nat → Ty, (∀ i, i < n → σ' i = .var i) → substCtx σ' Γ = Γ)
    (hg : GeneralizesAt n s d) : Generalizes s Γ d := by
  intro args
  obtain ⟨σ', heq, hfix⟩ := hg args
  exact ⟨σ', heq, hΓ σ' hfix⟩

/-- The monomorphic scheme generalizes at **any** level (no variables are generalized, so the
identity `σ'` — which fixes `[0,n)` — witnesses every instantiation). The `arity = 0` base case. -/
theorem generalizesAt_mono (n : Nat) (τ : Ty) : GeneralizesAt n (Scheme.mono τ) τ := by
  intro args
  exact ⟨fun i => .var i, by rw [Scheme.instantiate_mono, Ty.subst_id], fun i _ => rfl⟩

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

/-- Generalization **arity** at level `n`: one quantifier slot per generalized variable (`≥ n`) of
`d`, sized so every such variable fits (`v - n < genArity` for `v ≥ n` free in `d`). Closed-below-`n`
types get arity `0` (monomorphic). -/
def genArity (n : Nat) (d : Ty) : Nat := (d.freeVars.map (fun v => v + 1 - n)).foldr Nat.max 0

/-- The re-indexing turning `d` into a level-`n` scheme body with `arity` quantifiers: ambient vars
(`< n`) shift up past the prefix; generalized vars (`≥ n`) become quantifier `v - n`. -/
def reindexGen (n arity : Nat) : Nat → Ty :=
  fun v => if v < n then .var (v + arity) else .var (v - n)

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
  (∀ i, n ≤ i → σ i = .var i) ∧ (∀ i, i < n → ∀ w ∈ (σ i).freeVars, w < n)

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

/-- The computed generalization of `d` at level `n`: quantify the generalized (`≥ n`) variables. -/
def Scheme.genAt (n : Nat) (d : Ty) : Scheme :=
  ⟨d.genArity n, Ty.subst (Ty.reindexGen n (d.genArity n)) d⟩

@[simp] theorem Scheme.genAt_arity (n : Nat) (d : Ty) : (genAt n d).arity = d.genArity n := rfl

/-- Componentwise scheme equality (the `body` field is non-dependent). -/
theorem Scheme.ext' {s t : Scheme} (ha : s.arity = t.arity) (hb : s.body = t.body) : s = t := by
  cases s; cases t; cases ha; cases hb; rfl

/-- **`genAt` is a sound generalization** — every instantiation of `genAt n d` is a `subst`-instance
of `d` whose witnessing substitution fixes the ambient region `[0,n)`. (The witness fixes `[0,n)`
*regardless* of the arity: an ambient var `i < n` is reindexed to `i + arity ≥ arity`, which
`instantiate` shifts straight back to `var i`.) -/
theorem genAt_generalizesAt (n : Nat) (d : Ty) : GeneralizesAt n (Scheme.genAt n d) d := by
  intro args
  refine ⟨fun v => Ty.subst
      (fun j => if j < d.genArity n then args.getD j (.var j) else .var (j - d.genArity n))
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
    (hΓ : ∀ σ' : Nat → Ty, (∀ i, i < n → σ' i = .var i) → substCtx σ' Γ = Γ) :
    Generalizes (Scheme.genAt n d) Γ d :=
  generalizesAt_to_generalizes hΓ (genAt_generalizesAt n d)

/-- **Push-time polymorphic readiness for a `genAt`-generalized `let`.** Combines the rule-facing
bridge `genAt_generalizes` with the keystone `generalizes_closure_ready`: a let-bound lambda's runtime
closure inhabits **every** instantiation of its computed scheme `genAt n defnTy` (for a context below
level `n`). This is the closed readiness `Rdy` the `Assign`-push computes once, at the one coherent
point, and carries across the lambda→closure step (the coupling design's `StackWfV`). -/
theorem genAt_closure_ready {n : Nat} {Γ : Ctx} {x : String} {body : Tree.Node m} {a : m}
    {env : Env m} {defnTy ε : Ty}
    (hΓ : ∀ σ' : Nat → Ty, (∀ i, i < n → σ' i = .var i) → substCtx σ' Γ = Γ)
    (henv : EnvWf env Γ)
    (hlam : HasType Γ (⟨.Lambda x body, a⟩ : Tree.Node m) defnTy ε) :
    ∀ args, HasTypeV (Value.Closure x body env) ((Scheme.genAt n defnTy).instantiate args) :=
  generalizes_closure_ready (genAt_generalizes hΓ) henv hlam

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
  refine Scheme.ext' ?_ ?_
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
    rw [show Ty.reindexGen n (d.genArity n) v = Ty.var (v + d.genArity n) from by
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
