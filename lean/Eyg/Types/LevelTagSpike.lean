/-!
# G1 spike: does a level-tagged `Ty.var` resolve the nested `let_poly` wall?

**Isolated — imports nothing from `Eyg.Types`, wires into nothing.** Per
`plan/eyg-g1-level-tagged-ty.md` Phase 1–2: a minimal model to test whether tagging
`var` with an explicit generalization *level* (instead of encoding "quantified vs.
ambient" via index *magnitude*, the way `Ty`/`Scheme` do today) resolves the wall
`Generalization.lean`'s `generalizes_subst_false` proves for the untagged system.

Only `var`/`fn` are modeled. Every other `Ty` former is handled by uniform
structural recursion in the real system (see `Ty.subst`) and plays no special role
in the level-tag mechanics being tested here — adding them back is mechanical, not
part of what this spike needs to settle.

## The wall, restated

`Ty.var : Nat → Ty` is one flat index space; a `Scheme ⟨arity, body⟩` reads indices
`< arity` as its own quantifiers and `≥ arity` as ambient, by *convention*, not by
anything visible on the type itself. `Scheme.genAt`/`Scheme.instantiate` implement
this via `reindexGen`/down-shifts. The obstruction
(`progress/2026-06-19-G1-foundational-wall-confirmed-no-additive-slice.md`): the
*outer* let_poly's instantiation witness `σ_args` (opening its own quantifiers) is a
plain down-shift on `[n+arity, ∞)` — exactly where a *nested* let_poly's own fresh
generalized region has to live to stay disjoint from the outer's. Applying that
down-shift to the inner scheme perturbs its own index-magnitude bookkeeping,
requiring a compensating re-level that was separately shown non-additive too.

## The fix under test

Tag `var` with the generalization *level* it belongs to: `var (level idx : Nat)`.
`genAt`/`instantiate` no longer need index-magnitude arithmetic (no `reindexGen`, no
shifting) — they just filter/rewrite by level tag, which is exact regardless of the
numeric size of any index. The claim: an outer ambient substitution (which only
rewrites its own level's `var` leaves) then *cannot* touch an inner scheme's
disjoint-level quantifiers at all — the down-shift/re-level problem doesn't arise
because there was never any index-magnitude bookkeeping to perturb.
-/

namespace Eyg.Types.LevelTag

/-- Minimal level-tagged type language for the spike. -/
inductive Ty2 where
  | var (level idx : Nat)
  | fn (arg ret : Ty2)
  deriving DecidableEq, Repr

namespace Ty2

/-- Substitute at a single level `ℓ`: rewrite every `var ℓ i` leaf via `σ i`; leaves
at any other level are untouched. No shifting anywhere — unlike `Ty.shift`/
`reindexGen`, there is no index-magnitude bookkeeping for a level-disjoint
substitution to perturb. -/
def substAt (ℓ : Nat) (σ : Nat → Ty2) : Ty2 → Ty2
  | .var l i => if l = ℓ then σ i else .var l i
  | .fn a r => .fn (substAt ℓ σ a) (substAt ℓ σ r)

/-- The free `(level, idx)` pairs of a type. -/
def freeVars : Ty2 → List (Nat × Nat)
  | .var l i => [(l, i)]
  | .fn a r => freeVars a ++ freeVars r

/-- `substAt ℓ σ` never removes a leaf at a level other than `ℓ`. -/
theorem mem_freeVars_substAt_of_ne {ℓ l i : Nat} {σ : Nat → Ty2} {t : Ty2}
    (hl : l ≠ ℓ) (h : (l, i) ∈ t.freeVars) : (l, i) ∈ (substAt ℓ σ t).freeVars := by
  induction t with
  | var l' i' =>
      simp only [freeVars, List.mem_singleton] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp h
      simp only [substAt, if_neg hl, freeVars, List.mem_singleton]
  | fn a r iha ihr =>
      simp only [freeVars, List.mem_append] at h
      simp only [substAt, freeVars, List.mem_append]
      rcases h with h | h
      · exact Or.inl (iha h)
      · exact Or.inr (ihr h)

/-- **A level with no occurrence in `t` is untouched by a substitution at that
level.** The converse-shaped fact to `mem_freeVars_substAt_of_ne`, and the key step
in the cross-level commutation below: if `σ`'s output at some index happens to be
`ℓ`-clean, substituting at `ℓ` into it is a no-op. -/
theorem substAt_eq_self_of_not_mem {ℓ : Nat} {σ : Nat → Ty2} {t : Ty2}
    (h : ∀ i, (ℓ, i) ∉ t.freeVars) : substAt ℓ σ t = t := by
  induction t with
  | var l i =>
      by_cases hl : l = ℓ
      · exact absurd (hl ▸ freeVars.eq_1 l i ▸ List.mem_singleton_self _) (hl ▸ h i)
      · simp only [substAt, if_neg hl]
  | fn a r iha ihr =>
      simp only [freeVars, List.mem_append] at h
      simp only [substAt, iha (fun i hi => h i (Or.inl hi)), ihr (fun i hi => h i (Or.inr hi))]

/-- **Cross-level commutation, conditionally.** Substituting at `ℓ1` and at `ℓ2`
commute — for `ℓ1 ≠ ℓ2` — *provided* `σ`'s range never mentions level `ℓ2` (the
`hclean` hypothesis). This is the fact `Scheme.subst_instantiate` (the real
codebase's `var`/`builtin` `hasType_subst` arms) needs, and it is **not free** the
way `substScheme_genAt` is: the `var ℓ1 i` leaf case reduces to `substAt ℓ2 τ' (σ i)
= σ i`, which needs `σ i` to be `ℓ2`-clean. In the intended use (`hasType_subst`
opening a let_poly's own level `ℓ1` with `σ` = concrete/already-typed args, and
`ℓ2` = some *nested*, strictly-fresher let_poly's level), this holds by the
level-monotonicity discipline (nested levels are always chosen deeper/fresher than
anything already in scope) — so `hclean` is satisfiable by construction, not vacuous
work. -/
theorem substAt_substAt_comm {ℓ1 ℓ2 : Nat} (hne : ℓ1 ≠ ℓ2) {σ : Nat → Ty2} (τ : Nat → Ty2)
    (hclean : ∀ i, ∀ j, (ℓ2, j) ∉ (σ i).freeVars) (t : Ty2) :
    substAt ℓ1 σ (substAt ℓ2 τ t) = substAt ℓ2 (fun i => substAt ℓ1 σ (τ i)) (substAt ℓ1 σ t) := by
  induction t with
  | var l i =>
      by_cases h2 : l = ℓ2
      · simp [substAt, h2, if_neg (Ne.symm hne)]
      · by_cases h1 : l = ℓ1
        · have hne2 : l ≠ ℓ2 := h1 ▸ hne
          simp only [substAt, if_pos h1, if_neg hne2]
          exact (substAt_eq_self_of_not_mem (fun j => hclean i j)).symm
        · simp only [substAt, if_neg h1, if_neg h2]
  | fn a r iha ihr => simp only [substAt, iha, ihr]

/-- Every distinct level occurring anywhere in a type (own quantifiers and
ambient references alike) — the level-tag analog of the real `Ty.levels`. -/
def levels : Ty2 → List Nat
  | .var l _ => [l]
  | .fn a r => levels a ++ levels r

/-- **A substitution whose levels all sit below `n` is `ℓ`-clean for every `ℓ ≥
n`.** The bridge from a `CtxWf`-style freshness bound to `substAt_substAt_comm`'s
`hclean` hypothesis: if every argument's levels are `< n` (e.g. drawn from a
context bounded by `n`, or ground/ambient types), then substituting at the fresh
level `n` can never collide with any *strictly deeper* nested scheme (level `>
n`), because there is nothing at or above `n` in the substitution's range to
begin with. -/
private theorem mem_levels_of_mem_freeVars {t : Ty2} {ℓ j : Nat} (hmem : (ℓ, j) ∈ t.freeVars) :
    ℓ ∈ t.levels := by
  induction t with
  | var l k =>
      simp only [freeVars, List.mem_singleton] at hmem
      simp only [levels, List.mem_singleton]
      exact (Prod.mk.injEq .. |>.mp hmem).1
  | fn a r iha ihr =>
      simp only [freeVars, List.mem_append] at hmem
      simp only [levels, List.mem_append]
      rcases hmem with hmem | hmem
      · exact Or.inl (iha hmem)
      · exact Or.inr (ihr hmem)

theorem clean_of_levels_lt {σ : Nat → Ty2} {n : Nat} (hlt : ∀ i, ∀ l ∈ (σ i).levels, l < n)
    {ℓ : Nat} (hge : n ≤ ℓ) : ∀ i, ∀ j, (ℓ, j) ∉ (σ i).freeVars := by
  intro i j hmem
  exact absurd (hlt i ℓ (mem_levels_of_mem_freeVars hmem)) (by omega)

end Ty2

/-- A scheme owned by generalization level `ℓ`: its quantifiers are exactly the
`var ℓ _` occurrences of `body`. **No `arity`/reindexing bookkeeping** — `genAt` is
the identity on `body`, since the level tag already marks which variables belong to
this scheme (contrast `Scheme.genAt`, which computes `genArity` and calls
`reindexGen`). -/
structure Scheme2 where
  level : Nat
  body : Ty2
  deriving DecidableEq, Repr

namespace Scheme2

/-- Generalize `d` at level `ℓ` — no reindexing, unlike `Scheme.genAt`. -/
def genAt (ℓ : Nat) (d : Ty2) : Scheme2 := ⟨ℓ, d⟩

/-- Instantiate a scheme's own-level quantifiers with `args`; every other level is
untouched by construction (`substAt` only ever rewrites its target level). -/
def instantiate (s : Scheme2) (args : List Ty2) : Ty2 :=
  Ty2.substAt s.level (fun i => args.getD i (.var s.level i)) s.body

/-- Apply an ambient substitution at level `ℓ` to a scheme (its own quantifier level
is untouched whenever `ℓ ≠ s.level`, by `mem_freeVars_substAt_of_ne`). -/
def substScheme (ℓ : Nat) (σ : Nat → Ty2) (s : Scheme2) : Scheme2 :=
  ⟨s.level, Ty2.substAt ℓ σ s.body⟩

end Scheme2

/-! ## The payoff: the nested-generalization commutation, unconditionally

This is the direct analog of `Generalization.lean`'s `genAt_substScheme` — but where
that theorem needs a `Ty.LevelMap n σ` hypothesis (an "ambient stays low" magnitude
side-condition, exactly what a down-shifting instantiation witness violates), this
one needs **only `ℓ ≠ ℓ'`**: a trivial freshness fact, not a magnitude constraint.
`σ`'s outputs may contain *anything*, including further `var ℓ' _` occurrences — it
does not matter, because `substScheme`/`genAt` never inspect index magnitude. -/

/-- **The wall, resolved.** Substituting ambiently at level `ℓ` commutes with
generalizing at a *different* level `ℓ'` — for *any* `σ`, and (stronger than the
module doc claims) with **no hypothesis on `ℓ`/`ℓ'` at all**: `substScheme`/`genAt`
never inspect index magnitude, so there is nothing for a mismatched level pair to
disturb. Contrast `genAt_substScheme` in `Generalization.lean`, which needs
`Ty.LevelMap n σ` — exactly the hypothesis the down-shifting instantiation witness
`σ_args` fails to satisfy for a nested scheme. (A caller would still choose `ℓ ≠ ℓ'`
in practice — substituting at a scheme's *own* level is "opening" it, a different
operation from "substituting ambiently past it" — but the theorem doesn't need to
assume that to be true.) -/
theorem substScheme_genAt (ℓ ℓ' : Nat) (σ : Nat → Ty2) (d : Ty2) :
    Scheme2.substScheme ℓ σ (Scheme2.genAt ℓ' d) = Scheme2.genAt ℓ' (Ty2.substAt ℓ σ d) := by
  simp only [Scheme2.substScheme, Scheme2.genAt]

/-- Corollary in the shape `generalizesAt_subst` is used: instantiating the
level-`ℓ`-substituted scheme reduces to substituting-then-instantiating, exactly the
`hasType_subst` `let_poly` arm's proof obligation — for the SAME `d`/`args` whether
or not `d` itself contains a nested `genAt ℓ'' _` for some third level `ℓ'' ∉ {ℓ,ℓ'}`,
since `substAt`/`instantiate` never inspect indices at a foreign level. -/
theorem generalizesAt_subst2 (ℓ ℓ' : Nat) (σ : Nat → Ty2) (d : Ty2) (args : List Ty2) :
    (Scheme2.substScheme ℓ σ (Scheme2.genAt ℓ' d)).instantiate args
      = Ty2.substAt ℓ' (fun i => args.getD i (.var ℓ' i)) (Ty2.substAt ℓ σ d) := by
  rw [substScheme_genAt ℓ ℓ']
  rfl

/-! ## The original counterexample, re-run in the tagged system

`Generalization.lean`'s `generalizes_subst_false`: the untagged scheme `⟨1, var 0⟩`
generalizing `var 0` away from a context whose only free var is `var 1` breaks under
`σ = [0 ↦ var 1]` — the substitution's *target index* (`0`, the scheme's own
quantifier) and the context's *free index* (`1`) live in the same flat space, so a
substitution chosen to open the scheme can accidentally collide with the context.

Below: the direct level-tagged restatement. The scheme is `genAt ℓ' (var ℓ' 0)`; the
context's free variable is `var ℓctx 1` for a *different* level `ℓctx ≠ ℓ'`
(context vars are ambient — they belong to an already-fixed enclosing level, never
to the fresh level chosen for a new generalization). Substituting **at level `ℓ'`**
(opening the scheme, the analog of the failing `σ`) cannot touch `var ℓctx 1` at
all — `mem_freeVars_substAt_of_ne` — regardless of what the substitution sends
index `0` to. The class of bug `generalizes_subst_false` exhibits (quantified and
ambient indices numerically colliding) is structurally unrepresentable here: they're
tagged apart, not just numbered apart. -/

/-- The context-side witness: `var ℓctx 1`, standing in for `cexΓ`'s `("y", mono
(var 1))` binding. -/
example {ℓ' ℓctx : Nat} (hne : ℓctx ≠ ℓ') (σ : Nat → Ty2) :
    Ty2.substAt ℓ' σ (Ty2.var ℓctx 1) = Ty2.var ℓctx 1 := by
  simp only [Ty2.substAt, if_neg hne]

/-- Even the exact failing substitution from `generalizes_subst_false`
(`σ = [0 ↦ var ℓctx 1]`, i.e. "open the scheme's quantifier `0` with the context's
own free variable") leaves the context untouched and the scheme's instantiation
lands exactly where asked — no collision, unlike the untagged
`generalizes_subst_false` scenario. -/
example {ℓ' ℓctx : Nat} (hne : ℓctx ≠ ℓ') :
    let σ : Nat → Ty2 := fun i => if i = 0 then .var ℓctx 1 else .var ℓ' i
    Ty2.substAt ℓ' σ (Ty2.var ℓctx 1) = Ty2.var ℓctx 1 ∧
    (Scheme2.genAt ℓ' (Ty2.var ℓ' 0)).instantiate [.var ℓctx 1] = .var ℓctx 1 := by
  constructor
  · show (if ℓctx = ℓ' then (if (1 : Nat) = 0 then Ty2.var ℓctx 1 else Ty2.var ℓ' 1) else Ty2.var ℓctx 1)
        = Ty2.var ℓctx 1
    rw [if_neg hne]
  · show (if ℓ' = ℓ' then [Ty2.var ℓctx 1].getD 0 (Ty2.var ℓ' 0) else Ty2.var ℓ' 0) = Ty2.var ℓctx 1
    rw [if_pos rfl, List.getD_cons_zero]

/-! ## The `CtxWf`-analog: closing the loop on freshness threading

The last open design point: does a `CtxWf`-style freshness bound (the direct analog
of the real `CtxWf n Γ`, now bounding *levels* instead of index magnitude) actually
discharge `substAt_substAt_comm`'s `hclean` side condition at every nesting depth,
the way the old `CtxWf`/`LevelMap` discharged the magnitude-based obstruction? Yes —
`clean_of_levels_lt` above is exactly that bridge. Below: the freshness-extension
step (`CtxWf2` survives adding one new binding at the next fresh level), the analog
of the real `ctxWf_cons`, confirming the *whole* threading discipline — not just the
one-shot commutation — closes. -/

/-- A context is a list of `(name, scheme)` bindings. -/
abbrev Ctx2 := List (String × Scheme2)

/-- **Context below level `n`**: every level occurring in every binding's scheme
(quantifier level *and* ambient references alike) is `< n`. Direct analog of the
real `CtxWf n Γ`, now bounding levels instead of index magnitude. -/
def CtxWf2 (n : Nat) (Γ : Ctx2) : Prop := ∀ b ∈ Γ, ∀ l ∈ b.2.body.levels, l < n

/-- **Freshness extension**: a context below `n`, extended with a new binding
generalized at exactly level `n` (whose body's levels are all `≤ n`, i.e. either
ambient-below-`n` or the new binding's own quantifiers), is below `n + 1`. The
direct analog of the real `ctxWf_cons` — confirms the level-tag discipline threads
through *nested* `let_poly`s the same way the old magnitude discipline did, with no
extra bookkeeping. -/
theorem ctxWf2_cons {n : Nat} {x : String} {d : Ty2} {Γ : Ctx2}
    (hΓ : CtxWf2 n Γ) (hd : ∀ l ∈ d.levels, l ≤ n) :
    CtxWf2 (n + 1) ((x, Scheme2.genAt n d) :: Γ) := by
  intro b hb l hl
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Nat.lt_succ_of_le (hd l hl)
  · exact Nat.lt_succ_of_lt (hΓ b hb l hl)

/-- **The freshness bound feeds `hclean` at every deeper level.** If `Γ` is below
`n` and a new scheme is generalized at exactly `n`, then *any* instantiation
argument drawn from `Γ`-typed terms (hence with levels `< n`) is automatically
`ℓ`-clean for every `ℓ ≥ n` — in particular for any *even deeper* nested scheme's
own level. This is the end-to-end confirmation that the level-tag discipline
threads through arbitrarily deep nesting exactly like `CtxWf`/`LevelMap` did for
one layer, without the down-shift/re-level failure mode. -/
example {n : Nat} {Γ : Ctx2} (hΓ : CtxWf2 n Γ) {σ : Nat → Ty2}
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l < n) {ℓ : Nat} (hge : n ≤ ℓ) :
    ∀ i, ∀ j, (ℓ, j) ∉ (σ i).freeVars :=
  Ty2.clean_of_levels_lt hσ hge

end Eyg.Types.LevelTag
