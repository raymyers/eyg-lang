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

end Eyg.Types.LevelTag
