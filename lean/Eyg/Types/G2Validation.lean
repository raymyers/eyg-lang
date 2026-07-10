import Eyg.Types.Runtime

/-!
# G2 keystone regressions — universal readiness at the off-scheme instantiations

Permanent machine-checked witnesses for the `eyg-g2-args-discipline-universal-readiness` plan
(Phase 1). These are the *consumption-side* facts that the G1 Phase-6 wall (G27–G31) proved could
not be routed through any `{0, s.level}`-bounded `HasTypeRT`/readiness architecture — yet which are
plainly **true** of the exact counterexample values at their fatal instantiations. Landing them here
pins the plan's premise: the old architecture was not asking for something false; it merely could
not witness it. See `plan/eyg-g2-args-discipline-universal-readiness.md` §1 and its appendix.

- **V1** — the G30 counterexample value `\x.x` typed at `(genAtV 1 (α→α)).instantiateV [.var 2 0]`
  (the single off-level instantiation `HasTypeRT` could not witness).
- **V2** — the G31 value `\x.\y.x` typed at `(genAtV 1 (α→β→α)).instantiateV [.var 2 0, .var 5 0]`
  (two independent off-scheme levels, one escaping into the result type). Universal readiness is
  TRUE at exactly the args that refuted every bounded design.
- **V3** — necessity of per-level freshness: a σ-range level hitting an inner gen level genuinely
  captures (`genAtV` arity changes), so the `{0, ℓ}` bound really was capture-avoidance in disguise.
- **V4** — sufficiency at fresh level: with σ at a fresh level the arity is stable and the
  `substAt`/`instantiateV` commutation holds.
- **V5** — the G31 *program* admits a **disciplined** derivation (defn sublevel/floor chosen above
  all lookup arg levels); the escaping level-5 choice was gratuitous.
- **V6** — readiness also covers V5's disciplined instantiation.
-/

namespace Eyg.Types.G2Validation

open Eyg.Types Eyg.Ir Eyg.Ir.Tree

abbrev defnA : Ty := .fun (.var 1 0) .empty (.var 1 0)
abbrev defnAB : Ty := .fun (.var 1 0) .empty (.fun (.var 1 1) .empty (.var 1 0))

-- V1
example : (Scheme.genAtV 1 defnA).instantiateV [.var 2 0]
    = .fun (.var 2 0) .empty (.var 2 0) := by decide

/-- **V1.** The G30 counterexample value `Closure "x" x []` is typeable at the off-scheme
instantiation `(genAtV 1 (α→α)).instantiateV [.var 2 0]` that `HasTypeRT` could not witness. -/
theorem v1 : HasTypeV (m := Unit) (.Closure "x" (variable_ "x") [])
    ((Scheme.genAtV 1 defnA).instantiateV [.var 2 0]) := by
  have hinst : (Scheme.genAtV 1 defnA).instantiateV [.var 2 0]
      = .fun (.var 2 0) .empty (.var 2 0) := by decide
  rw [hinst]
  have hbody : HasType (m := Unit) 3 [("x", Scheme.mono (.var 2 0))]
      (variable_ "x") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3) (Γ := [("x", Scheme.mono (.var 2 0))])
      (x := "x") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  exact HasTypeV.closure (lvl' := 3) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody (.refl _)

-- V2
example : (Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 5 0]
    = .fun (.var 2 0) .empty (.fun (.var 5 0) .empty (.var 2 0)) := by decide

/-- **V2.** The G31 value `Closure "x" (\y.x) []` typed at two independent off-scheme levels
`[.var 2 0, .var 5 0]`, one (level 5) escaping into the result type — the exact multiplicity that
refuted every single-level bounded design. -/
theorem v2 : HasTypeV (m := Unit) (.Closure "x" (lambda "y" (variable_ "x")) [])
    ((Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 5 0]) := by
  have hinst : (Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 5 0]
      = .fun (.var 2 0) .empty (.fun (.var 5 0) .empty (.var 2 0)) := by decide
  rw [hinst]
  have hx : HasType (m := Unit) 6
      [("y", Scheme.mono (.var 5 0)), ("x", Scheme.mono (.var 2 0))]
      (variable_ "x") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 6)
      (Γ := [("y", Scheme.mono (.var 5 0)), ("x", Scheme.mono (.var 2 0))])
      (x := "x") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hbody : HasType (m := Unit) 6 [("x", Scheme.mono (.var 2 0))]
      (lambda "y" (variable_ "x")) (.fun (.var 5 0) .empty (.var 2 0)) .empty :=
    HasType.lam (le_refl 6)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hx
  exact HasTypeV.closure (lvl' := 6) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody (.refl _)

-- V3
abbrev dCap : Ty := .fun (.var 1 0) .empty (.var 2 0)

/-- **V3.** Necessity of per-level freshness: substituting `.var 2 0` at level 1 into a scheme body
with an inner gen level 2 changes `genAtV 2`'s arity 1→2 (capture). The `{0, ℓ}` bound really was
capture-avoidance; `hasType_substAt_multi` must (and need only) demand σ-range levels avoid
gen/scheme levels. -/
example : (Scheme.genAtV 2 dCap).arity = 1 := by decide
example : (Scheme.genAtV 2 (Ty.substAt 1 (fun _ => .var 2 0) dCap)).arity = 2 := by decide
example : Scheme.genAtV 2 (Ty.substAt 1 (fun _ => .var 2 0) dCap)
    ≠ Scheme.genAtV 2 dCap := by decide

-- V4
/-- **V4.** Sufficiency at a fresh level: with σ at level 3 (fresh) the arity is stable and the
`substAt`/`instantiateV` commutation holds. -/
example : (Scheme.genAtV 2 (Ty.substAt 1 (fun _ => .var 3 0) dCap)).arity
    = (Scheme.genAtV 2 dCap).arity := by decide

example :
    Ty.substAt 1 (fun _ => .var 3 0)
      ((Scheme.genAtV 2 dCap).instantiateV [.integer])
    = (Scheme.genAtV 2 (Ty.substAt 1 (fun _ => .var 3 0) dCap)).instantiateV
        [Ty.substAt 1 (fun _ => .var 3 0) .integer] := by decide

-- V5
abbrev ΓAB' : Ctx := [("a", Scheme.genAtV 1 defnAB)]
abbrev ΓABw' : Ctx := ("w", Scheme.mono (.var 2 0)) :: ΓAB'

theorem v5_body : HasType (m := Unit) 3 ΓABw'
    (apply (variable_ "a") (variable_ "w"))
    (.fun (.var 2 1) .empty (.var 2 0)) .empty := by
  have haType : (Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 2 1]
      = .fun (.var 2 0) .empty (.fun (.var 2 1) .empty (.var 2 0)) := by decide
  have ha : HasType (m := Unit) 3 ΓABw' (variable_ "a")
      (.fun (.var 2 0) .empty (.fun (.var 2 1) .empty (.var 2 0))) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3) (Γ := ΓABw') (x := "a")
      (s := Scheme.genAtV 1 defnAB) (args := [.var 2 0, .var 2 1]) (ε := .empty)
      (a := ()) (by decide)
    rwa [haType] at h
  have hw : HasType (m := Unit) 3 ΓABw' (variable_ "w") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3) (Γ := ΓABw') (x := "w")
      (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  exact HasType.app ha (Ty.effWeaken_refl _) hw

/-- **V5.** The G31 program admits a **disciplined** derivation: same program, lookup args
`[.var 2 0, .var 2 1]`, defn sublevel (floor) chosen `lvl' = 3 >` all lookup arg levels. The
escaping level-5 choice of the naive derivation was gratuitous. -/
theorem v5 : HasType (m := Unit) 1 []
    (let_ "a" (lambda "x" (lambda "y" (variable_ "x")))
      (lambda "w" (apply (variable_ "a") (variable_ "w"))))
    (.fun (.var 2 0) .empty (.fun (.var 2 1) .empty (.var 2 0))) .empty := by
  have hx : HasType (m := Unit) 3
      [("y", Scheme.mono (.var 1 1)), ("x", Scheme.mono (.var 1 0))]
      (variable_ "x") (.var 1 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3)
      (Γ := [("y", Scheme.mono (.var 1 1)), ("x", Scheme.mono (.var 1 0))])
      (x := "x") (s := Scheme.mono (.var 1 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hbodydefn : HasType (m := Unit) 3 [("x", Scheme.mono (.var 1 0))]
      (lambda "y" (variable_ "x")) (.fun (.var 1 1) .empty (.var 1 0)) .empty :=
    HasType.lam (le_refl 3)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hx
  have hlamw : HasType (m := Unit) 2 ΓAB'
      (lambda "w" (apply (variable_ "a") (variable_ "w")))
      (.fun (.var 2 0) .empty (.fun (.var 2 1) .empty (.var 2 0))) .empty :=
    HasType.lam (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
      v5_body
  exact HasType.let_poly (by omega)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbodydefn (by intro b hb; cases hb) hlamw

-- V6
/-- **V6.** Readiness also covers V5's disciplined instantiation: the closure `\x.\y.x` typed at
`(genAtV 1 (α→β→α)).instantiateV [.var 2 0, .var 2 1]` (all lookup arg levels below the floor). -/
theorem v6 : HasTypeV (m := Unit) (.Closure "x" (lambda "y" (variable_ "x")) [])
    ((Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 2 1]) := by
  have hinst : (Scheme.genAtV 1 defnAB).instantiateV [.var 2 0, .var 2 1]
      = .fun (.var 2 0) .empty (.fun (.var 2 1) .empty (.var 2 0)) := by decide
  rw [hinst]
  have hx : HasType (m := Unit) 3
      [("y", Scheme.mono (.var 2 1)), ("x", Scheme.mono (.var 2 0))]
      (variable_ "x") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3)
      (Γ := [("y", Scheme.mono (.var 2 1)), ("x", Scheme.mono (.var 2 0))])
      (x := "x") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hbody : HasType (m := Unit) 3 [("x", Scheme.mono (.var 2 0))]
      (lambda "y" (variable_ "x")) (.fun (.var 2 1) .empty (.var 2 0)) .empty :=
    HasType.lam (le_refl 3)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hx
  exact HasTypeV.closure (lvl' := 3) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody (.refl _)

-- V7 — the decisive capture-prone case (for the unconditional-readiness prove/refute).
/-- **V7.** A closure whose body contains an **inner generalizable `let`**, typed at an off-scheme
instantiation — the case V1/V2 do not exercise (they have no inner `let_poly`, hence no capture
risk). The closure `\x. (let g = \y.y in g x)` has scheme `genAtV 1 (α→α)`; instantiated at
`[.var 2 0]` it must inhabit `.var 2 0 → .var 2 0`. The runtime **value** carries no fixed inner
gen level, so the readiness derivation is free to generalize the inner `g` at a **fresh** level
(here 3 ≠ 2), sidestepping the capture that the `substAt`-route hits. Machine-checked evidence that
universal (`ArgsDisc`-free) readiness holds even in the capture-prone case — the crux of route B. -/
theorem v7 : HasTypeV (m := Unit)
    (.Closure "x"
      (let_ "g" (lambda "y" (variable_ "y")) (apply (variable_ "g") (variable_ "x"))) [])
    ((Scheme.genAtV 1 defnA).instantiateV [.var 2 0]) := by
  have hinst : (Scheme.genAtV 1 defnA).instantiateV [.var 2 0]
      = .fun (.var 2 0) .empty (.var 2 0) := by decide
  rw [hinst]
  -- inner defn `\y.y` : g's scheme body, generalized fresh at level 3
  have hgy : HasType (m := Unit) 4
      [("y", Scheme.mono (.var 3 0)), ("x", Scheme.mono (.var 2 0))]
      (variable_ "y") (.var 3 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 4)
      (Γ := [("y", Scheme.mono (.var 3 0)), ("x", Scheme.mono (.var 2 0))])
      (x := "y") (s := Scheme.mono (.var 3 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  -- inner let body `g x`, with g : genAtV 3 (β→β) instantiated at [.var 2 0]
  have hg : HasType (m := Unit) 4
      [("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
       ("x", Scheme.mono (.var 2 0))]
      (variable_ "g") (.fun (.var 2 0) .empty (.var 2 0)) .empty := by
    have hginst : (Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))).instantiateV [.var 2 0]
        = .fun (.var 2 0) .empty (.var 2 0) := by decide
    have h := HasType.var (m := Unit) (lvl := 4)
      (Γ := [("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
             ("x", Scheme.mono (.var 2 0))])
      (x := "g") (s := Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0)))
      (args := [.var 2 0]) (ε := .empty) (a := ()) (by decide)
    rwa [hginst] at h
  have hxx : HasType (m := Unit) 4
      [("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
       ("x", Scheme.mono (.var 2 0))]
      (variable_ "x") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 4)
      (Γ := [("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
             ("x", Scheme.mono (.var 2 0))])
      (x := "x") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hgx : HasType (m := Unit) 4
      [("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
       ("x", Scheme.mono (.var 2 0))]
      (apply (variable_ "g") (variable_ "x")) (.var 2 0) .empty :=
    HasType.app hg (Ty.effWeaken_refl _) hxx
  have hbody : HasType (m := Unit) 3 [("x", Scheme.mono (.var 2 0))]
      (let_ "g" (lambda "y" (variable_ "y")) (apply (variable_ "g") (variable_ "x")))
      (.var 2 0) .empty :=
    HasType.let_poly (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
      hgy
      (by intro b hb l hl
          rcases List.mem_singleton.mp hb with rfl
          simp only [Scheme.mono, Ty.levels, List.mem_singleton] at hl; omega)
      hgx
  exact HasTypeV.closure (lvl' := 3) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody (.refl _)

-- V8 — the interleaving witness (the residual-reachability prove/refute).
/-- **V8.** The depth-2 case G16 suspected but never machine-confirmed: a closure whose `retTy`
carries an inner-lambda-binder level (3) *above* an inner `let_poly` gen level, typed at a colliding
instantiation. The closure `\x. (let g = \y.y in \w. g x)` has type `α → (γ → α)` — scheme
`genAtV 1 (.var 1 0 → (.var 3 0 → .var 1 0))`; instantiated at `[.var 2 0]` it must inhabit
`.var 2 0 → (.var 3 0 → .var 2 0)`. The *natural* stored derivation would generalize `g` at `b`'s
sublevel `2`, interleaving with the `retTy` binder level `3` — so no threshold `raiseTy` moves `g`
(≤ 2) while fixing `retTy`'s level 3. **Yet the value IS typeable**: generalize `g` **fresh** at 5,
and the colliding instantiation `g @ [.var 2 0]` no longer captures. So readiness is *semantically
true even in the interleaving case*; the difficulty is purely proof-architectural (a fixed stored
derivation transported by a threshold raise cannot reach it — a fresh re-derivation can). This is
why route B is a "prove", and why the closing route must re-derive fresh (or relabel structurally),
not threshold-raise. -/
theorem v8 : HasTypeV (m := Unit)
    (.Closure "x"
      (let_ "g" (lambda "y" (variable_ "y"))
        (lambda "w" (apply (variable_ "g") (variable_ "x")))) [])
    ((Scheme.genAtV 1 (.fun (.var 1 0) .empty (.fun (.var 3 0) .empty (.var 1 0)))).instantiateV
      [.var 2 0]) := by
  have hinst :
      (Scheme.genAtV 1 (.fun (.var 1 0) .empty (.fun (.var 3 0) .empty (.var 1 0)))).instantiateV
        [.var 2 0]
      = .fun (.var 2 0) .empty (.fun (.var 3 0) .empty (.var 2 0)) := by decide
  rw [hinst]
  -- g's defn `\y.y`, generalized FRESH at level 5 (≠ 2, ≠ 3 — avoids the interleaving collision)
  have hgy : HasType (m := Unit) 6
      [("y", Scheme.mono (.var 5 0)), ("x", Scheme.mono (.var 2 0))]
      (variable_ "y") (.var 5 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 6)
      (Γ := [("y", Scheme.mono (.var 5 0)), ("x", Scheme.mono (.var 2 0))])
      (x := "y") (s := Scheme.mono (.var 5 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  -- `g x` at ambient 7: g : genAtV 5 (β→β) instantiated at the colliding [.var 2 0]
  have hg : HasType (m := Unit) 7
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
       ("x", Scheme.mono (.var 2 0))]
      (variable_ "g") (.fun (.var 2 0) .empty (.var 2 0)) .empty := by
    have hginst :
        (Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))).instantiateV [.var 2 0]
        = .fun (.var 2 0) .empty (.var 2 0) := by decide
    have h := HasType.var (m := Unit) (lvl := 7)
      (Γ := [("w", Scheme.mono (.var 3 0)),
             ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
             ("x", Scheme.mono (.var 2 0))])
      (x := "g") (s := Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0)))
      (args := [.var 2 0]) (ε := .empty) (a := ()) (by decide)
    rwa [hginst] at h
  have hx : HasType (m := Unit) 7
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
       ("x", Scheme.mono (.var 2 0))]
      (variable_ "x") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 7)
      (Γ := [("w", Scheme.mono (.var 3 0)),
             ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
             ("x", Scheme.mono (.var 2 0))])
      (x := "x") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hgx : HasType (m := Unit) 7
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
       ("x", Scheme.mono (.var 2 0))]
      (apply (variable_ "g") (variable_ "x")) (.var 2 0) .empty :=
    HasType.app hg (Ty.effWeaken_refl _) hx
  have hlamw : HasType (m := Unit) 6
      [("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
       ("x", Scheme.mono (.var 2 0))]
      (lambda "w" (apply (variable_ "g") (variable_ "x")))
      (.fun (.var 3 0) .empty (.var 2 0)) .empty :=
    HasType.lam (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hgx
  have hbody : HasType (m := Unit) 5 [("x", Scheme.mono (.var 2 0))]
      (let_ "g" (lambda "y" (variable_ "y"))
        (lambda "w" (apply (variable_ "g") (variable_ "x"))))
      (.fun (.var 3 0) .empty (.var 2 0)) .empty :=
    HasType.let_poly (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
      hgy
      (by intro b hb l hl
          rcases List.mem_singleton.mp hb with rfl
          simp only [Scheme.mono, Ty.levels, List.mem_singleton] at hl; omega)
      hlamw
  exact HasTypeV.closure (lvl' := 5) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody (.refl _)

/-! ## V8's B1 obstruction, machine-checked — no separating raise threshold

`HasType.let_poly` generalizes at **exactly** its conclusion ambient `lvl` (`genAtV lvl`, body at
`lvl+1`): an inner `let`'s gen level is rigidly tied to the ambient at which its node is typed, so
it cannot be changed within a fixed derivation without moving ambients — i.e. only by a **monotone**
`raiseTy`. For V8 that is impossible: to move `g`'s gen level (2) the raise threshold `t` must be
`t ≤ 2`, but then `t ≤ 3` so the same raise moves `retTy`'s inner-binder level (3), changing the
closure's advertised type; and any `t` that fixes level 3 (`t > 3`) leaves `g` stranded at 2, where
the instantiation `[.var 2 0]` still captures. The two facts below pin this: **no single threshold
separates "move `g`" from "fix `retTy`".** So B1 (relabel the fixed stored derivation) cannot close
V8 by any threshold raise — the fresh-`g` derivation V8 exhibits is a genuinely *different*
derivation, not a transform of the stored one. -/

/-- Any raise that can move `g`'s gen level 2 (threshold `t ≤ 2`) necessarily moves `retTy`'s
inner-binder level 3 — changing the closure's advertised type. -/
theorem v8_moving_g_moves_retTy (o t : Nat) (ho : 1 ≤ o) (ht : t ≤ 2) :
    Ty.raiseTy t o (.var 3 0) ≠ .var 3 0 := by
  simp only [Ty.raiseTy, if_pos (by omega : t ≤ 3)]
  intro h; injection h with h1 _; omega

/-- Any raise that fixes `retTy`'s inner-binder level 3 strands `g` at level 2 — where the
instantiation `[.var 2 0]` still captures `g`'s gen level 2. -/
theorem v8_fixing_retTy_strands_g (o t : Nat) (ho : 1 ≤ o)
    (hfix : Ty.raiseTy t o (.var 3 0) = .var 3 0) :
    Ty.raiseTy t o (.var 2 0) = .var 2 0 := by
  have ht : ¬ t ≤ 3 := by
    intro hle; simp only [Ty.raiseTy, if_pos hle] at hfix; injection hfix with h1 _; omega
  simp only [Ty.raiseTy, if_neg (by omega : ¬ t ≤ 2)]

end Eyg.Types.G2Validation
