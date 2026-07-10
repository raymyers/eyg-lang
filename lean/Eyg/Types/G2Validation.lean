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

/-! ## W1 — the CORRECT closure-apply wall witness (G30), and the floor crossing it

Correction to the V8 framing above: V8 is a true readiness *value* witness, but it is **not** a
witness of the closure-apply wall (its inner `g = \y.y` doesn't capture `x`, and its arg sits below
the sublevel, so the floor keystone handles it). The genuine wall is about **maintaining the
`HasTypeRT` args-condition across a closure-apply** — this is the plan's G30 program.

`let a = \x.x in \w. a w`: when the closure `\w. a w` is applied, its body `a w` becomes the control
and instantiates `a` at `[w's type = .var 2 0]` (level 2). `HasTypeRT.var`'s condition is
`args ⊆ {0, s.level}` with `s.level = 1` — and `2 ∉ {0, 1}`, so `HasTypeRT` of the body is
unobtainable. That is the real, documented wall (`w1_old_condition_fails`). The **floor-widened**
condition `l = 0 ∨ l = 1 ∨ l < B` with `B =` a's defn sublevel (chosen `3 > 2`) **holds**
(`w1_floor_condition_holds`) — crossing the wall for this (args-disciplined) derivation. Since a's
`retTy = .var 1 0` is low, an *undisciplined* derivation (sublevel 2) can raise a's floor to 3 with
`retTy` fixed — so G30 closes either way. -/

/-- The G30 program, well-typed with `a`'s defn sublevel chosen `3` (> `w`'s level 2). -/
theorem w1 : HasType (m := Unit) 1 []
    (let_ "a" (lambda "x" (variable_ "x"))
      (lambda "w" (apply (variable_ "a") (variable_ "w"))))
    (.fun (.var 2 0) .empty (.var 2 0)) .empty := by
  have hxdefn : HasType (m := Unit) 3 [("x", Scheme.mono (.var 1 0))]
      (variable_ "x") (.var 1 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3) (Γ := [("x", Scheme.mono (.var 1 0))])
      (x := "x") (s := Scheme.mono (.var 1 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have haw : HasType (m := Unit) 3
      [("w", Scheme.mono (.var 2 0)),
       ("a", Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0)))]
      (apply (variable_ "a") (variable_ "w")) (.var 2 0) .empty := by
    have hainst : (Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0))).instantiateV [.var 2 0]
        = .fun (.var 2 0) .empty (.var 2 0) := by decide
    have ha := HasType.var (m := Unit) (lvl := 3)
      (Γ := [("w", Scheme.mono (.var 2 0)),
             ("a", Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0)))])
      (x := "a") (s := Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0)))
      (args := [.var 2 0]) (ε := .empty) (a := ()) (by decide)
    rw [hainst] at ha
    have hw := HasType.var (m := Unit) (lvl := 3)
      (Γ := [("w", Scheme.mono (.var 2 0)),
             ("a", Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0)))])
      (x := "w") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rw [Scheme.instantiateV_mono] at hw
    exact HasType.app ha (Ty.effWeaken_refl _) hw
  have hlamw : HasType (m := Unit) 2
      [("a", Scheme.genAtV 1 (.fun (.var 1 0) .empty (.var 1 0)))]
      (lambda "w" (apply (variable_ "a") (variable_ "w")))
      (.fun (.var 2 0) .empty (.var 2 0)) .empty :=
    HasType.lam (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) haw
  exact HasType.let_poly (by omega)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hxdefn (by intro b hb; cases hb) hlamw

/-- The wall: `a`'s args `[.var 2 0]` break the old `HasTypeRT.var` condition `⊆ {0, s.level}`. -/
theorem w1_old_condition_fails : ¬ (∀ l ∈ (Ty.var 2 0).levels, l = 0 ∨ l = 1) := by decide

/-- The crossing: the floor-widened condition (`l < 3`, a's sublevel) holds for `[.var 2 0]`. -/
theorem w1_floor_condition_holds : ∀ l ∈ (Ty.var 2 0).levels, l = 0 ∨ l = 1 ∨ l < 3 := by decide

/-! ## R1 — the escaping-`retTy` candidate admits a DISCIPLINED (closing) derivation

The residual for unconditional route B is the escaping-`retTy` case: a closure whose `retTy` has a
level `≥ lvl'`. The sharpest candidate is `\x. (let g = \y.x in \w. g w)` — `x` flows into `g`'s
generalized defn, and `\w` is *inside* `g`'s let, so `\w`'s binder level can sit above `g`'s gen
level. R1 machine-checks that this closure **admits a disciplined derivation**: `g` generalized
fresh at 5, and `\w`'s binder level chosen **3** (kept *below* the sublevel 5). Then
`retTy = .var 3 0 → .var 1 0` has all levels `{3, 1} < lvl' = 5` (`r1_retTy_below_sublevel`) — the
CLOSING case, so `genAtV_instantiate_lam_ready_universal` discharges readiness at any args.

So the escaping-`retTy` residual is a **level choice**, not an inherent obstruction: a binder's
*level* is independent of its *ambient* (here binder 3 under ambient 6), so the same closure syntax
admits a `retTy < lvl'` derivation. The remaining open question is whether the *program's inference*
is forced to produce an escaping scheme (binder level `=` ambient) or free to produce a disciplined
one — a
generation-semantics question, not a readiness-transform obstruction. -/
theorem r1_disciplined_body : HasType (m := Unit) 5 [("x", Scheme.mono (.var 1 0))]
    (let_ "g" (lambda "y" (variable_ "x"))
      (lambda "w" (apply (variable_ "g") (variable_ "w"))))
    (.fun (.var 3 0) .empty (.var 1 0)) .empty := by
  have hgdefn : HasType (m := Unit) 6
      [("y", Scheme.mono (.var 5 0)), ("x", Scheme.mono (.var 1 0))]
      (variable_ "x") (.var 1 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 6)
      (Γ := [("y", Scheme.mono (.var 5 0)), ("x", Scheme.mono (.var 1 0))])
      (x := "x") (s := Scheme.mono (.var 1 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hg : HasType (m := Unit) 7
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 1 0))),
       ("x", Scheme.mono (.var 1 0))]
      (variable_ "g") (.fun (.var 3 0) .empty (.var 1 0)) .empty := by
    have hginst : (Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 1 0))).instantiateV [.var 3 0]
        = .fun (.var 3 0) .empty (.var 1 0) := by decide
    have h := HasType.var (m := Unit) (lvl := 7)
      (Γ := [("w", Scheme.mono (.var 3 0)),
             ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 1 0))),
             ("x", Scheme.mono (.var 1 0))])
      (x := "g") (s := Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 1 0)))
      (args := [.var 3 0]) (ε := .empty) (a := ()) (by decide)
    rwa [hginst] at h
  have hw : HasType (m := Unit) 7
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 1 0))),
       ("x", Scheme.mono (.var 1 0))]
      (variable_ "w") (.var 3 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 7)
      (Γ := [("w", Scheme.mono (.var 3 0)),
             ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 1 0))),
             ("x", Scheme.mono (.var 1 0))])
      (x := "w") (s := Scheme.mono (.var 3 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hgw : HasType (m := Unit) 7
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 1 0))),
       ("x", Scheme.mono (.var 1 0))]
      (apply (variable_ "g") (variable_ "w")) (.var 1 0) .empty :=
    HasType.app hg (Ty.effWeaken_refl _) hw
  have hlamw : HasType (m := Unit) 6
      [("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 1 0))),
       ("x", Scheme.mono (.var 1 0))]
      (lambda "w" (apply (variable_ "g") (variable_ "w")))
      (.fun (.var 3 0) .empty (.var 1 0)) .empty :=
    HasType.lam (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hgw
  exact HasType.let_poly (by omega)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hgdefn
    (by intro b hb l hl
        rcases List.mem_singleton.mp hb with rfl
        simp only [Scheme.mono, Ty.levels, List.mem_singleton] at hl; omega)
    hlamw

/-- R1's `retTy` sits entirely below the sublevel 5 — the closing case. -/
theorem r1_retTy_below_sublevel :
    ∀ l ∈ (Ty.fun (.var 3 0) .empty (.var 1 0)).levels, l < 5 := by decide

/-! ## R2–R4 — settling the generation-semantics question (2026-07-10)

`Generation.lean` turned out to be the **inversion**-lemma file, not an inference algorithm; and
`Generalization.lean`'s docstring pins that inference is a *separate, unbuilt (T8) layer* — the
judgment is purely **declarative**, `HasType.var` quantifying over *arbitrary* instantiation args.
So the "is inference forced to escape?" framing is **moot**: there is no inference to force anything,
and the entry derivation to `soundness` is an *arbitrary* well-typed derivation.

Binder-level assignment lives in `HasType.lam` (`Typing.lean:111`): `lvl ≤ lvl'` (sublevel a *free*
choice `≥` ambient) and `argTy.levels < lvl'` (binder levels strictly *below* the sublevel, otherwise
free — **not** pinned to the ambient). So the declarative system admits **both** disciplined (R1) and
escaping derivations of the same syntax.

**R2/R3** — an escaping-`retTy` closure is genuinely constructible: the K-ish defn `\a. \w2. a` with
the inner binder `w2` chosen at level `1` `=` the outer sublevel `1`, so the outer `retTy` carries a
level `≥` its own sublevel (`r2_retTy_not_below_sublevel`). The closure **value** type-checks
(`r3_escaping_closure`), and at that closure the universal-closing lemma's `hretTy < lvl'` premise
**fails** (`r3_retTy_not_below_sublevel`).

**R4 — but escaping-`retTy` is NOT a readiness wall (for a body without internal generalization).**
Readiness for the *same* escaping closure at a **high** arg (`[.var 5 0]`, level 5 ≥ the stored
sublevel 1) is establishable by **re-typing** the body at a *fresh* sublevel `6` dominating both the
arg (5) and the *fixed* escaping level (1). The escaping level is a bounded constant of the program,
so a dominating sublevel always exists. Hence the escaping-`retTy` case per se is a level choice at
readiness-*construction* time, not an obstruction — the universal-closing lemma's `hretTy < lvl'` is a
limitation of *that* lemma (it reuses the stored sublevel via `hasType_fullRaise`), not a wall.

**Verdict.** The genuine residual is *narrower* than "escaping `retTy`": it is exactly a closure body
with **internal generalization** (a captured polymorphic `let`) whose gen level a uniform raise
cannot move while keeping the advertised type fixed — the G16 two-modes / interleaving structure. That
(not escaping-`retTy`, and not the flawed V8) is the true remaining wall witness to build, tested
against the *re-typing* route above (not only the raise route). -/

-- R2: the escaping-`retTy` defn `\a. \w2. a` (outer sublevel 1, inner binder `w2` at level 1).
theorem r2_escaping_defn : HasType (m := Unit) 0 []
    (lambda "a" (lambda "w2" (variable_ "a")))
    (.fun (.var 0 0) .empty (.fun (.var 1 0) .empty (.var 0 0))) .empty := by
  have ha : HasType (m := Unit) 2
      [("w2", Scheme.mono (.var 1 0)), ("a", Scheme.mono (.var 0 0))]
      (variable_ "a") (.var 0 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 2)
      (Γ := [("w2", Scheme.mono (.var 1 0)), ("a", Scheme.mono (.var 0 0))])
      (x := "a") (s := Scheme.mono (.var 0 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hinner : HasType (m := Unit) 1 [("a", Scheme.mono (.var 0 0))]
      (lambda "w2" (variable_ "a")) (.fun (.var 1 0) .empty (.var 0 0)) .empty :=
    HasType.lam (lvl' := 2) (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) ha
  exact HasType.lam (lvl' := 1) (by omega)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hinner

/-- R2's outer sublevel is 1; its `retTy` carries level 1, NOT `< 1` — escaping. -/
theorem r2_retTy_not_below_sublevel :
    ¬ (∀ l ∈ (Ty.fun (.var 1 0) .empty (.var 0 0)).levels, l < 1) := by decide

-- R3: the escaping closure **value** type-checks at `(genAtV 0 …).instantiateV [.integer]`.
theorem r3_escaping_closure : HasTypeV (m := Unit)
    (.Closure "a" (lambda "w2" (variable_ "a")) [])
    ((Scheme.genAtV 0 (.fun (.var 0 0) .empty (.fun (.var 1 0) .empty (.var 0 0)))).instantiateV
      [.integer]) := by
  have hinst : (Scheme.genAtV 0 (.fun (.var 0 0) .empty (.fun (.var 1 0) .empty (.var 0 0)))).instantiateV
      [.integer] = .fun .integer .empty (.fun (.var 1 0) .empty .integer) := by decide
  rw [hinst]
  have ha : HasType (m := Unit) 2
      [("w2", Scheme.mono (.var 1 0)), ("a", Scheme.mono .integer)]
      (variable_ "a") .integer .empty := by
    have h := HasType.var (m := Unit) (lvl := 2)
      (Γ := [("w2", Scheme.mono (.var 1 0)), ("a", Scheme.mono .integer)])
      (x := "a") (s := Scheme.mono .integer) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hbody : HasType (m := Unit) 1 [("a", Scheme.mono .integer)]
      (lambda "w2" (variable_ "a")) (.fun (.var 1 0) .empty .integer) .empty :=
    HasType.lam (lvl' := 2) (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) ha
  exact HasTypeV.closure (lvl' := 1) (argTy := .integer) (εb := .empty)
    (retTy := .fun (.var 1 0) .empty .integer) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels] at hl; exact (List.not_mem_nil hl).elim)
    hbody (.refl _)

/-- R3's closure `retTy` (post-instantiation) carries level 1, NOT `< 1` — the universal-closing
lemma's `hretTy` premise fails at this closure. -/
theorem r3_retTy_not_below_sublevel :
    ¬ (∀ l ∈ (Ty.fun (.var 1 0) .empty (Ty.integer)).levels, l < 1) := by decide

-- R4: readiness for the escaping closure at a HIGH arg (`[.var 5 0]`) — establishable by re-typing
-- the body at a fresh sublevel 6 dominating both the arg (5) and the fixed escaping level (1).
theorem r4_escaping_closure_ready_high_arg : HasTypeV (m := Unit)
    (.Closure "a" (lambda "w2" (variable_ "a")) [])
    ((Scheme.genAtV 0 (.fun (.var 0 0) .empty (.fun (.var 1 0) .empty (.var 0 0)))).instantiateV
      [.var 5 0]) := by
  have hinst : (Scheme.genAtV 0 (.fun (.var 0 0) .empty (.fun (.var 1 0) .empty (.var 0 0)))).instantiateV
      [.var 5 0] = .fun (.var 5 0) .empty (.fun (.var 1 0) .empty (.var 5 0)) := by decide
  rw [hinst]
  have ha : HasType (m := Unit) 7
      [("w2", Scheme.mono (.var 1 0)), ("a", Scheme.mono (.var 5 0))]
      (variable_ "a") (.var 5 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 7)
      (Γ := [("w2", Scheme.mono (.var 1 0)), ("a", Scheme.mono (.var 5 0))])
      (x := "a") (s := Scheme.mono (.var 5 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hbody : HasType (m := Unit) 6 [("a", Scheme.mono (.var 5 0))]
      (lambda "w2" (variable_ "a")) (.fun (.var 1 0) .empty (.var 5 0)) .empty :=
    HasType.lam (lvl' := 7) (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) ha
  exact HasTypeV.closure (lvl' := 6) (argTy := .var 5 0) (εb := .empty)
    (retTy := .fun (.var 1 0) .empty (.var 5 0)) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody (.refl _)

/-! ## W2 — the genuine INTERLEAVING wall witness (2026-07-10)

The W1 note flagged the interleaving residual "not yet constructed as a genuine blocked case." W2
constructs it: the **natural interleaving ENTRY derivation** of V8's closure body
`let g = \y.y in \w. g x`, with `g` generalized at its LOW natural ambient `3` and the `\w` binder
chosen AT that same level `3` — so `retTy = .var 3 0 → .var 2 0` carries level `3` `=` the closure
sublevel `3` (`interleave_retTy_not_below_sublevel`). This is a *valid, well-typed* derivation
(`interleave_body`, `interleave_closure`) — and per finding (9) the entry to `soundness` is
*arbitrary*, so this interleaving derivation is an admissible entry.

At this derivation:
- the **universal-closing lemma** (`genAtV_instantiate_lam_ready_universal`) does **not** apply: its
  `∀ l ∈ retTy.levels, l < lvl'` premise fails (level 3 ⊀ sublevel 3);
- the **raise route** cannot transport it to a covered form: to move `g`'s gen level 3 the raise
  threshold `t ≤ 3` also moves `retTy`'s binder level 3, changing the advertised type; any `t > 3`
  strands `g` at 3 where the instantiation still collides (`v8_moving_g_moves_retTy` /
  `v8_fixing_retTy_strands_g` — the same arithmetic, now anchored to a *constructed* entry).

Yet readiness is **semantically true**: the SAME closure value is typeable with `g` re-generalized
fresh at 5 (`v8`), where `retTy {3,2} < 5` is disciplined. The two derivations genuinely differ; the
substitution/raise keystone (`genAtV_closure_ready_value_node`, `Substitution.lean:168`, still on the
`l = 0 ∨ l = lvl` args bound) transports the stored one and cannot reach the fresh one.

**Verdict.** The interleaving residual is REAL and reachable as an arbitrary entry derivation. The
current substitution/raise keystone cannot discharge its readiness. Unconditional route B therefore
needs **either** a re-derivation (structural-relabel) keystone — the G16 type-fixed relabel, which
`v8_moving_g_moves_retTy`/`v8_fixing_retTy_strands_g` show no threshold raise provides — **or** the
entry-premise restriction (`ArgsDisc`, §2/§4) / decoupled-`let_poly` rule (finding 5,
`G2DecoupledSpike.lean`), a judgment change needing Phase-0 sign-off. -/

-- W2: the natural interleaving entry derivation (g generalized at low ambient 3; \w binder at 3).
theorem w2_interleave_body : HasType (m := Unit) 3 [("x", Scheme.mono (.var 2 0))]
    (let_ "g" (lambda "y" (variable_ "y"))
      (lambda "w" (apply (variable_ "g") (variable_ "x"))))
    (.fun (.var 3 0) .empty (.var 2 0)) .empty := by
  have hgy : HasType (m := Unit) 4
      [("y", Scheme.mono (.var 3 0)), ("x", Scheme.mono (.var 2 0))]
      (variable_ "y") (.var 3 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 4)
      (Γ := [("y", Scheme.mono (.var 3 0)), ("x", Scheme.mono (.var 2 0))])
      (x := "y") (s := Scheme.mono (.var 3 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hg : HasType (m := Unit) 5
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
       ("x", Scheme.mono (.var 2 0))]
      (variable_ "g") (.fun (.var 2 0) .empty (.var 2 0)) .empty := by
    have hginst : (Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))).instantiateV [.var 2 0]
        = .fun (.var 2 0) .empty (.var 2 0) := by decide
    have h := HasType.var (m := Unit) (lvl := 5)
      (Γ := [("w", Scheme.mono (.var 3 0)),
             ("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
             ("x", Scheme.mono (.var 2 0))])
      (x := "g") (s := Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0)))
      (args := [.var 2 0]) (ε := .empty) (a := ()) (by decide)
    rwa [hginst] at h
  have hx : HasType (m := Unit) 5
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
       ("x", Scheme.mono (.var 2 0))]
      (variable_ "x") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 5)
      (Γ := [("w", Scheme.mono (.var 3 0)),
             ("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
             ("x", Scheme.mono (.var 2 0))])
      (x := "x") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty)
      (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hgx : HasType (m := Unit) 5
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
       ("x", Scheme.mono (.var 2 0))]
      (apply (variable_ "g") (variable_ "x")) (.var 2 0) .empty :=
    HasType.app hg (Ty.effWeaken_refl _) hx
  have hlamw : HasType (m := Unit) 4
      [("g", Scheme.genAtV 3 (.fun (.var 3 0) .empty (.var 3 0))),
       ("x", Scheme.mono (.var 2 0))]
      (lambda "w" (apply (variable_ "g") (variable_ "x")))
      (.fun (.var 3 0) .empty (.var 2 0)) .empty :=
    HasType.lam (lvl' := 5) (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hgx
  exact HasType.let_poly (by omega)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hgy
    (by intro b hb l hl
        rcases List.mem_singleton.mp hb with rfl
        simp only [Scheme.mono, Ty.levels, List.mem_singleton] at hl; omega)
    hlamw

/-- W2's `retTy` carries level 3 `=` the closure sublevel 3, NOT `< 3` — the universal-closing
lemma's `hretTy` premise fails on this valid, arbitrary-entry interleaving derivation. -/
theorem w2_interleave_retTy_not_below_sublevel :
    ¬ (∀ l ∈ (Ty.fun (.var 3 0) .empty (.var 2 0)).levels, l < 3) := by decide

/-- The closure VALUE built from the interleaving body type-checks (sublevel 3). -/
theorem w2_interleave_closure : HasTypeV (m := Unit)
    (.Closure "x"
      (let_ "g" (lambda "y" (variable_ "y"))
        (lambda "w" (apply (variable_ "g") (variable_ "x")))) [])
    (.fun (.var 2 0) .empty (.fun (.var 3 0) .empty (.var 2 0))) :=
  HasTypeV.closure (lvl' := 3) (argTy := .var 2 0) (εb := .empty)
    (retTy := .fun (.var 3 0) .empty (.var 2 0)) (by omega) EnvWf.nil
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    w2_interleave_body (.refl _)

end Eyg.Types.G2Validation
