import Eyg.Types.Typing

/-!
# G2 B1′ prototype — decoupled-generalization `let_poly` (spike, does not touch live `HasType`)

Validates the fix for the B1 block (`plan/progress/2026-07-10-G2-B1-blocked-ruleCoupling.md`): the
live `HasType.let_poly` generalizes at *exactly* its conclusion ambient (`genAtV lvl`), tying each
`let`'s gen level to its node's ambient — which is what makes V8's interleaving un-relabelable.

`HasTypeD` below is a minimal declarative typing whose `let_poly` generalizes at a **chosen** level
`gl`, **decoupled** from the ambient and required **fresh** w.r.t. the context (`gl` private to this
generalization). The payoff to demonstrate:

1. **Decoupling** — `HasTypeD` types V8's program with `g` generalized at a fresh `gl = 5` while
   `b`'s body ambient stays low (`2`). The coupled rule cannot (it ties the gen level to ambient).
2. (next) With `gl` private, no use-site instantiation arg ever equals `gl`, so the capture that
   blocked readiness never arises — readiness holds with no raise.
-/

namespace Eyg.Types.Decoupled

open Eyg.Ir Eyg.Ir.Tree

variable {m : Type}

/-- `gl` is fresh w.r.t. every binding of `Γ` (does not occur in any scheme body's levels). -/
def CtxFresh (gl : Nat) (Γ : Ctx) : Prop := ∀ b ∈ Γ, gl ∉ b.2.body.levels

/-- **Prototype declarative typing with decoupled generalization.** The only change from the live
`HasType` is `let_poly`: it generalizes at a **chosen fresh** level `gl` (private to the context),
decoupled from the ambient `lvl` (the body stays at `lvl`, not `lvl+1`). Minimal constructor set —
enough to type V8's program. -/
inductive HasTypeD : Nat → Ctx → Tree.Node m → Ty → Ty → Prop where
  | var {lvl Γ x s args ε a} (hl : Γ.lookup x = some s) :
      HasTypeD lvl Γ ⟨.Variable x, a⟩ (s.instantiateV args) ε
  | lam {lvl lvl' Γ x body argTy εb retTy ε a} (hle : lvl ≤ lvl')
      (hfv : ∀ l ∈ argTy.levels, l < lvl')
      (hbody : HasTypeD lvl' ((x, .mono argTy) :: Γ) body retTy εb) :
      HasTypeD lvl Γ ⟨.Lambda x body, a⟩ (.fun argTy εb retTy) ε
  | app {lvl Γ f arg argTy εf retTy ε a}
      (hf : HasTypeD lvl Γ f (.fun argTy εf retTy) ε) (hw : Ty.EffWeaken εf ε)
      (harg : HasTypeD lvl Γ arg argTy ε) :
      HasTypeD lvl Γ ⟨.Apply f arg, a⟩ retTy ε
  | let_poly {lvl gl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a}
      (hfresh : CtxFresh gl Γ) (hgl : ∀ l ∈ argTy.levels, l ≤ gl)
      (hfv : ∀ l ∈ argTy.levels, l < lvl')
      (hbodydefn : HasTypeD lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb)
      (hbody : HasTypeD lvl ((x, Scheme.genAtV gl (.fun argTy εb retTy)) :: Γ) body bodyTy ε) :
      HasTypeD lvl Γ ⟨.Let x ⟨.Lambda lx lbody, la⟩ body, a⟩ bodyTy ε
  | int {lvl Γ n ε a} : HasTypeD lvl Γ ⟨.Integer n, a⟩ .integer ε

/-- **Payoff 1 — decoupling.** V8's closure body types in `HasTypeD` with `g` generalized at a fresh
`gl = 5`, while `b`'s body ambient stays low at `2`. In the live coupled rule the gen level would be
*forced* to equal the ambient — the rigidity that blocks the V8 relabel. Here the two are free. -/
theorem v8_body_decoupled : HasTypeD (m := Unit) 2 [("x", Scheme.mono (.var 2 0))]
    (let_ "g" (lambda "y" (variable_ "y"))
      (lambda "w" (apply (variable_ "g") (variable_ "x"))))
    (.fun (.var 3 0) .empty (.var 2 0)) .empty := by
  have hgy : HasTypeD (m := Unit) 6
      [("y", Scheme.mono (.var 5 0)), ("x", Scheme.mono (.var 2 0))]
      (variable_ "y") (.var 5 0) .empty := by
    have h := HasTypeD.var (m := Unit) (lvl := 6)
      (Γ := [("y", Scheme.mono (.var 5 0)), ("x", Scheme.mono (.var 2 0))])
      (x := "y") (s := Scheme.mono (.var 5 0)) (args := ([] : List Ty)) (ε := .empty) (a := ())
      (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hg : HasTypeD (m := Unit) 4
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
       ("x", Scheme.mono (.var 2 0))]
      (variable_ "g") (.fun (.var 2 0) .empty (.var 2 0)) .empty := by
    have hginst :
        (Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))).instantiateV [.var 2 0]
        = .fun (.var 2 0) .empty (.var 2 0) := by decide
    have h := HasTypeD.var (m := Unit) (lvl := 4)
      (Γ := [("w", Scheme.mono (.var 3 0)),
             ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
             ("x", Scheme.mono (.var 2 0))])
      (x := "g") (s := Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0)))
      (args := [.var 2 0]) (ε := .empty) (a := ()) (by decide)
    rwa [hginst] at h
  have hx : HasTypeD (m := Unit) 4
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
       ("x", Scheme.mono (.var 2 0))]
      (variable_ "x") (.var 2 0) .empty := by
    have h := HasTypeD.var (m := Unit) (lvl := 4)
      (Γ := [("w", Scheme.mono (.var 3 0)),
             ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
             ("x", Scheme.mono (.var 2 0))])
      (x := "x") (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty) (a := ())
      (by decide)
    rwa [Scheme.instantiateV_mono] at h
  have hgx : HasTypeD (m := Unit) 4
      [("w", Scheme.mono (.var 3 0)),
       ("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
       ("x", Scheme.mono (.var 2 0))]
      (apply (variable_ "g") (variable_ "x")) (.var 2 0) .empty :=
    HasTypeD.app hg (Ty.effWeaken_refl _) hx
  have hlamw : HasTypeD (m := Unit) 2
      [("g", Scheme.genAtV 5 (.fun (.var 5 0) .empty (.var 5 0))),
       ("x", Scheme.mono (.var 2 0))]
      (lambda "w" (apply (variable_ "g") (variable_ "x")))
      (.fun (.var 3 0) .empty (.var 2 0)) .empty :=
    HasTypeD.lam (by omega)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega) hgx
  exact HasTypeD.let_poly
    (by intro b hb; rcases List.mem_singleton.mp hb with rfl; decide)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hgy hlamw

end Eyg.Types.Decoupled
