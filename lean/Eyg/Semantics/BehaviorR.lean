import Eyg.Semantics.Behavior
import Eyg.Semantics.Reduction

/-!
# Observable behaviour over the transparent `Reduce` (Milestone T0/T7)

`Behaviors` (S4) is built over `eygLTS`/`MState.outcome?`, which are defined over
the **opaque** `partial def step`. The type-soundness theorem (T7) cannot conclude
about those at the kernel level (the S5 wall). This module mirrors the S4
observable layer over the **transparent** `Reduce`/`reduce1Run`:

* `reduceLTS` — the `Cslib.LTS` whose transition relation is `Reduce`.
* `BehaviorsR` — the `MTr`-over-`Reduce` analogue of `Behaviors`, using the
  transparent terminal `MState.terminalR?`.
* `evalR_sound_done` / `evalR_done_mem_behaviorsR` — the tie-the-knot: a
  terminating `evalR` is realized as a terminating member of `BehaviorsR`. This is
  the Reduce analogue of S5's `eval_done_mem_behaviors`, and (unlike that one) is a
  genuine kernel result, because `reduce1Run` is transparent.

`BehaviorsR` is the object the headline soundness theorem (T7) concludes about; the
bridge to the shipped `Behaviors`/`eval` remains *executable only* (the `evalR ≈
eval` `#guard` battery), exactly as the plan's "kernel claim stays at the `Reduce`
level" prescribes.
-/

namespace Eyg.Semantics

open Eyg.Interpreter
open Eyg.Ir
open Cslib

/-- The EYG LTS over the **transparent** reduction relation `Reduce`. -/
def reduceLTS {m : Type} [BEq m] : LTS (MState m) (Label m) := ⟨Reduce⟩

@[simp] theorem reduceLTS_Tr {m : Type} [BEq m] {s μ s'} :
    (reduceLTS (m := m)).Tr s μ s' ↔ Reduce s μ s' := Iff.rfl

/-- `tau` is the internal label for the `Reduce` LTS too. -/
instance {m : Type} : HasTau (Label m) where
  τ := .tau

/-- The behaviours a configuration exhibits **over `Reduce`** — the transparent
analogue of `Behaviors`. -/
def BehaviorsR {m : Type} [BEq m] (cfg : Config m) : Set (Behavior m) :=
  fun b => match b with
  | .terminates trace o => ∃ s', reduceLTS.MTr (.run cfg) trace s' ∧ s'.terminalR? = some o
  | .suspended trace op lift => ∃ envP kP, reduceLTS.MTr (.run cfg) trace (.wait op envP kP) ∧
      Label.observable trace = [Label.perform op lift]
  | .diverges μs => ∃ ss, reduceLTS.ωTr ss μs ∧ ss 0 = .run cfg

/-! ## Tie-the-knot: `evalR` ⟶ `BehaviorsR` -/

/-- A terminating `evalR` is mirrored by a `Reduce`-`MTr` to a state with the same
terminal outcome. Fuel induction over the transparent `reduce1Run` — no opaque
`step`, so this is a kernel theorem. -/
theorem evalR_sound_done {m : Type} [BEq m] :
    ∀ (fuel : Nat) (cfg : Config m) (o : Outcome m), evalR fuel cfg = .done o →
      ∃ trace s', reduceLTS.MTr (.run cfg) trace s' ∧ s'.terminalR? = some o := by
  intro fuel
  induction fuel with
  | zero => intro cfg o h; simp [evalR] at h
  | succ n ih =>
      intro cfg o h
      rw [evalR_succ] at h
      cases hr : reduce1Run cfg with
      | tau cfg' =>
          rw [hr] at h
          obtain ⟨trace, s', hmtr, hout⟩ := ih cfg' o h
          exact ⟨.tau :: trace, s', LTS.MTr.stepL (Reduce.tau hr) hmtr, hout⟩
      | done o' =>
          rw [hr] at h; cases h
          exact ⟨[], .run cfg, LTS.MTr.refl, by simp [MState.terminalR?, hr]⟩
      | perform op lift envP kP => rw [hr] at h; simp [evalR] at h

/-- A terminating `evalR` is an observable terminating behaviour of `BehaviorsR`
(the Reduce-level analogue of S5's `eval_done_mem_behaviors`). -/
theorem evalR_done_mem_behaviorsR {m : Type} [BEq m] {cfg : Config m} {o : Outcome m}
    (h : ∃ fuel, evalR fuel cfg = .done o) :
    ∃ trace, Behavior.terminates trace o ∈ BehaviorsR cfg := by
  obtain ⟨fuel, hf⟩ := h
  obtain ⟨trace, s', hmtr, hout⟩ := evalR_sound_done fuel cfg o hf
  exact ⟨trace, s', hmtr, hout⟩

/-! ## The converse: a silent `BehaviorsR` termination comes from `evalR`

The Reduce analogue of S3's `eval_complete`: a `tau`-only `Reduce`-`MTr` to a terminal
state is realized by `evalR` at some fuel. This is the direction the soundness *of*
behaviours needs — it pulls a `BehaviorsR` membership back to an `evalR` result that the
typing soundness lemmas (`soundness_evalR_*`) constrain. -/

/-- Completeness (terminating, silent runs): a `tau`-only `Reduce`-multistep to a
terminal state is realized by `evalR` at some fuel. -/
theorem evalR_complete {m : Type} [BEq m] {o : Outcome m} :
    ∀ {s : MState m} {trace : List (Label m)} {s' : MState m},
      reduceLTS.MTr s trace s' → (∀ μ ∈ trace, μ = Label.tau) → s'.terminalR? = some o →
      ∀ cfg, s = .run cfg → ∃ fuel, evalR fuel cfg = .done o := by
  intro s trace s' hmtr
  induction hmtr with
  | refl =>
      intro _htau hterm cfg hs
      subst hs
      refine ⟨1, ?_⟩
      have hout : (MState.run cfg).terminalR? = some o := hterm
      simp only [MState.terminalR?] at hout
      cases hstep : reduce1Run cfg with
      | tau cfg' => rw [hstep] at hout; simp at hout
      | done o' => rw [evalR_succ, hstep]; rw [hstep] at hout; simp_all
      | perform op lift envP kP => rw [hstep] at hout; simp at hout
  | @stepL s1 μ s2 μs s3 htr _hmtr ih =>
      intro htau hterm cfg hs
      subst hs
      have hμ : μ = Label.tau := htau μ (by simp)
      subst hμ
      cases htr
      rename_i cfg' hstep
      have htau' : ∀ ν ∈ μs, ν = Label.tau := fun ν hν => htau ν (by simp [hν])
      obtain ⟨fuel, hfuel⟩ := ih htau' hterm cfg' rfl
      exact ⟨fuel + 1, by rw [evalR_succ, hstep]; exact hfuel⟩

end Eyg.Semantics
