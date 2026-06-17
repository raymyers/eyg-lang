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

end Eyg.Semantics
