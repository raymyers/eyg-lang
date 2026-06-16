import Eyg.Semantics.Correspondence

/-!
# Observable behaviour: traces & divergence (Milestone S4)

A program's observable behaviour is either

* **termination** — a finite trace of effect events ending in an `Outcome`
  (`value`/`crash`), reached by `eygLTS.MTr`; or
* **divergence** — an infinite run, captured by cslib's `ωTr` over an
  `ωSequence` of labels. Unlike a big-step semantics, this can express "a server
  loops on `!fix` performing effects forever" (difference-doc §divergence).

The headline results:

* `outcome_unique` — the (silent) terminal outcome of a config is determined
  (a corollary of S3: `eval_iff_mtr` + `eval_mono`).
* `tauDiverges_iff_timeout` — internal (τ-only) divergence is exactly "`eval`
  times out at every fuel", tying the LTS notion to the FBS one.
-/

namespace Eyg.Semantics

open Eyg.Interpreter
open Eyg.Ir
open Cslib

/-- A possible observable behaviour of a configuration. -/
inductive Behavior (m : Type) where
  /-- Terminates with a finite `trace` at `outcome`. -/
  | terminates (trace : List (Label m)) (outcome : Outcome m)
  /-- Diverges, emitting the infinite `trace`. -/
  | diverges (trace : ωSequence (Label m))

/-- The behaviours a configuration exhibits. -/
def Behaviors {m : Type} [BEq m] (cfg : Config m) : Set (Behavior m) :=
  fun b => match b with
  | .terminates trace o => ∃ s', eygLTS.MTr (.run cfg) trace s' ∧ s'.outcome? = some o
  | .diverges μs => ∃ ss, eygLTS.ωTr ss μs ∧ ss 0 = .run cfg

/-! ## Finite-behaviour determinacy

The terminal outcome reached by a *silent* (τ-only) run is unique: the machine
is deterministic, so `eval` pins it. -/

/-- The silent terminal outcome of a configuration is determined. -/
theorem outcome_unique {m : Type} [BEq m] {cfg : Config m} {o1 o2 : Outcome m}
    (h1 : ∃ trace s', eygLTS.MTr (.run cfg) trace s' ∧
      (∀ μ ∈ trace, μ = Label.tau) ∧ s'.outcome? = some o1)
    (h2 : ∃ trace s', eygLTS.MTr (.run cfg) trace s' ∧
      (∀ μ ∈ trace, μ = Label.tau) ∧ s'.outcome? = some o2) :
    o1 = o2 := by
  obtain ⟨c, e, k⟩ := cfg
  obtain ⟨f1, hf1⟩ := (eval_iff_mtr c e k o1).mpr h1
  obtain ⟨f2, hf2⟩ := (eval_iff_mtr c e k o2).mpr h2
  have e1 : eval (max f1 f2) (c, e, k) = .done o1 :=
    eval_mono (le_max_left f1 f2) hf1 (by simp)
  have e2 : eval (max f1 f2) (c, e, k) = .done o2 :=
    eval_mono (le_max_right f1 f2) hf2 (by simp)
  rw [e1, Result.done.injEq] at e2
  exact e2

/-! ## Divergence ⟷ timeout

Internal (τ-only) divergence — the machine reduces forever without reaching a
value, a crash, or an effect — is exactly "`eval` times out at every fuel". This
is the EYG analogue of cslib's `LTS.Divergent`, and the place where the LTS says
something a big-step semantics cannot. -/

/-- Internal (τ-only) divergence: an infinite silent run from `cfg`. -/
def TauDiverges {m : Type} [BEq m] (cfg : Config m) : Prop :=
  (eygLTS (m := m)).Divergent (.run cfg)

/-- Forward direction: an infinite silent run makes `eval` time out at every
fuel (the machine never breaks). -/
theorem tauDiverges_imp_timeout {m : Type} [BEq m] :
    ∀ (fuel : Nat) (cfg : Config m), TauDiverges cfg → eval fuel cfg = .timeout := by
  intro fuel
  induction fuel with
  | zero => intro cfg _; rfl
  | succ n ih =>
      intro cfg hdiv
      obtain ⟨c, e, k⟩ := cfg
      obtain ⟨ss, μs, hω, hs0, htr⟩ := hdiv
      have h0 := hω 0
      rw [eygLTS_Tr, hs0, htr 0] at h0
      generalize hsucc : ss 1 = s1 at h0
      cases h0 with
      | tau hstep =>
          rename_i c' e' k'
          rw [eval_succ, hstep]
          apply ih (c', e', k')
          refine ⟨ss.tail, μs.tail, ?_, ?_, ?_⟩
          · intro i; exact hω (i + 1)
          · show ss 1 = MState.run (c', e', k'); rw [hsucc]
          · intro i; exact htr (i + 1)

/-- Total "loop successor": the next config if `step` reduces, else `cfg`
unchanged. Under always-`timeout`, the `else` branch never fires. -/
def loopSucc {m : Type} [BEq m] (cfg : Config m) : Config m :=
  match step cfg.1 cfg.2.1 cfg.2.2 with
  | .Loop c' e' k' => (c', e', k')
  | _ => cfg

/-- Under always-`timeout`, `step` loops and `loopSucc` is exactly its target. -/
theorem timeout_step_loop {m : Type} [BEq m] {cfg : Config m}
    (h : ∀ f, eval f cfg = .timeout) :
    step cfg.1 cfg.2.1 cfg.2.2 =
      .Loop (loopSucc cfg).1 (loopSucc cfg).2.1 (loopSucc cfg).2.2 := by
  obtain ⟨c, e, k⟩ := cfg
  cases hs : step c e k with
  | Loop c' e' k' => simp [loopSucc, hs]
  | Break res =>
      exfalso
      have hone : eval (0 + 1) (c, e, k) = .timeout := h 1
      rw [eval_succ, hs] at hone
      cases res with
      | ok v => simp at hone
      | error d => obtain ⟨r, _, _, _⟩ := d; cases r <;> simp at hone

/-- Always-`timeout` propagates to the loop successor. -/
theorem timeout_loopSucc {m : Type} [BEq m] {cfg : Config m}
    (h : ∀ f, eval f cfg = .timeout) : ∀ f, eval f (loopSucc cfg) = .timeout := by
  obtain ⟨c, e, k⟩ := cfg
  have hloop := timeout_step_loop h
  intro f
  have := h (f + 1)
  rw [eval_succ, hloop] at this
  exact this

/-- One silent step from a diverging config to its loop successor. -/
theorem step_loopSucc_tau {m : Type} [BEq m] {cfg : Config m}
    (h : ∀ f, eval f cfg = .timeout) :
    Step (.run cfg) Label.tau (.run (loopSucc cfg)) := by
  obtain ⟨c, e, k⟩ := cfg
  exact Step.tau (timeout_step_loop h)

/-- Backward direction: if `eval` times out at every fuel, the config has an
infinite silent run (it loops forever via `loopSucc`). -/
theorem timeout_imp_tauDiverges {m : Type} [BEq m] {cfg : Config m}
    (h : ∀ f, eval f cfg = .timeout) : TauDiverges cfg := by
  have hT : ∀ n, ∀ f, eval f (loopSucc^[n] cfg) = .timeout := by
    intro n
    induction n with
    | zero => exact h
    | succ k ihk => rw [Function.iterate_succ_apply']; exact timeout_loopSucc ihk
  refine ⟨(⟨fun n => MState.run (loopSucc^[n] cfg)⟩ : ωSequence (MState m)),
          ωSequence.const Label.tau, ?_, rfl, fun _ => rfl⟩
  intro i
  show eygLTS.Tr (.run (loopSucc^[i] cfg)) _ (.run (loopSucc^[i + 1] cfg))
  rw [eygLTS_Tr, Function.iterate_succ_apply']
  exact step_loopSucc_tau (hT i)

/-- **Divergence ⟷ timeout** (S4): internal divergence is exactly "`eval` times
out at every fuel". -/
theorem tauDiverges_iff_timeout {m : Type} [BEq m] {cfg : Config m} :
    TauDiverges cfg ↔ ∀ fuel, eval fuel cfg = .timeout :=
  ⟨fun hd fuel => tauDiverges_imp_timeout fuel cfg hd, timeout_imp_tauDiverges⟩

end Eyg.Semantics
