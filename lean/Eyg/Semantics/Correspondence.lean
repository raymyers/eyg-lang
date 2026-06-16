import Eyg.Semantics.Lts

/-!
# FBS ⟷ LTS correspondence (Milestone S3)

The fuel-indexed interpreter `eval` and the relational `eygLTS` describe the same
finite executions. Both are phrased over the *same* `step` function, so the
proofs never evaluate `step` on a concrete config — they case on `step c e k`
abstractly (see `progress/2026-06-16-partial-def-irreducibility.md`).

This file currently establishes **determinism**; soundness/completeness of `eval`
against `eygLTS.MTr` follow.
-/

namespace Eyg.Semantics

open Eyg.Interpreter
open Eyg.Ir
open Cslib

/-- `eygLTS` is deterministic: a state has at most one `μ`-derivative. Each
transition is pinned by the function `step` (for `tau`/`perform`) or by the
label's own value (for `reply`), so the target is unique. -/
instance instDeterministic {m : Type} [BEq m] : (eygLTS (m := m)).Deterministic where
  deterministic s μ s2 s3 h1 h2 := by
    cases h1 <;> cases h2 <;> simp_all

/-! ## Soundness: `eval` runs are LTS multisteps

A finished `eval` is mirrored by an `eygLTS.MTr` to a state with the same
outcome, and the *observable* trace (the non-`tau` labels) is exactly what was
emitted: nothing for a value/crash, `[perform op lift]` for an effect. -/

@[simp] theorem observable_tau_cons {m : Type} (trace : List (Label m)) :
    Label.observable (.tau :: trace) = Label.observable trace := by
  simp [Label.observable, Label.isObservable]

/-- Soundness, terminating case: if `eval` reaches a terminal outcome `o`, the
LTS multisteps (silently) to a terminal state carrying `o`. -/
theorem eval_sound_done {m : Type} [BEq m] :
    ∀ (fuel : Nat) (c : Control m) (e : Env m) (k : Stack m) (o : Outcome m),
      eval fuel (c, e, k) = .done o →
      ∃ trace s', eygLTS.MTr (.run (c, e, k)) trace s' ∧ s'.outcome? = some o ∧
        Label.observable trace = [] := by
  intro fuel
  induction fuel with
  | zero => intro c e k o h; simp [eval] at h
  | succ n ih =>
      intro c e k o h
      cases hs : step c e k with
      | Loop c' e' k' =>
          simp only [eval_succ, hs] at h
          obtain ⟨trace, s', hmtr, hout, hobs⟩ := ih c' e' k' o h
          exact ⟨.tau :: trace, s', LTS.MTr.stepL (Step.tau hs) hmtr, hout, by simp [hobs]⟩
      | Break res =>
          cases res with
          | ok v =>
              simp only [eval_succ, hs] at h
              injection h with h'
              exact ⟨[], .run (c, e, k), LTS.MTr.refl, by simp [MState.outcome?, hs, h'], rfl⟩
          | error d =>
              obtain ⟨reason, ann, envP, kP⟩ := d
              cases reason with
              | UnhandledEffect op lift => simp [eval_succ, hs] at h
              | _ =>
                  simp only [eval_succ, hs] at h
                  injection h with h'
                  exact ⟨[], .run (c, e, k), LTS.MTr.refl,
                    by simp [MState.outcome?, hs, h'], rfl⟩

/-- Soundness, effect case: if `eval` suspends at an unhandled effect, the LTS
multisteps to the matching `wait` state, with observable trace `[perform op
lift]` and the same resumption. -/
theorem eval_sound_effect {m : Type} [BEq m] :
    ∀ (fuel : Nat) (c : Control m) (e : Env m) (k : Stack m)
      (op : String) (lift : Value m) (resume : Value m → Config m),
      eval fuel (c, e, k) = .effect op lift resume →
      ∃ trace envP kP, eygLTS.MTr (.run (c, e, k)) trace (.wait op envP kP) ∧
        resume = (fun v => (.V v, envP, kP)) ∧
        Label.observable trace = [Label.perform op lift] := by
  intro fuel
  induction fuel with
  | zero => intro c e k op lift resume h; simp [eval] at h
  | succ n ih =>
      intro c e k op lift resume h
      cases hs : step c e k with
      | Loop c' e' k' =>
          simp only [eval_succ, hs] at h
          obtain ⟨trace, envP, kP, hmtr, hres, hobs⟩ := ih c' e' k' op lift resume h
          exact ⟨.tau :: trace, envP, kP, LTS.MTr.stepL (Step.tau hs) hmtr, hres, by simp [hobs]⟩
      | Break res =>
          cases res with
          | ok v => simp [eval_succ, hs] at h
          | error d =>
              obtain ⟨reason, ann, envP, kP⟩ := d
              cases reason with
              | UnhandledEffect op' lift' =>
                  simp only [eval_succ, hs] at h
                  injection h with ho hl hr
                  rw [ho, hl] at hs
                  exact ⟨[.perform op lift], envP, kP,
                    LTS.MTr.single eygLTS (Step.perform hs), hr.symm, by
                      simp [Label.observable, Label.isObservable]⟩
              | _ => simp [eval_succ, hs] at h

/-! ## Completeness: terminal LTS runs are reachable by `eval`

The converse of `eval_sound_done`, for the `tau`-only runs that bare `eval`
models (it suspends at the first effect, so effectful runs belong to `run`, not
`eval`). Every silent multistep to a terminal state is matched by some fuel. -/

/-- Completeness (terminating, silent runs): a `tau`-only multistep to a terminal
state is realized by `eval` at some fuel. -/
theorem eval_complete {m : Type} [BEq m] {o : Outcome m} :
    ∀ {s : MState m} {trace : List (Label m)} {s' : MState m},
      eygLTS.MTr s trace s' → (∀ μ ∈ trace, μ = Label.tau) → s'.outcome? = some o →
      ∀ c e k, s = .run (c, e, k) → ∃ fuel, eval fuel (c, e, k) = .done o := by
  intro s trace s' hmtr
  induction hmtr with
  | refl =>
      intro _htau hterm c e k hs
      subst hs
      refine ⟨1, ?_⟩
      have hout : (MState.run (c, e, k)).outcome? = some o := hterm
      simp only [MState.outcome?] at hout
      cases hstep : step c e k with
      | Loop c' e' k' => rw [hstep] at hout; simp at hout
      | Break res =>
          cases res with
          | ok v => rw [eval_succ, hstep]; rw [hstep] at hout; simp_all
          | error d =>
              obtain ⟨reason, ann, envP, kP⟩ := d
              cases reason with
              | UnhandledEffect op lift => rw [hstep] at hout; simp at hout
              | _ => rw [eval_succ, hstep]; rw [hstep] at hout; simp_all
  | @stepL s1 μ s2 μs s3 htr hmtr ih =>
      intro htau hterm c e k hs
      subst hs
      have hμ : μ = Label.tau := htau μ (by simp)
      subst hμ
      cases htr
      rename_i c' e' k' hstep
      have htau' : ∀ ν ∈ μs, ν = Label.tau := fun ν hν => htau ν (by simp [hν])
      obtain ⟨fuel, hfuel⟩ := ih htau' hterm c' e' k' rfl
      exact ⟨fuel + 1, by rw [eval_succ, hstep]; exact hfuel⟩

/-- An empty observable trace means every label was `tau`. -/
theorem observable_nil_tau {m : Type} {trace : List (Label m)}
    (h : Label.observable trace = []) : ∀ μ ∈ trace, μ = Label.tau := by
  intro μ hμ
  simp only [Label.observable, List.filter_eq_nil_iff] at h
  have := h μ hμ
  cases μ <;> simp_all [Label.isObservable]

/-- Characterisation (S3): `eval` reaches `done o` at some fuel **iff** the LTS
silently multisteps to a terminal state with outcome `o`. Combines
`eval_sound_done`, `eval_complete`, and (implicitly, via `instDeterministic`) the
uniqueness of that run. -/
theorem eval_iff_mtr {m : Type} [BEq m] (c : Control m) (e : Env m) (k : Stack m)
    (o : Outcome m) :
    (∃ fuel, eval fuel (c, e, k) = .done o) ↔
    (∃ trace s', eygLTS.MTr (.run (c, e, k)) trace s' ∧
      (∀ μ ∈ trace, μ = Label.tau) ∧ s'.outcome? = some o) := by
  constructor
  · rintro ⟨fuel, h⟩
    obtain ⟨trace, s', hmtr, hout, hobs⟩ := eval_sound_done fuel c e k o h
    exact ⟨trace, s', hmtr, observable_nil_tau hobs, hout⟩
  · rintro ⟨trace, s', hmtr, htau, hout⟩
    exact eval_complete hmtr htau hout c e k rfl

end Eyg.Semantics
