import Eyg.Types.Runtime
import Eyg.Types.EffRow
import Eyg.Semantics.Reduction

/-!
# Continuation & machine-state typing (Milestone T3c-i)

The continuation half of the runtime-typing layer. Following
`references/abstract-machine-type-soundness.md` §2, a continuation stack is typed
as an **answer-type transformer**: `StackWf k τin ε τout` means "feeding a value
of type `τin` (under ambient effect row `ε`) into the stack `k` ultimately yields
an answer of type `τout`". The empty stack is the identity transformer
(`τin = τout`); each frame composes one more transformation.

`MStateWf s τout ε` then types a whole machine state by splitting it into "the
control produces some intermediate `τin`" and "the stack `k` takes `τin` to the
final `τout`". These are the signatures `preservation`/`progress` are stated over
(T3c-ii/iii); they are **fixed once** here (plan rule 1) — later slices add
*frames*/cases, never re-type them.

## Frames in the pure core

`Trace` (pass-through), `Assign` (the `let` continuation — run the body under the
bound value), `Arg` (evaluate the argument, then apply), `Apply`/`CallWith` (apply
a known function value). The effect-delimiting `Delimit` frame and the `wait`
state join in T5; `MStateWf` pins `wait` to `False` for now (pure-core programs
never suspend), to be given real content when effects un-pin the row.
-/

namespace Eyg.Types

open Eyg.Interpreter
open Eyg.Ir
open Eyg.Semantics

/-- A continuation stack as an answer-type transformer: feeding a `τin`-value
into `k` (ambient effect `ε`) yields a final `τout`. -/
inductive StackWf {m : Type} : Stack m → Ty → Ty → Ty → Prop where
  /-- The empty stack is the identity transformer. -/
  | nil {τ ε} : StackWf [] τ ε τ
  /-- `Trace` forwards its incoming value unchanged. -/
  | trace {a w rest τin ε τout} :
      StackWf rest τin ε τout →
      StackWf ((Kontinue.Trace w, a) :: rest) τin ε τout
  /-- `Assign` (the `let` continuation): the incoming value is the definition; the
  body is run in the captured env extended with it. -/
  | assign {a x body fenv Γ defnTy bodyTy ε τout rest lvl} :
      1 ≤ lvl →
      EnvWf fenv Γ →
      (hbody : HasType lvl ((x, .mono defnTy) :: Γ) body bodyTy ε) →
      HasTypeRT hbody →
      StackWf rest bodyTy ε τout →
      StackWf ((Kontinue.Assign x body fenv, a) :: rest) defnTy ε τout
  /-- `Arg`: the incoming value is the *function* `argTy →⟨εf⟩ retTy`; the stored
  argument node is evaluated next, then applied. The function's latent `εf` may be
  weakened to the ambient `ε` (`EffWeaken εf ε` — a pure function applied in an
  effectful ambient; exact match for T3–T5). -/
  | arg {a arg fenv Γ argTy εf retTy ε τout rest lvl} :
      1 ≤ lvl →
      EnvWf fenv Γ →
      (harg : HasType lvl Γ arg argTy ε) →
      HasTypeRT harg →
      Ty.EffWeaken εf ε →
      StackWf rest retTy ε τout →
      StackWf ((Kontinue.Arg arg fenv, a) :: rest) (.fun argTy εf retTy) ε τout
  /-- `Apply f`: the incoming value is the *argument* of type `argTy`; the stored
  function value `f` has type `argTy →⟨εf⟩ retTy`, latent `εf` weakenable to `ε`. -/
  | applyf {a f fenv argTy εf retTy ε τout rest} :
      HasTypeV f (.fun argTy εf retTy) →
      Ty.EffWeaken εf ε →
      StackWf rest retTy ε τout →
      StackWf ((Kontinue.Apply f fenv, a) :: rest) argTy ε τout
  /-- `CallWith arg`: the incoming value is the *function* `argTy →⟨εf⟩ retTy`; the
  stored value `arg` is its argument; latent `εf` weakenable to `ε`. -/
  | callwith {a arg fenv argTy εf retTy ε τout rest} :
      HasTypeV arg argTy →
      Ty.EffWeaken εf ε →
      StackWf rest retTy ε τout →
      StackWf ((Kontinue.CallWith arg fenv, a) :: rest) (.fun argTy εf retTy) ε τout
  /-- A deep `Delimit l handler henv` frame **discharges `l`**: the incoming value (the
  exec's normal result, type `ret`) arrives under the handled row `⟨l:(lift,reply)|tail⟩`,
  and everything below runs under the shrunk row `tail`. **No `EnvWf` premise** (the
  handler is a self-contained value; the frame env is arbitrary at `reduceDeep`). This is
  the one frame where the ambient row changes across the step. -/
  | delimit {a l handler henv lift reply tail ret ε τout rest} :
      HasTypeV handler (handlerTy lift reply tail ret) →
      Ty.EffWeaken tail ε →
      StackWf rest ret ε τout →
      StackWf ((Kontinue.Delimit l handler henv false, a) :: rest)
        ret (.effectExtend l lift reply tail) τout
  /-- **Conversion closure**: the input type and ambient row may be replaced by
  `TyEquiv`-equal ones. Needed so the reified `Resume` continuation (whose stored segment
  endpoints match the operation types only up to `TyEquiv`) plugs into the call-site
  stack. Mirrors the value-level `HasTypeV.conv` baked in at the leaves. -/
  | conv {k σ σ' ε ε' τout} :
      StackWf k σ ε τout → Ty.TyEquiv σ σ' → Ty.TyEquiv ε ε' →
      StackWf k σ' ε' τout

/-! ## Stack composition (keystone for `Resume`/`Handle`, T5d)

The reified `Resume` continuation re-pushes a captured **segment** `acc` (a `StackSegWf`,
which tracks per-endpoint rows — it may contain a row-discharging `Delimit`) onto the
call-site base stack `k` (a `StackWf`). `stackSeg_toStackWf` composes the two: the
segment's hole `(σmid, εmid)` is plugged by `k`. The old uniform-`ε` `stackWf_append`/
`stackWf_move` are gone — they assumed a single ambient row, incompatible with the
row-shrinking `Delimit`/`conv`. -/

/-- The interpreter's `move acc k` (re-push popped frames) is `acc.reverse ++ k`. -/
theorem move_eq {m : Type} (acc k : Stack m) : move acc k = acc.reverse ++ k := by
  induction acc generalizing k with
  | nil => rfl
  | cons hd rest ih => obtain ⟨s, mt⟩ := hd; simp [move, ih, List.reverse_cons]

/-- **Segment → stack composition.** A segment `seg` typed `(σin,εin) ⇒ (σmid,εmid)`
followed by a base stack `k` typed `(σmid,εmid) ⇒ τ` yields `StackWf (seg ++ k) σin εin
τ`: each segment frame becomes the matching `StackWf` frame (the `delimit` frame becomes
`StackWf.delimit`, where the ambient row shrinks). By `induction seg` + `cases hseg`. -/
theorem stackSeg_toStackWf {m : Type} {seg k : Stack m} {σin εin σmid εmid τ : Ty}
    (hseg : StackSegWf seg σin εin σmid εmid) (hk : StackWf k σmid εmid τ) :
    StackWf (seg ++ k) σin εin τ := by
  induction seg generalizing σin εin with
  | nil => cases hseg with | nil h1 h2 => exact StackWf.conv hk h1.symm h2.symm
  | cons hd rest ih =>
      obtain ⟨kont, ann⟩ := hd
      cases hseg with
      | trace h => exact .trace (ih h)
      | assign hlvl henv hbody hrt h => exact .assign hlvl henv hbody hrt (ih h)
      | arg hlvl henv harg hrt hw h => exact .arg hlvl henv harg hrt hw (ih h)
      | applyf hf hw h => exact .applyf hf hw (ih h)
      | callwith harg hw h => exact .callwith harg hw (ih h)
      | delimit hh he hweak h => exact StackWf.conv (.delimit hh hweak (ih h)) (.refl _) he.symm

/-- **Resume composition.** Feeding a reply into `move acc k` is well-typed: `acc.reverse`
(the captured delimited prefix, in original order) is a segment `(reply,εtop) ⇒
(ret,tail)`, composed onto the base stack `k` (`(ret,tail) ⇒ τ`). -/
theorem stackWf_resume {m : Type} {acc k : Stack m} {σin εin σmid εmid τ : Ty}
    (hseg : StackSegWf acc.reverse σin εin σmid εmid) (hk : StackWf k σmid εmid τ) :
    StackWf (move acc k) σin εin τ := by
  rw [move_eq]; exact stackSeg_toStackWf hseg hk

/-! ## Per-frame inversion lemmas (fold `conv`)

`cases hst` on a `StackWf` cannot recurse through the `conv` constructor (it wraps a
smaller `StackWf` on the *same* stack at a different `(σ,ε)`). The four preservation/
progress theorems therefore branch on the **frame** (`cases kont`) and use these
inversion lemmas, which fold `conv` via `TyEquiv.trans` (mirroring the `HasType`
generation lemmas `inv_app` etc. folding `HasType.conv`). Each is proved by `induction`
on the `StackWf` with the cons-stack generalized: the matching frame is `refl`, `conv`
composes, other frames/`nil` contradict the stack head. -/

theorem stackWf_trace_inv {m : Type} {w : Value m} {a : m} {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.Trace w, a) :: rest) σ ε τ) : StackWf rest σ ε τ := by
  generalize hs : ((Kontinue.Trace w, a) :: rest) = s at h
  induction h with
  | trace h' => cases hs; exact h'
  | conv h' hσ hε ih => exact .conv (ih hs) hσ hε
  | _ => simp at hs

theorem stackWf_assign_inv {m : Type} {x : String} {body : Tree.Node m} {fenv : Env m}
    {a : m} {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.Assign x body fenv, a) :: rest) σ ε τ) :
    ∃ Γ defnTy bodyTy ε0 lvl, 1 ≤ lvl ∧ Ty.TyEquiv σ defnTy ∧ Ty.TyEquiv ε ε0 ∧ EnvWf fenv Γ ∧
      ∃ hbody : HasType lvl ((x, .mono defnTy) :: Γ) body bodyTy ε0,
        HasTypeRT hbody ∧ StackWf rest bodyTy ε0 τ := by
  generalize hs : ((Kontinue.Assign x body fenv, a) :: rest) = s at h
  induction h with
  | assign hlvl henv hbody hrt hrest =>
      cases hs; exact ⟨_, _, _, _, _, hlvl, .refl _, .refl _, henv, hbody, hrt, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨Γ, dT, bT, ε0, lvl, hlvl, hσ', hε', henv, hbody, hrt, hrest⟩ := ih hs
      exact ⟨Γ, dT, bT, ε0, lvl, hlvl, hσ.symm.trans hσ', hε.symm.trans hε', henv, hbody, hrt, hrest⟩
  | _ => simp at hs

theorem stackWf_arg_inv {m : Type} {arg : Tree.Node m} {fenv : Env m} {a : m}
    {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.Arg arg fenv, a) :: rest) σ ε τ) :
    ∃ Γ argTy εf retTy ε0 lvl, 1 ≤ lvl ∧ Ty.TyEquiv σ (.fun argTy εf retTy) ∧ Ty.TyEquiv ε ε0 ∧
      EnvWf fenv Γ ∧ ∃ harg : HasType lvl Γ arg argTy ε0,
        HasTypeRT harg ∧ Ty.EffWeaken εf ε0 ∧ StackWf rest retTy ε0 τ := by
  generalize hs : ((Kontinue.Arg arg fenv, a) :: rest) = s at h
  induction h with
  | arg hlvl henv harg hrt hw hrest =>
      cases hs; exact ⟨_, _, _, _, _, _, hlvl, .refl _, .refl _, henv, harg, hrt, hw, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨Γ, aT, εf, rT, ε0, lvl, hlvl, hσ', hε', henv, harg, hrt, hw, hrest⟩ := ih hs
      exact ⟨Γ, aT, εf, rT, ε0, lvl, hlvl, hσ.symm.trans hσ', hε.symm.trans hε', henv, harg, hrt, hw,
        hrest⟩
  | _ => simp at hs

theorem stackWf_applyf_inv {m : Type} {f : Value m} {fenv : Env m} {a : m}
    {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.Apply f fenv, a) :: rest) σ ε τ) :
    ∃ argTy εf retTy ε0, Ty.TyEquiv σ argTy ∧ Ty.TyEquiv ε ε0 ∧
      HasTypeV f (.fun argTy εf retTy) ∧ Ty.EffWeaken εf ε0 ∧ StackWf rest retTy ε0 τ := by
  generalize hs : ((Kontinue.Apply f fenv, a) :: rest) = s at h
  induction h with
  | applyf hf hw hrest => cases hs; exact ⟨_, _, _, _, .refl _, .refl _, hf, hw, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨aT, εf, rT, ε0, hσ', hε', hf, hw, hrest⟩ := ih hs
      exact ⟨aT, εf, rT, ε0, hσ.symm.trans hσ', hε.symm.trans hε', hf, hw, hrest⟩
  | _ => simp at hs

theorem stackWf_callwith_inv {m : Type} {arg : Value m} {fenv : Env m} {a : m}
    {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.CallWith arg fenv, a) :: rest) σ ε τ) :
    ∃ argTy εf retTy ε0, Ty.TyEquiv σ (.fun argTy εf retTy) ∧ Ty.TyEquiv ε ε0 ∧
      HasTypeV arg argTy ∧ Ty.EffWeaken εf ε0 ∧ StackWf rest retTy ε0 τ := by
  generalize hs : ((Kontinue.CallWith arg fenv, a) :: rest) = s at h
  induction h with
  | callwith harg hw hrest => cases hs; exact ⟨_, _, _, _, .refl _, .refl _, harg, hw, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨aT, εf, rT, ε0, hσ', hε', harg, hw, hrest⟩ := ih hs
      exact ⟨aT, εf, rT, ε0, hσ.symm.trans hσ', hε.symm.trans hε', harg, hw, hrest⟩
  | _ => simp at hs

/-- `Delimit` inversion. Only the deep (`shallow = false`) frame is typeable; the input
type is the handler's return `ret` and the input row is the handled `⟨l:(lift,reply)|tail⟩`,
while `rest` runs at some ambient `εInner` with `tail ⊑ εInner` (the handle's discharged row
is weakenable to the continuation's ambient — `εInner = tail` in the exact case). -/
theorem stackWf_delimit_inv {m : Type} {l : String} {handler : Value m} {henv : Env m}
    {shallow : Bool} {a : m} {rest : Stack m} {σ ε τ : Ty}
    (h : StackWf ((Kontinue.Delimit l handler henv shallow, a) :: rest) σ ε τ) :
    ∃ lift reply tail ret εInner, shallow = false ∧ Ty.TyEquiv σ ret ∧
      Ty.TyEquiv ε (.effectExtend l lift reply tail) ∧ Ty.EffWeaken tail εInner ∧
      HasTypeV handler (handlerTy lift reply tail ret) ∧ StackWf rest ret εInner τ := by
  generalize hs : ((Kontinue.Delimit l handler henv shallow, a) :: rest) = s at h
  induction h with
  | delimit hh hw hrest => cases hs; exact ⟨_, _, _, _, _, rfl, .refl _, .refl _, hw, hh, hrest⟩
  | conv _ hσ hε ih =>
      obtain ⟨li, r, t, re, ei, hsh, hσ', hε', hweff, hh, hrest⟩ := ih hs
      exact ⟨li, r, t, re, ei, hsh, hσ.symm.trans hσ', hε.symm.trans hε', hweff, hh, hrest⟩
  | _ => simp at hs

/-- The empty-stack (identity) inversion, folding `conv`: `StackWf [] σ ε τ` forces the
input type to equal the answer (up to `TyEquiv`). -/
theorem stackWf_nil_inv {m : Type} {σ ε τ : Ty} (h : StackWf ([] : Stack m) σ ε τ) :
    Ty.TyEquiv σ τ := by
  generalize hs : ([] : Stack m) = s at h
  induction h with
  | nil => exact .refl _
  | conv _ hσ hε ih => exact hσ.symm.trans (ih hs)
  | _ => simp at hs

/-! ## Value-aware stack typing for `let_poly` (T6)

The polymorphic `let`'s Assign frame binds the value at a **scheme** `genAt n defnTy`, so the Assign-pop
must know the incoming value is **ready** — `∀ args, HasTypeV v (sc.instantiate args)` — which is *not*
derivable from the value's monotype (it is the false-for-generic-`v` value-substitution property). So the
readiness is carried in a value-aware stack predicate. `StackWfV v k` (the value flowing in is `v`) is
value-aware at the `Assign` head; `StackWfE e env k` (the control `e` will become a value) carries the
*future* closure's readiness across the lambda→closure step. See
`progress/2026-06-18-T6-let_poly-stackwfV-stackwfE-design.md`. -/

/-- Value-aware stack typing: the value `v` flows into stack `k`. At an `Assign` head it carries the
binding **readiness** about `v`; `Trace` passes `v` through; every other head consumes `v` (plain
`StackWf`). -/
def StackWfV {m : Type} (v : Value m) : Stack m → Ty → Ty → Ty → Prop
  | (Kontinue.Trace _, _) :: rest, σ, ε, τ => StackWfV v rest σ ε τ
  | (Kontinue.Assign x body fenv, _) :: rest, σ, ε, τ =>
      ∃ Γ sc defnTy bodyTy lvl, 1 ≤ lvl ∧ Ty.TyEquiv σ defnTy ∧
        (∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = sc.level) →
            HasTypeV v (sc.instantiateV args)) ∧
        EnvWf fenv Γ ∧ ∃ hbody : HasType lvl ((x, sc) :: Γ) body bodyTy ε,
          HasTypeRT hbody ∧ StackWf rest bodyTy ε τ
  | k, σ, ε, τ => StackWf k σ ε τ

/-- Control-aware stack typing for an `.E` state: the control `e` (in env `env`) will become a value. At
an `Assign` head it carries (1) the **future closure's readiness** when `e` is a lambda, and (2) the
invariant that the binding is **either monomorphic at the input type** (`sc = .mono defnTy`) **or the
control is a lambda** (the poly case) — which rules out an arrow-typed builtin `Partial` flowing into a
poly binding (false readiness, but semantically impossible). `Trace` passes through; other heads are plain
`StackWf`. -/
def StackWfE {m : Type} (e : Tree.Node m) (env : Env m) : Stack m → Ty → Ty → Ty → Prop
  | (Kontinue.Trace _, _) :: rest, σ, ε, τ => StackWfE e env rest σ ε τ
  | (Kontinue.Assign x body fenv, _) :: rest, σ, ε, τ =>
      ∃ Γ sc defnTy bodyTy lvl, 1 ≤ lvl ∧ Ty.TyEquiv σ defnTy ∧ EnvWf fenv Γ ∧
        ∃ hbody : HasType lvl ((x, sc) :: Γ) body bodyTy ε,
        HasTypeRT hbody ∧ StackWf rest bodyTy ε τ ∧
        (∀ lx lbody la, e = ⟨.Lambda lx lbody, la⟩ →
          ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = sc.level) →
            HasTypeV (Value.Closure lx lbody env) (sc.instantiateV args)) ∧
        (sc = Scheme.mono defnTy ∨ ∃ lx lbody la, e = ⟨.Lambda lx lbody, la⟩)
  | k, σ, ε, τ => StackWf k σ ε τ

/-- **`StackWf` (only mono Assign frames) refines to `StackWfV`** for any value `v` of the input type.
Sound because plain `StackWf` Assign frames are **monomorphic** (poly Assign frames live only in the
transient `StackWfV`/`StackWfE` states — they are popped one step after creation, never persisting in a
plain stack), so the binding readiness `∀args, HasTypeV v ((.mono defnTy).instantiate args)` is the
trivial `HasTypeV v defnTy`. This is what re-greens the frame/effect cases of `preservation_V`/`progress`,
which produce values on reorganized stacks. -/
theorem stackWf_toStackWfV {m : Type} {v : Value m} {k : Stack m} {σ ε τ : Ty}
    (h : StackWf k σ ε τ) (hv : HasTypeV v σ) : StackWfV v k σ ε τ := by
  induction k with
  | nil => exact h
  | cons hd rest ih =>
      obtain ⟨kont, ann⟩ := hd
      cases kont with
      | Trace w => exact ih (stackWf_trace_inv h)
      | Assign x body fenv =>
          obtain ⟨Γ, defnTy, bodyTy, ε0, lvl, hlvl, hσ, hε, henv, hbody, hrt, hrest⟩ :=
            stackWf_assign_inv h
          exact ⟨Γ, .mono defnTy, defnTy, bodyTy, lvl, hlvl, hσ,
            fun args _ => by rw [Scheme.instantiateV_mono]; exact hv.conv hσ, henv,
            HasType.conv hbody (.refl _) hε.symm, hrt.conv (.refl _) hε.symm,
            StackWf.conv hrest (.refl _) hε.symm⟩
      | Arg _ _ => exact h
      | Apply _ _ => exact h
      | CallWith _ _ => exact h
      | Delimit _ _ _ _ => exact h

/-- **`StackWf` (mono Assign frames) refines to `StackWfE`** for a control `e`, given the closure typing
when `e` is a lambda (`hclo`). The dual of `stackWf_toStackWfV` for `.E` states. -/
theorem stackWf_toStackWfE {m : Type} {e : Tree.Node m} {env : Env m} {k : Stack m} {σ ε τ : Ty}
    (h : StackWf k σ ε τ)
    (hclo : ∀ lx lb la, e = ⟨.Lambda lx lb, la⟩ → HasTypeV (Value.Closure lx lb env) σ) :
    StackWfE e env k σ ε τ := by
  induction k with
  | nil => exact h
  | cons hd rest ih =>
      obtain ⟨kont, ann⟩ := hd
      cases kont with
      | Trace w => exact ih (stackWf_trace_inv h)
      | Assign x body fenv =>
          obtain ⟨Γ, defnTy, bodyTy, ε0, lvl, hlvl, hσ, hε, henv, hbody, hrt, hrest⟩ :=
            stackWf_assign_inv h
          refine ⟨Γ, .mono defnTy, defnTy, bodyTy, lvl, hlvl, hσ, henv,
            HasType.conv hbody (.refl _) hε.symm, hrt.conv (.refl _) hε.symm,
            StackWf.conv hrest (.refl _) hε.symm, ?_, Or.inl rfl⟩
          intro lx lb la hlam args _
          rw [Scheme.instantiateV_mono]
          exact (hclo lx lb la hlam).conv hσ
      | Arg _ _ => exact h
      | Apply _ _ => exact h
      | CallWith _ _ => exact h
      | Delimit _ _ _ _ => exact h

/-- Forget the control-awareness: a `StackWfE` (for a **non-lambda** control, so any Assign head is
monomorphic) is a `StackWf`. -/
theorem stackWfE_toStackWf {m : Type} {e : Tree.Node m} {env : Env m}
    (hne : ∀ lx lbody la, e ≠ ⟨.Lambda lx lbody, la⟩) :
    ∀ {k : Stack m} {σ ε τ : Ty}, StackWfE e env k σ ε τ → StackWf k σ ε τ
  | [], _, _, _, h => h
  | (Kontinue.Trace _, _) :: rest, _, _, _, h => StackWf.trace (stackWfE_toStackWf hne h)
  | (Kontinue.Assign _ _ _, _) :: _, _, _, _, h => by
      obtain ⟨Γ, sc, defnTy, bodyTy, lvl, hlvl, hσ, henv, hbody, hrt, hrest, _, hmono⟩ := h
      rcases hmono with rfl | ⟨lx, lb, la, he⟩
      · exact StackWf.conv (StackWf.assign hlvl henv hbody hrt hrest) hσ.symm (.refl _)
      · exact absurd he (hne lx lb la)
  | (Kontinue.Arg _ _, _) :: _, _, _, _, h => h
  | (Kontinue.Apply _ _, _) :: _, _, _, _, h => h
  | (Kontinue.CallWith _ _, _) :: _, _, _, _, h => h
  | (Kontinue.Delimit _ _ _ _, _) :: _, _, _, _, h => h
  termination_by k => k.length

/-- **The lambda→closure transition.** When the control is a lambda, the `StackWfE`'s carried closure
readiness becomes the `StackWfV` readiness for the produced closure. -/
theorem stackWfE_lambda_step {m : Type} {lx : String} {lbody : Tree.Node m} {la : m} {env : Env m}
    {k : Stack m} {σ ε τ : Ty} (h : StackWfE ⟨.Lambda lx lbody, la⟩ env k σ ε τ) :
    StackWfV (Value.Closure lx lbody env) k σ ε τ := by
  induction k with
  | nil => exact h
  | cons hd rest ih =>
      obtain ⟨kont, ann⟩ := hd
      cases kont with
      | Trace w => exact ih h
      | Assign x body fenv =>
          obtain ⟨Γ, sc, defnTy, bodyTy, lvl, hlvl, hσ, henv, hbody, hrt, hrest, hclo, _⟩ := h
          exact ⟨Γ, sc, defnTy, bodyTy, lvl, hlvl, hσ, hclo lx lbody la rfl, henv, hbody, hrt,
            hrest⟩
      | Arg _ _ => exact h
      | Apply _ _ => exact h
      | CallWith _ _ => exact h
      | Delimit _ _ _ _ => exact h

/-- **A non-lambda value transition.** When the control is *not* a lambda, the `StackWfE` Assign head is
forced monomorphic (the `sc = .mono defnTy ∨ control-is-λ` clause), so the produced value `v` (of the
input type) discharges the trivial readiness. -/
theorem stackWfE_value_step {m : Type} {e : Tree.Node m} {env : Env m} {v : Value m}
    {k : Stack m} {σ ε τ : Ty} (h : StackWfE e env k σ ε τ) (hv : HasTypeV v σ)
    (hne : ∀ lx lbody la, e ≠ ⟨.Lambda lx lbody, la⟩) : StackWfV v k σ ε τ := by
  induction k with
  | nil => exact h
  | cons hd rest ih =>
      obtain ⟨kont, ann⟩ := hd
      cases kont with
      | Trace w => exact ih h
      | Assign x body fenv =>
          obtain ⟨Γ, sc, defnTy, bodyTy, lvl, hlvl, hσ, henv, hbody, hrt, hrest, _, hmono⟩ := h
          rcases hmono with hsc | ⟨lx, lbody, la, he⟩
          · subst hsc
            exact ⟨Γ, .mono defnTy, defnTy, bodyTy, lvl, hlvl, hσ,
              fun args _ => by rw [Scheme.instantiateV_mono]; exact hv.conv hσ, henv, hbody, hrt,
                hrest⟩
          · exact absurd he (hne lx lbody la)
      | Arg _ _ => exact h
      | Apply _ _ => exact h
      | CallWith _ _ => exact h
      | Delimit _ _ _ _ => exact h

/-- A machine state is well-typed at answer type `τ` and effect row `ε`: the
control yields an intermediate `τin` that the stack carries to `τ`. A `wait op env
k` state (suspended performing `op`, awaiting a reply) is typed by **effect safety**
(T5): `op` is a member of the ambient row `ε` (carrying lift `a`, reply `b`), and
the stack `k` carries a reply of type `b` (up to `TyEquiv`, since the stack's
expected input need only be equivalent to the declared reply type) to the answer
`τ`. The reply value itself is supplied by the world — typed by the reply contract,
discharged in `preservation`'s `reply` case. -/
def MStateWf {m : Type} : MState m → Ty → Ty → Prop
  | .run (.E e, env, k), τ, ε =>
      ∃ Γ τin lvl, 1 ≤ lvl ∧ EnvWf env Γ ∧ ∃ hty : HasType lvl Γ e τin ε,
        HasTypeRT hty ∧ StackWfE e env k τin ε τ
  | .run (.V v, _, k), τ, ε => ∃ τin, HasTypeV v τin ∧ StackWfV v k τin ε τ
  | .wait op _ k, τ, ε =>
      ∃ a b replyTy, Ty.EffContains ε op a b ∧ Ty.TyEquiv b replyTy ∧ StackWf k replyTy ε τ

/-! ## A well-typed program yields a well-typed initial state

`MStateWf (run (Config.initial prog)) τ ε` reduces to `HasType [] prog τ ε` **plus** the
runtime-restriction `HasTypeRT h`: the empty env realizes the empty context and the empty
stack is the identity transformer. The `HasTypeRT h` premise is the runtime-groundness
invariant at the entry point; it holds for closed programs of ground result type (every
reachable-as-control var node then instantiates at ground/ambient-level args) and is
threaded forward by preservation. This is the entry point the soundness theorem (T3c-iii)
starts from. -/

theorem mStateWf_initial {m : Type} {lvl : Nat} {prog : Tree.Node m} {τ ε : Ty}
    (hlvl : 1 ≤ lvl) (h : HasType lvl [] prog τ ε) (hrt : HasTypeRT h) :
    MStateWf (.run (Config.initial prog)) τ ε :=
  ⟨[], τ, lvl, hlvl, EnvWf.nil, h, hrt, StackWf.nil⟩

/-! ## Sanity checks -/

section
open Eyg.Ir.Tree

-- The initial state for `(\x. x) 1` is well-typed at `integer ! empty` and its control
-- derivation is `HasTypeRT` (all args are ground: the closure body's `x` is `.mono`, the
-- literal is a leaf).
example : MStateWf (.run (Config.initial
    (apply (lambda "x" (variable_ "x")) (integer 1)))) .integer .empty := by
  have hlam : HasType (m := Unit) 1 [] (lambda "x" (variable_ "x"))
      (.fun .integer .empty .integer) .empty :=
    HasType.lam (lvl' := 1) (le_refl _)
      (by intro l hl; simp only [Ty.levels] at hl; exact absurd hl (by simp))
      (HasType.var (s := .mono .integer) (args := []) rfl)
  have happ : HasType (m := Unit) 1 []
      (apply (lambda "x" (variable_ "x")) (integer 1)) .integer .empty :=
    HasType.app (argTy := .integer) hlam (Ty.effWeaken_refl _) HasType.int
  exact mStateWf_initial (le_refl 1) happ
    (HasTypeRT.app (hw := Ty.effWeaken_refl _) (hasTypeRT_lambda hlam) HasTypeRT.int)

-- A non-empty stack: applying the argument frame to a function value flows
-- `integer → integer` to a final `integer`.
example : StackWf [(Kontinue.Apply (.Closure "x" (variable_ "x") []) ([] : Env Unit), ())]
    .integer .empty .integer :=
  StackWf.applyf
    (HasTypeV.closure (lvl' := 1) (le_refl 1) EnvWf.nil
      (by intro l hl; simp only [Ty.levels] at hl; exact absurd hl (by simp))
      (HasType.var (s := .mono .integer) (args := []) rfl)
      (Ty.TyEquiv.refl _))
    (Ty.effWeaken_refl _)
    StackWf.nil

end

end Eyg.Types
