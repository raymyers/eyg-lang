import Eyg.Types.Typing
import Eyg.Types.TyEquivInv
import Eyg.Types.Row
import Eyg.Interpreter.State

/-!
# Runtime typing — values & environments (Milestone T3b)

Typing for *runtime* objects, the layer that lets preservation/progress talk
about machine states. Following `references/abstract-machine-type-soundness.md`
§3, an environment machine replaces the **substitution lemma** with an
**environment-typing + lookup lemma**: a closure is well-typed when its captured
environment realizes a context under which its body type-checks, and variable
lookup is sound against that.

This slice delivers the **value** half — `HasTypeV` (values), `EnvWf`
(environments, lock-step with `Ctx`), and `BuiltinPartialWf` (a partially-applied
builtin at its residual arrow) — plus the lookup lemma and the canonical-forms
lemmas. The **continuation** half (`StackWf` answer-type transformer) and
`MStateWf`, then `preservation`/`progress`/`soundness`, are the T3c sub-slice.

## Why a partially-applied builtin is typed *only at an arrow*

A resting `Partial (Builtin id) applied` is always **strictly under-applied** —
the machine reduces a saturated builtin immediately, never leaving it as a value.
So its type is always a residual *arrow* (`fun a ε r`). Baking that into
`HasTypeV.partialBuiltin` (the conclusion type is literally `.fun a ε r`) makes
the arrow canonical-forms lemma immediate and excludes the un-reachable
"saturated builtin sitting as a base-typed value". Preservation maintains it:
applying the last argument reduces rather than resting.
-/

namespace Eyg.Types

open Eyg.Interpreter
open Eyg.Ir

/-- A builtin partial `Partial (Builtin id) applied` is well-formed for `partialBuiltin`
typing only when it has a scheme **and** is **strictly under-applied** (`applied.length <
arity`). A saturated/over-applied builtin partial never rests (it reduces), so this is a true
runtime invariant; enforcing it rules out the fictional over-applied `fix` partials. Bundled
(scheme + arity bound) so destructuring `partialBuiltin` keeps a single hypothesis. -/
def PartialBuiltinWf {m : Type} (id : String) (s : Scheme) (applied : List (Interpreter.Value m)) :
    Prop :=
  Builtins.scheme id = some s ∧ ∃ n, Interpreter.Builtin.builtinArity id = some n ∧ applied.length < n

/-! Runtime typing for values, environments, and builtin partials (mutually
recursive: a `Closure` carries an `EnvWf`; an env binds `HasTypeV` values). Values
are pure — no effect row (a value *is* a result). -/
mutual

/-- A value has a type. Each constructor's conclusion is *any* type `TyEquiv`-equal
to the value's natural type — conversion is baked in at the leaves (rather than as
a separate recursive `convV` rule), so canonical forms are pure `cases` and the
typing-judgment's conversion is localized to values (keeping `StackWf`
conversion-free). -/
inductive HasTypeV {m : Type} : Value m → Ty → Prop where
  | int {n τ} : Ty.TyEquiv .integer τ → HasTypeV (.Integer n) τ
  | str {s τ} : Ty.TyEquiv .string τ → HasTypeV (.String s) τ
  | bin {b τ} : Ty.TyEquiv .binary τ → HasTypeV (.Binary b) τ
  /-- A closure inhabits (a type equivalent to) an arrow, provided its captured env realizes a context
  under which the **lambda node** type-checks level-natively (`HasType lvl`), at some ambient level
  `lvl` (existentially stored — the level is irrelevant to the value, only that the lambda types). This
  is the level-native replacement of the old magnitude closure premise: it exists for arbitrarily
  nested generalization (no `noLambdaLet`). -/
  | closure {lvl' x body env argTy εb retTy Γ τ} :
      1 ≤ lvl' →
      EnvWf env Γ →
      (∀ l ∈ argTy.levels, l < lvl') →
      HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb →
      Ty.TyEquiv (.fun argTy εb retTy) τ →
      HasTypeV (.Closure x body env) τ
  /-- A (strictly under-applied) builtin partial at (a type equivalent to) its
  residual arrow. The `PartialBuiltinWf` bundle enforces both the scheme lookup **and**
  strict under-application (`applied.length < arity`) — the latter rules out the fictional
  over-applied `fix` partials (whose arrow return type would otherwise let this rule type
  them), which is what makes `fix` preservation provable. -/
  | partialBuiltin {id s args applied a ε r τ} :
      PartialBuiltinWf id s applied →
      BuiltinPartialWf (s.instantiateV args) applied (.fun a ε r) →
      Ty.TyEquiv (.fun a ε r) τ →
      HasTypeV (.Partial (.Builtin id) applied) τ
  /-- The empty list inhabits any list type. -/
  | listNil {elem τ} : Ty.TyEquiv (.list elem) τ → HasTypeV (.LinkedList []) τ
  /-- A cons cell: head and tail share the element type. -/
  | listCons {hd tl elem τ} :
      HasTypeV hd elem → HasTypeV (.LinkedList tl) (.list elem) →
      Ty.TyEquiv (.list elem) τ → HasTypeV (.LinkedList (hd :: tl)) τ
  /-- The unsaturated `Cons` (no args): `α → List α → List α`. -/
  | partialConsNil {elem τ} :
      Ty.TyEquiv (.fun elem .empty (.fun (.list elem) .empty (.list elem))) τ →
      HasTypeV (.Partial .Cons []) τ
  /-- `Cons` applied to its head: `List α → List α`. -/
  | partialConsOne {hd elem τ} :
      HasTypeV hd elem → Ty.TyEquiv (.fun (.list elem) .empty (.list elem)) τ →
      HasTypeV (.Partial .Cons [hd]) τ
  /-- A tagged value inhabits a union row containing its label. -/
  | tagged {label v elem tail τ} :
      HasTypeV v elem → Ty.TyEquiv (.union (.rowExtend label elem tail)) τ →
      HasTypeV (.Tagged label v) τ
  /-- The unsaturated `Tag l`: `α → ⟨l : α | r⟩`. -/
  | partialTag {label elem tail τ} :
      Ty.TyEquiv (.fun elem .empty (.union (.rowExtend label elem tail))) τ →
      HasTypeV (.Partial (.Tag label) []) τ
  /-- The unsaturated `NoCases`: `⟨⟩ → β`. -/
  | partialNoCases {ret τ} :
      Ty.TyEquiv (.fun (.union .empty) .empty ret) τ →
      HasTypeV (.Partial .NoCases []) τ
  /-- `Case l` with no args: the full match scheme
  `(inner →⟨e⟩ r) → (⟨tail⟩ →⟨e⟩ r) → (⟨l:inner|tail⟩ →⟨e⟩ r)`. -/
  | partialMatchNil {label inner eff ret tail τ} :
      Ty.TyEquiv (.fun (.fun inner eff ret) .empty
        (.fun (.fun (.union tail) eff ret) .empty
          (.fun (.union (.rowExtend label inner tail)) eff ret))) τ →
      HasTypeV (.Partial (.Match label) []) τ
  /-- `Case l` with the branch applied. -/
  | partialMatchOne {label branch inner eff ret tail τ} :
      HasTypeV branch (.fun inner eff ret) →
      Ty.TyEquiv (.fun (.fun (.union tail) eff ret) .empty
        (.fun (.union (.rowExtend label inner tail)) eff ret)) τ →
      HasTypeV (.Partial (.Match label) [branch]) τ
  /-- `Case l` with both branches applied: `⟨l:inner|tail⟩ →⟨e⟩ r`. -/
  | partialMatchTwo {label branch otherwise inner eff ret tail τ} :
      HasTypeV branch (.fun inner eff ret) →
      HasTypeV otherwise (.fun (.union tail) eff ret) →
      Ty.TyEquiv (.fun (.union (.rowExtend label inner tail)) eff ret) τ →
      HasTypeV (.Partial (.Match label) [branch, otherwise]) τ
  /-- A record value realizes a row by **first-occurrence membership**, in two
  `∃`-free clauses (so it nests legally): every row label is *present*, and every
  present value *matches* the row's visible field type. Both read the first
  occurrence, so the interpreter's sorted-unique records match scoped-row types
  even with shadowed duplicates. -/
  | record {fields row τ} :
      (∀ l f, Ty.RowContains row l f → recordGet fields l ≠ none) →
      (∀ l f v, Ty.RowContains row l f → recordGet fields l = some v → HasTypeV v f) →
      Ty.TyEquiv (.record row) τ → HasTypeV (.Record fields) τ
  /-- `Select l`: `∀α r. ⟨l:α|r⟩ → α` (`select(l) = pure1(Record(RowExtend l q0 q1), q0)`). -/
  | partialSelect {label fieldTy tail τ} :
      Ty.TyEquiv (.fun (.record (.rowExtend label fieldTy tail)) .empty fieldTy) τ →
      HasTypeV (.Partial (.Select label) []) τ
  /-- `Extend l` with no args: `∀α r. α → {r} → {l:α|r}`. -/
  | partialExtendNil {label fieldTy row τ} :
      Ty.TyEquiv (.fun fieldTy .empty
        (.fun (.record row) .empty (.record (.rowExtend label fieldTy row)))) τ →
      HasTypeV (.Partial (.Extend label) []) τ
  /-- `Extend l` with the field value applied: `{r} → {l:α|r}`. -/
  | partialExtendOne {label v fieldTy row τ} :
      HasTypeV v fieldTy →
      Ty.TyEquiv (.fun (.record row) .empty (.record (.rowExtend label fieldTy row))) τ →
      HasTypeV (.Partial (.Extend label) [v]) τ
  /-- `Overwrite l` with no args: `∀α β r. α → {l:β|r} → {l:α|r}`. -/
  | partialOverwriteNil {label newTy oldTy tail τ} :
      Ty.TyEquiv (.fun newTy .empty
        (.fun (.record (.rowExtend label oldTy tail)) .empty
          (.record (.rowExtend label newTy tail)))) τ →
      HasTypeV (.Partial (.Overwrite label) []) τ
  /-- `Overwrite l` with the new field value applied: `{l:β|r} → {l:α|r}`. -/
  | partialOverwriteOne {label v newTy oldTy tail τ} :
      HasTypeV v newTy →
      Ty.TyEquiv (.fun (.record (.rowExtend label oldTy tail)) .empty
        (.record (.rowExtend label newTy tail))) τ →
      HasTypeV (.Partial (.Overwrite label) [v]) τ
  /-- `Perform l` (the resting effect operation, no args): `∀α β μ. α →⟨l:(α,β)|μ⟩ β`.
  Calling it with an `α` performs `l`; the latent row `⟨l:(α,β)|μ⟩` is unified with
  the ambient effect by the stack frame, so a resting `Perform l` is the witness that
  `l ∈ ε` (effect safety). -/
  | partialPerformNil {label argTy replyTy μ τ} :
      Ty.TyEquiv (.fun argTy (.effectExtend label argTy replyTy μ) replyTy) τ →
      HasTypeV (.Partial (.Perform label) []) τ
  /-- The internal `fixed` partial produced when `fix` saturates on a **pure** builder.
  `fix : ∀α β. (α →⟨β⟩ α) →⟨β⟩ α`; the fixpoint type `α` is pinned to an **arrow**
  `D →⟨γ⟩ R` — the only shape at which `fix` is operationally sound. (A base-type
  fixpoint such as `fix (\x. x+1) : Int` is well-typed under the raw gleam scheme but
  *crashes* — `fixed` is a `Partial`, so feeding it where an `Int` is expected fails the
  cast; restricting to arrows keeps every canonical-forms lemma valid and excludes that
  footgun.) The builder's *evaluation* latent is pinned to `∅` (building the recursive
  function — usually a lambda — does not itself perform); this is exactly the
  standard-recursion fragment (the recursive function `D →⟨γ⟩ R` may still be effectful
  when *called*). The pure builder is what makes the `fixed` re-application's
  `Apply builder` frame dischargeable with the empty-restricted `EffWeaken` (a non-pure
  builder needs general row subsumption — see `progress/2026-06-16-T6b-fix-scoping.md`).
  The stored value has the fixpoint arrow type (`fix builder = builder (fix builder)`).
  `Builtins.scheme "fixed" = none`, so this is the *only* way a `fixed` partial is typed
  (it has no `partialBuiltin` typing). -/
  | partialFixed {builder D γ R τ} :
      HasTypeV builder (.fun (.fun D γ R) .empty (.fun D γ R)) →
      Ty.TyEquiv (.fun D γ R) τ →
      HasTypeV (.Partial (.Builtin "fixed") [builder]) τ
  /-- `Handle l` with no args: at (a type equivalent to) the full `handle(l)` arrow. -/
  | partialHandleNil {l lift reply tail ret τ} :
      Ty.TyEquiv (handleTy l lift reply tail ret) τ →
      HasTypeV (.Partial (.Handle l) []) τ
  /-- `Handle l` with the handler applied: `Fun(exec, tail, ret)`. -/
  | partialHandleOne {l handler lift reply tail ret τ} :
      HasTypeV handler (handlerTy lift reply tail ret) →
      Ty.TyEquiv (.fun (execTy l lift reply tail ret) tail ret) τ →
      HasTypeV (.Partial (.Handle l) [handler]) τ
  /-- The reified delimited continuation `Resume acc iEnv`. The captured segment
  `acc.reverse` (the frames between the `perform` and its `Delimit`, with the matching
  `Delimit` re-pushed for a deep handler) is a stack-**segment** transformer taking the
  reply value (`reply`, at the handled row `εtop`) to the handler's return (`ret`, at the
  discharged row `tail`). It rests at the resumption type `kontTy reply tail ret =
  reply →⟨tail⟩ ret`. The segment is stored **quantified over the discharge row**
  `εBelow ⊇ tail`: the captured prefix runs at the fixed handled row `εtop`, and only the
  re-pushed final `Delimit`'s discharge varies, so the construction is polymorphic in
  `εBelow`. This is exactly what lets an escaping resume (pure tail, `tail ≈ ∅`) be invoked
  at a larger ambient `ε` — the resume dispatch instantiates `εBelow := ε`. -/
  | partialResume {acc iEnv reply εtop ret tail τ} :
      (∀ εBelow, Ty.EffWeaken tail εBelow → StackSegWf acc.reverse reply εtop ret εBelow) →
      Ty.TyEquiv (kontTy reply tail ret) τ →
      HasTypeV (.Partial (.Resume acc iEnv) []) τ

/-- An environment realizes a context, binding-for-binding. The value bound to a
scheme must inhabit *every* instantiation of it (polymorphic readiness; for the
monomorphic schemes of T3–T5 this is just `HasTypeV v τ`). -/
inductive EnvWf {m : Type} : Env m → Ctx → Prop where
  | nil : EnvWf [] []
  | cons {y v s env Γ} :
      (∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) → HasTypeV v (s.instantiateV args)) →
      (s.arity ≠ 0 → s.level ≠ 0 ∧ s.level ∈ s.body.levels) →
      EnvWf env Γ →
      EnvWf ((y, v) :: env) ((y, s) :: Γ)

/-- Peel the already-applied arguments of a builtin partial off an arrow,
yielding the residual type: each applied value matches the next domain. -/
inductive BuiltinPartialWf {m : Type} : Ty → List (Value m) → Ty → Prop where
  | nil {τ} : BuiltinPartialWf τ [] τ
  | cons {a ε r v applied τ} :
      HasTypeV v a →
      BuiltinPartialWf r applied τ →
      BuiltinPartialWf (.fun a ε r) (v :: applied) τ

/-- A continuation **segment** typed as a transformer tracking *both* endpoints
`(σin, εin) ⇒ (σout, εout)`. Unlike `StackWf` (whose `nil` is the answer and which keeps
one ambient row), a segment ends in a **hole** another stack plugs into, and an
**effect-discharging `Delimit` frame changes the row** (`εin = ⟨l:(lift,reply)|tail⟩`
above, `tail` below) — so the output row is a separate index. This types the reified
delimited continuation that `Resume` captures (`acc`, re-pushed via `move`); see
`stackSeg_append`. The six non-`Delimit` frames keep the row constant (`εin = εout`);
only `delimit` shrinks it. In the `HasTypeV` mutual block because `partialResume`
references it and it references `HasTypeV`. -/
inductive StackSegWf {m : Type} : Stack m → Ty → Ty → Ty → Ty → Prop where
  | nil {σ σ' ε ε'} : Ty.TyEquiv σ σ' → Ty.TyEquiv ε ε' → StackSegWf [] σ ε σ' ε'
  | trace {a w rest σin εin σout εout} :
      StackSegWf rest σin εin σout εout →
      StackSegWf ((Kontinue.Trace w, a) :: rest) σin εin σout εout
  | assign {a x body fenv Γ defnTy bodyTy εin σout εout rest lvl} :
      1 ≤ lvl →
      EnvWf fenv Γ →
      (hbody : HasType lvl ((x, .mono defnTy) :: Γ) body bodyTy εin) →
      HasTypeRT hbody →
      StackSegWf rest bodyTy εin σout εout →
      StackSegWf ((Kontinue.Assign x body fenv, a) :: rest) defnTy εin σout εout
  | arg {a arg fenv Γ argTy εf retTy εin σout εout rest lvl} :
      1 ≤ lvl →
      EnvWf fenv Γ →
      (harg : HasType lvl Γ arg argTy εin) →
      HasTypeRT harg →
      Ty.EffWeaken εf εin →
      StackSegWf rest retTy εin σout εout →
      StackSegWf ((Kontinue.Arg arg fenv, a) :: rest) (.fun argTy εf retTy) εin σout εout
  | applyf {a f fenv argTy εf retTy εin σout εout rest} :
      HasTypeV f (.fun argTy εf retTy) →
      Ty.EffWeaken εf εin →
      StackSegWf rest retTy εin σout εout →
      StackSegWf ((Kontinue.Apply f fenv, a) :: rest) argTy εin σout εout
  | callwith {a arg fenv argTy εf retTy εin σout εout rest} :
      HasTypeV arg argTy →
      Ty.EffWeaken εf εin →
      StackSegWf rest retTy εin σout εout →
      StackSegWf ((Kontinue.CallWith arg fenv, a) :: rest) (.fun argTy εf retTy) εin σout εout
  /-- A deep `Delimit l handler henv` frame: discharges `l` from the input row
  `⟨l:(lift,reply)|tail⟩`; the rest continues under any `εBelow ⊇ tail`
  (`EffWeaken tail εBelow`), mirroring the generalized `StackWf.delimit`. This lets an
  escaping resumption's captured segment be re-composed onto a base stack at a *larger*
  ambient (the row-bridge for a pure-tail continuation invoked in an effectful context).
  **No `EnvWf` premise** — the frame's stored env is never used for typing (the handler is
  a self-contained value), and at `reduceDeep` the frame env is arbitrary. -/
  | delimit {a l handler henv lift reply tail ret εin εBelow σout εout rest} :
      HasTypeV handler (handlerTy lift reply tail ret) →
      Ty.TyEquiv εin (.effectExtend l lift reply tail) →
      Ty.EffWeaken tail εBelow →
      StackSegWf rest ret εBelow σout εout →
      StackSegWf ((Kontinue.Delimit l handler henv false, a) :: rest)
        ret εin σout εout

end

/-- **Value conversion** (derived): a value's type may be replaced by a
`TyEquiv`-equal one. Each constructor already carries a `TyEquiv` to its natural
type; compose it with `trans`. -/
theorem HasTypeV.conv {m : Type} {v : Value m} {τ τ' : Ty}
    (h : HasTypeV v τ) (heq : Ty.TyEquiv τ τ') : HasTypeV v τ' := by
  cases h with
  | int he => exact .int (he.trans heq)
  | str he => exact .str (he.trans heq)
  | bin he => exact .bin (he.trans heq)
  | closure hlvl henv hfv hbody he => exact .closure hlvl henv hfv hbody (he.trans heq)
  | partialBuiltin hs hp he => exact .partialBuiltin hs hp (he.trans heq)
  | listNil he => exact .listNil (he.trans heq)
  | listCons hh ht he => exact .listCons hh ht (he.trans heq)
  | partialConsNil he => exact .partialConsNil (he.trans heq)
  | partialConsOne hh he => exact .partialConsOne hh (he.trans heq)
  | tagged hv he => exact .tagged hv (he.trans heq)
  | partialTag he => exact .partialTag (he.trans heq)
  | partialNoCases he => exact .partialNoCases (he.trans heq)
  | partialMatchNil he => exact .partialMatchNil (he.trans heq)
  | partialMatchOne hb he => exact .partialMatchOne hb (he.trans heq)
  | partialMatchTwo hb ho he => exact .partialMatchTwo hb ho (he.trans heq)
  | record hpres hmatch he => exact .record hpres hmatch (he.trans heq)
  | partialSelect he => exact .partialSelect (he.trans heq)
  | partialExtendNil he => exact .partialExtendNil (he.trans heq)
  | partialExtendOne hvf he => exact .partialExtendOne hvf (he.trans heq)
  | partialOverwriteNil he => exact .partialOverwriteNil (he.trans heq)
  | partialOverwriteOne hvf he => exact .partialOverwriteOne hvf (he.trans heq)
  | partialPerformNil he => exact .partialPerformNil (he.trans heq)
  | partialFixed hb he => exact .partialFixed hb (he.trans heq)
  | partialHandleNil he => exact .partialHandleNil (he.trans heq)
  | partialHandleOne hh he => exact .partialHandleOne hh (he.trans heq)
  | partialResume hseg he => exact .partialResume hseg (he.trans heq)

/-- **Segment output-endpoint conversion.** The hole endpoints may be replaced by
`TyEquiv`-equal ones. Simpler than input-conversion (the frame cases just thread to the
tail; only the `nil` case composes). -/
theorem stackSeg_conv_output {m : Type} {seg : Stack m} :
    ∀ {σin εin σout εout σout' εout' : Ty},
    StackSegWf seg σin εin σout εout → Ty.TyEquiv σout σout' → Ty.TyEquiv εout εout' →
    StackSegWf seg σin εin σout' εout' := by
  induction seg with
  | nil =>
      intro σin εin σout εout σout' εout' h hσ hε
      cases h with | nil h1 h2 => exact .nil (h1.trans hσ) (h2.trans hε)
  | cons hd rest ih =>
      intro σin εin σout εout σout' εout' h hσ hε
      obtain ⟨kont, ann⟩ := hd
      cases h with
      | trace h' => exact .trace (ih h' hσ hε)
      | assign hlvl henv hbody hrt h' => exact .assign hlvl henv hbody hrt (ih h' hσ hε)
      | arg hlvl henv harg hrt hw h' => exact .arg hlvl henv harg hrt hw (ih h' hσ hε)
      | applyf hf hw h' => exact .applyf hf hw (ih h' hσ hε)
      | callwith harg hw h' => exact .callwith harg hw (ih h' hσ hε)
      | delimit hh he hweak h' => exact .delimit hh he hweak (ih h' hσ hε)

/-- **Segment input-endpoint conversion.** A segment's input type/row may be replaced by
`TyEquiv`-equal ones (the arrow frames invert with `tyEquiv_fun_inv'` + `HasTypeV.conv`;
`assign` via `hasType_ctxHead_conv`; `delimit` folds the equiv into its membership row). -/
theorem stackSeg_conv_input {m : Type} {seg : Stack m} :
    ∀ {σin εin σout εout σin' εin' : Ty},
    StackSegWf seg σin εin σout εout → Ty.TyEquiv σin' σin → Ty.TyEquiv εin' εin →
    StackSegWf seg σin' εin' σout εout := by
  induction seg with
  | nil =>
      intro σin εin σout εout σin' εin' h hσ hε
      cases h with | nil h1 h2 => exact .nil (hσ.trans h1) (hε.trans h2)
  | cons hd rest ih =>
      intro σin εin σout εout σin' εin' h hσ hε
      obtain ⟨kont, ann⟩ := hd
      cases h with
      | trace h' => exact .trace (ih h' hσ hε)
      | assign hlvl henv hbody hrt h' =>
          obtain ⟨hbody', hrt'⟩ := hasTypeRT_ctxHead_conv hrt hσ
          exact .assign hlvl henv (hbody'.conv (.refl _) hε.symm)
            (hrt'.conv (.refl _) hε.symm) (ih h' (.refl _) hε)
      | @arg _ arg fenv Γ argTy εf retTy εin₀ _ _ rest' _ hlvl henv harg hrt hw h' =>
          obtain ⟨a', e', r', rfl, ha', he', hr'⟩ := Ty.tyEquiv_fun_inv' hσ
          have hw' : Ty.EffWeaken e' εin' := by
            rcases Ty.effWeaken_tyEquiv_right hw hε.symm with h | h
            · exact .inl (he'.trans h)
            · exact .inr (he'.trans h)
          exact .arg hlvl henv (harg.conv ha'.symm hε.symm) (hrt.conv ha'.symm hε.symm) hw'
            (ih h' hr' hε)
      | @applyf _ f fenv argTy εf retTy εin₀ _ _ rest' hf hw h' =>
          have hf' : HasTypeV f (.fun σin' εf retTy) :=
            hf.conv (.congrFun hσ.symm (.refl _) (.refl _))
          exact .applyf hf' (Ty.effWeaken_tyEquiv_right hw hε.symm) (ih h' (.refl _) hε)
      | @callwith _ arg fenv argTy εf retTy εin₀ _ _ rest' harg hw h' =>
          obtain ⟨a', e', r', rfl, ha', he', hr'⟩ := Ty.tyEquiv_fun_inv' hσ
          have hw' : Ty.EffWeaken e' εin' := by
            rcases Ty.effWeaken_tyEquiv_right hw hε.symm with h | h
            · exact .inl (he'.trans h)
            · exact .inr (he'.trans h)
          exact .callwith (harg.conv ha'.symm) hw' (ih h' hr' hε)
      | @delimit _ l handler henv lift reply tail ret εin₀ εBelow _ _ rest' hh heq hweak h' =>
          refine .delimit (hh.conv ?_) (hε.trans heq) hweak (ih h' hσ (.refl _))
          exact .congrFun (.refl _) (.refl _)
            (.congrFun (.congrFun (.refl _) (.refl _) hσ.symm) (.refl _) hσ.symm)

/-- **Segment composition** (the corrected `Resume` keystone). Two segments compose
end-to-end: the first's hole `(σmid, εmid)` is filled by the second. This *is*
provable across the row-changing `delimit` frame (the row is tracked per-endpoint),
unlike the uniform-`ε` `stackWf_append`. Re-proved by `induction seg` + `cases hseg`
(mutual inductives forbid `induction hseg`). -/
theorem stackSeg_append {m : Type} {seg k : Stack m} {σin εin σmid εmid σout εout : Ty}
    (hseg : StackSegWf seg σin εin σmid εmid) (hk : StackSegWf k σmid εmid σout εout) :
    StackSegWf (seg ++ k) σin εin σout εout := by
  induction seg generalizing σin εin with
  | nil => cases hseg with | nil h1 h2 => exact stackSeg_conv_input hk h1 h2
  | cons hd rest ih =>
      obtain ⟨kont, ann⟩ := hd
      cases hseg with
      | trace h => exact .trace (ih h)
      | assign hlvl henv hbody hrt h => exact .assign hlvl henv hbody hrt (ih h)
      | arg hlvl henv harg hrt hw h => exact .arg hlvl henv harg hrt hw (ih h)
      | applyf hf hw h => exact .applyf hf hw (ih h)
      | callwith harg hw h => exact .callwith harg hw (ih h)
      | delimit hh he hweak h => exact .delimit hh he hweak (ih h)

/-! ## The lookup lemma (replaces the substitution lemma)

If `env` realizes `Γ` and `Γ` binds `x` to scheme `s`, then `env` binds `x` to a
value inhabiting every instantiation of `s` — in particular the one the `var`
typing rule chose. -/

theorem envwf_lookup {m : Type} {env : Env m} {Γ : Ctx} {x : String} {s : Scheme}
    (h : EnvWf env Γ) (hl : Γ.lookup x = some s) :
    ∃ v, env.lookup x = some v ∧
      ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) → HasTypeV v (s.instantiateV args) := by
  induction env generalizing Γ with
  | nil => cases h; simp [List.lookup] at hl
  | cons hd tl ih =>
      obtain ⟨y, v⟩ := hd
      cases h with
      | @cons _ _ s' _ Γ₀ hv _ henv =>
          simp only [List.lookup_cons] at hl ⊢
          by_cases hxy : (x == y) = true
          · simp only [hxy] at hl ⊢
            cases hl
            exact ⟨v, rfl, hv⟩
          · simp only [hxy] at hl ⊢
            exact ih henv hl


/-- **`CtxPolyBd` is a projection of `EnvWf`.** Every `EnvWf.cons` carries the per-binding
`hpoly` clause (a poly binding sits at a nonzero level occurring among its body levels), so an
`EnvWf env Γ` witnesses `CtxPolyBd Γ` — the runtime nonzero-poly-level invariant the `let_poly`
preservation case feeds to `polyAboveFV_of_ctxPolyBd`. -/
theorem ctxPolyBd_of_envWf {m : Type} {env : Env m} {Γ : Ctx} (h : EnvWf env Γ) : CtxPolyBd Γ := by
  induction env generalizing Γ with
  | nil => cases h; intro b hb; exact absurd hb (by simp)
  | cons hd tl ih =>
      obtain ⟨y, v⟩ := hd
      cases h with
      | @cons _ _ s' _ Γ₀ _ hpoly henv =>
          intro b hb harity
          rcases List.mem_cons.mp hb with h | h
          · subst h; exact hpoly harity
          · exact ih henv b h harity

/-! ## Canonical forms

A value of a base type is the corresponding literal; a value of an arrow type is
a closure or a builtin partial (the only callable shapes in the pure core). Since
conversion is baked into each constructor's conclusion, these are pure `cases`:
the constructors whose *natural* head differs carry an impossible `TyEquiv` (e.g.
`TyEquiv .string .integer`), refuted by the head-shape inversion lemmas. -/

theorem canonical_integer {m : Type} {v : Value m} (h : HasTypeV v .integer) :
    ∃ n, v = .Integer n := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, rfl⟩ | exact absurd (Ty.tyEquiv_integer_inv he) (by simp)

theorem canonical_string {m : Type} {v : Value m} (h : HasTypeV v .string) :
    ∃ s, v = .String s := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, rfl⟩ | exact absurd (Ty.tyEquiv_string_inv he) (by simp)

theorem canonical_binary {m : Type} {v : Value m} (h : HasTypeV v .binary) :
    ∃ b, v = .Binary b := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, rfl⟩ | exact absurd (Ty.tyEquiv_binary_inv he) (by simp)

/-- A value at a list type is a `LinkedList`. -/
theorem canonical_list {m : Type} {v : Value m} {elem : Ty} (h : HasTypeV v (.list elem)) :
    ∃ es, v = .LinkedList es := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, rfl⟩ | (obtain ⟨_, hc⟩ := Ty.tyEquiv_list_inv he; simp at hc)

/-- **No value inhabits the empty union.** A tagged value's natural row is a
`rowExtend` (≠ `empty`), and every other value's natural type is not a union — so
the carried `TyEquiv` to `union empty` is impossible (head-shape mismatch under the
union row). This makes `NoCases` vacuously safe. -/
theorem canonical_union_empty {m : Type} {v : Value m}
    (h : HasTypeV v (.union .empty)) : False := by
  cases h <;> rename_i he <;>
    (have hs := Ty.tyEquiv_shape (Ty.tyEquiv_unionRow he); simp [Ty.shape, Ty.unionRow] at hs)

/-- A value at a union type is a `Tagged` value. -/
theorem canonical_union {m : Type} {v : Value m} {row : Ty} (h : HasTypeV v (.union row)) :
    ∃ label inner, v = .Tagged label inner := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, _, rfl⟩ | (have hs := Ty.tyEquiv_shape he; simp [Ty.shape] at hs)

/-- A value at a record type is a `Record` value. -/
theorem canonical_record {m : Type} {v : Value m} {row : Ty} (h : HasTypeV v (.record row)) :
    ∃ fields, v = .Record fields := by
  cases h <;> rename_i he <;>
    first | exact ⟨_, rfl⟩ | (have hs := Ty.tyEquiv_shape he; simp [Ty.shape] at hs)

/-- **`Select` is safe**: from the two record clauses, `recordGet` finds the field
(present) and its value has the row's type (matches) — no `MissingField`. -/
theorem record_get {m : Type} {fields : List (String × Value m)} {row : Ty} {l : String}
    {f : Ty}
    (hpres : ∀ l f, Ty.RowContains row l f → recordGet fields l ≠ none)
    (hmatch : ∀ l f v, Ty.RowContains row l f → recordGet fields l = some v → HasTypeV v f)
    (hc : Ty.RowContains row l f) : ∃ v, recordGet fields l = some v ∧ HasTypeV v f := by
  cases hg : recordGet fields l with
  | none => exact absurd hg (hpres l f hc)
  | some v => exact ⟨v, rfl, hmatch l f v hc hg⟩

/-- Inserting `l ↦ v` makes `recordGet … l = v` (the sorted-insert ↔ lookup hinge). -/
theorem recordInsert_get_eq {m : Type} (fields : List (String × Value m)) (l : String)
    (v : Value m) : recordGet (recordInsert fields l v) l = some v := by
  induction fields with
  | nil => simp [recordInsert, recordGet]
  | cons hd rest ih =>
      obtain ⟨k, vk⟩ := hd
      simp only [recordInsert]
      split
      · simp [recordGet]
      · next h1 =>
          split
          · simp [recordGet]
          · simp only [recordGet]
            split
            · next hh => exact absurd hh h1
            · exact ih

/-- Inserting `l ↦ v` leaves `recordGet … l'` unchanged for `l' ≠ l`. -/
theorem recordInsert_get_ne {m : Type} (fields : List (String × Value m)) {l l' : String}
    (v : Value m) (hne : (l' == l) = false) :
    recordGet (recordInsert fields l v) l' = recordGet fields l' := by
  induction fields with
  | nil => simp [recordInsert, recordGet, hne]
  | cons hd rest ih =>
      obtain ⟨k, vk⟩ := hd
      simp only [recordInsert]
      split
      · next hlk => obtain rfl := eq_of_beq hlk; simp [recordGet, hne]
      · split
        · simp [recordGet, hne]
        · simp only [recordGet]
          split
          · rfl
          · exact ih

/-- A value at an arrow type is a closure or a (callable) partial — never a
literal or a data structure. Callers `cases` the typing again to dispatch on the
partial's switch. -/
theorem canonical_arrow {m : Type} {v : Value m} {a ε r : Ty}
    (h : HasTypeV v (.fun a ε r)) :
    (∃ x body env, v = .Closure x body env) ∨
    (∃ sw applied, v = .Partial sw applied) := by
  cases h with
  | closure _ _ _ _ _ => exact Or.inl ⟨_, _, _, rfl⟩
  | partialBuiltin _ _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialConsNil _ => exact Or.inr ⟨_, _, rfl⟩
  | partialConsOne _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialTag _ => exact Or.inr ⟨_, _, rfl⟩
  | partialNoCases _ => exact Or.inr ⟨_, _, rfl⟩
  | partialMatchNil _ => exact Or.inr ⟨_, _, rfl⟩
  | partialMatchOne _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialMatchTwo _ _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialSelect _ => exact Or.inr ⟨_, _, rfl⟩
  | partialExtendNil _ => exact Or.inr ⟨_, _, rfl⟩
  | partialExtendOne _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialOverwriteNil _ => exact Or.inr ⟨_, _, rfl⟩
  | partialOverwriteOne _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialPerformNil _ => exact Or.inr ⟨_, _, rfl⟩
  | partialFixed _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialHandleNil _ => exact Or.inr ⟨_, _, rfl⟩
  | partialHandleOne _ _ => exact Or.inr ⟨_, _, rfl⟩
  | partialResume _ _ => exact Or.inr ⟨_, _, rfl⟩
  | record _ _ he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | tagged _ he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | int he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | str he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | bin he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | listNil he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc
  | listCons _ _ he => obtain ⟨_, _, _, hc⟩ := Ty.tyEquiv_fun_inv he; simp at hc

/-! ## Sanity checks -/

-- `Integer 5 : integer`.
example : HasTypeV (.Integer 5 : Value Unit) .integer := HasTypeV.int (Ty.TyEquiv.refl _)

-- The empty env realizes the empty context.
example : EnvWf ([] : Env Unit) [] := EnvWf.nil

-- A partially-applied `int_add` rests at the arrow `integer → integer`.
example : HasTypeV (.Partial (.Builtin "int_add") [.Integer 2] : Value Unit)
    (.fun .integer .empty .integer) :=
  HasTypeV.partialBuiltin (s := .mono (Ty.pure2 .integer .integer .integer)) (args := [])
    ⟨rfl, 2, rfl, by decide⟩
    (BuiltinPartialWf.cons (HasTypeV.int (Ty.TyEquiv.refl _)) BuiltinPartialWf.nil)
    (Ty.TyEquiv.refl _)

-- A closure over the empty env inhabits `integer → integer`.
example : HasTypeV (.Closure "x" (Eyg.Ir.Tree.variable_ "x") [] : Value Unit)
    (.fun .integer .empty .integer) :=
  HasTypeV.closure (lvl' := 1) (le_refl 1) EnvWf.nil
    (by intro l hl; simp only [Ty.levels] at hl; exact absurd hl (by simp))
    (HasType.var (s := .mono .integer) (args := []) rfl)
    (Ty.TyEquiv.refl _)

-- The `fixed` value of the pure builder `\f. f` (a `(Int→Int)→(Int→Int)` closure)
-- inhabits the fixpoint arrow `Int → Int` (`fix : ((Int→Int)→(Int→Int)) → (Int→Int)`).
example : HasTypeV (.Partial (.Builtin "fixed")
    [.Closure "f" (Eyg.Ir.Tree.variable_ "f") []] : Value Unit)
    (.fun .integer .empty .integer) :=
  HasTypeV.partialFixed
    (HasTypeV.closure (lvl' := 1) (le_refl 1) EnvWf.nil
      (by intro l hl; simp only [Ty.levels] at hl; exact absurd hl (by simp))
      (HasType.var (s := .mono (.fun .integer .empty .integer)) (args := []) rfl)
      (Ty.TyEquiv.refl _))
    (Ty.TyEquiv.refl _)

end Eyg.Types
