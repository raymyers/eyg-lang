---
date: 2026-06-16
milestone: T6b
status: scoped (not started)
---

# T6b remainder: typing `fix` (`FixPreserves` / `FixNoBadCrash`)

## What is already done (this session)

T6b's **assembly** is delivered (`Eyg/Types/Soundness.lean`,
commit "Lean type-soundness T6b: discharge builtin saturation obligations"):

- `builtinAppPreserves : FixPreserves m → BuiltinAppPreserves m`
- `builtinAppNoBadCrash : FixNoBadCrash m → BuiltinAppNoBadCrash m`

cover **every schemed builtin except `fix`**, sorry-free, axioms clean. The two
`Fix*` sub-hypotheses are the only residual builtin assumption. Wrappers
`preservation_fix` / `progress_fix` / `soundness_value_fix` re-state the headline
theorems with the general-builtin obligation removed.

## Why `fix` is *not* a quick slice

`FixPreserves` is about `reduceCall (.Partial (.Builtin "fix") applied) builder`.
`builtinArity "fix" = 1`, so it saturates on the builder:

```
reduceCallBuiltin "fix" [builder]
  = .tau (.V (.Partial (.Builtin "fixed") [builder]), env,
          (Kontinue.Apply builder env, ann) :: k)
```

The successor's **control value is `.Partial (.Builtin "fixed") [builder]`**, and
`Builtins.scheme "fixed" = none` — so it is **not typeable via `partialBuiltin`**.
Typing it needs a *bespoke* `HasTypeV` rule (analogous to `Handle`'s internal
`Resume`):

```
partialFixed : HasTypeV builder (.fun α ε α) → Ty.TyEquiv α τ →
               HasTypeV (.Partial (.Builtin "fixed") [builder]) τ
```

(`fix : ∀αβ. (α →⟨β⟩ α) →⟨β⟩ α`; the fixpoint value has type `α`, which is itself
typically an arrow — the recursive function.)

### The cascade

Adding a constructor to the **mutual** inductive `HasTypeV` breaks every site that
enumerates its value constructors. The arrow-value sites that need a new
`partialFixed` arm:

1. `canonical_arrow` (`Runtime.lean`) — add `.Partial (.Builtin "fixed") [_]` to the
   "is a `Closure` or an operator/builtin partial" disjunction.
2. `HasTypeV.conv` (`Runtime.lean`) — trivial `partialFixed` arm (carry the
   `TyEquiv` through, like `partialBuiltin`).
3. `preservation_V`'s `applyf` split (`Soundness.lean` ~445) — the `fixed`
   re-application case (see below).
4. `progress`'s `applyf` and `callwith` splits (`Soundness.lean` ~1109, ~1180).
5. any `cases hf`/`canonical_arrow` rcases in `reduceCall_perform_wait` and friends.

### The genuinely hard arm — `fixed` re-application

When `.Partial (.Builtin "fixed") [builder]` is itself applied (its type `α` is an
arrow), `reduceCall` pushes **two** frames:

```
reduceCallBuiltin "fixed" [builder, arg]
  = .tau (.V (.Partial (.Builtin "fixed") [builder]), env,
          (Kontinue.Apply builder env, ann) ::
          (Kontinue.CallWith arg env, ann) :: k)
```

i.e. it computes `(builder (fixed builder)) arg`. Preservation must show:
`StackWf (Apply builder :: CallWith arg :: k) ...` is well-typed, which forces
`α = .fun D ε R` and threads: `Apply builder` feeds `fixed-partial : α` into
`builder : α →ε α` (yields `α`), `CallWith arg` applies that `α = D→εR` to
`arg : D` (yields `R`), `k` carries `R`. The subtle obligations:

- **Effect equality `β = ε`.** `fix`'s latent effect must equal the ambient row;
  everything is up to `TyEquiv`, so the `applyf`/`callwith` frames need the
  builder's effect converted to the exact ambient `ε` (use `HasTypeV.conv` +
  `tyEquiv_fun_components`, as the closure-application crux already does).
- **Self-application well-foundedness is *not* a proof obligation** (it is a
  runtime value, no termination claim) — only type preservation.

`FixNoBadCrash` is comparatively easy once `partialFixed` exists: the `fix`/`fixed`
arms of `reduceCallBuiltin` never `.done (.crash _)` (they always `.tau`), so the
crash hypothesis is contradictory — `reduceCallBuiltin_other` does **not** apply
(fix/fixed are special), so prove a small `reduceCallBuiltin_fix_ne_crash` /
`_fixed_ne_crash` by `unfold` + `simp`.

## ⚠ Added finding: the arity-1 / special-arm interaction (harder than first scoped)

`builtinArity "fix" = 1`, but the `reduceCallBuiltin` **special arm** `("fix",[builder])`
fires only at list-length **1**. These interact badly across the `BuiltinPartialWf`
peel of a typed `.Partial (.Builtin "fix") applied`:

- `applied = []` → `reduceCallBuiltin "fix" [arg]` (length 1) → **special arm** → the
  real fixpoint (`fixed` partial + pushed `Apply`). *This is the case `partialFixed`
  is for.*
- `applied = [x]` (only typeable when the fixpoint type `α` is itself an arrow) →
  `reduceCallBuiltin "fix" [x, arg]` (length 2) → **generic `_,_` branch** → since
  `2 ≠ arity 1`, accumulate `.Partial (.Builtin "fix") [x, arg]`. A *degenerate but
  typeable* resting partial.
- longer `applied` → likewise generic-accumulate.

The catch: `reduceCallBuiltin_other` (the generic-branch lemma) **requires `key ≠
"fix"`**, so it does *not* cover the degenerate accumulate cases. They need a
**fix-specific** reduction lemma (`reduceCallBuiltin "fix" args = _,_`-branch when
`args.length ≠ 1`) — provable by `unfold` + `split`, but it is extra plumbing the
generic drivers can't reuse.

So `FixPreserves` is **not** just "the `applied = []` fixpoint case": it must also
discharge the degenerate `applied = x::_` accumulate cases (where `α` is an arrow).
Practically: peel `hpw` like the arity drivers, branch on `applied = []` (special,
`partialFixed`) vs `applied = _::_` (generic accumulate, re-`partialBuiltin` at the
residual — `fix` *does* have a scheme, so this is available). Budget accordingly; the
`partialFixed` cascade plus this two-mode split is why `fix` is its own slice.

## ⚠ Added finding 2: effect consistency in the `fixed` self-application

`partialFixed : HasTypeV builder (.fun α ε α) → TyEquiv α τ → HasTypeV (fixed [builder]) τ`
stores the builder's **latent effect `ε`**. When the `fixed` partial is later applied,
`reduceCall` pushes `Apply builder :: CallWith arg :: k`, and the `applyf` frame for
`Apply builder` forces `builder`'s latent effect to equal the **stack's ambient `εamb`**.
So preservation needs `ε = εamb`. But `canonical_arrow` only gives `TyEquiv α (.fun argTy
εamb retTy)` — there is **no syntactic link forcing `α`'s internal effect (hence the
recursion's effect) to equal the builder's `ε`**. In Koka's `fix : ∀αβ. (α→β α) →β α`
the result `α`, when it is the recursive arrow `D →β R`, carries effect `β` *by the type
structure*, so `ε = εamb` holds — but the Lean `partialFixed` rule must **encode that
link** (e.g. quantify `α = D →ε R` in the applied case, or carry the effect in the rule)
rather than leave `α` opaque. Getting this rule shape right (so the self-application
preserves *and* the rule is inhabited by the real `fix`) is the genuine design work — it
is effect-threading metatheory, not mechanical plumbing. Budget it with the `Handle`
effect work, not as a quick win.

## ⚠ Added finding 3 (the real blocker): `fix` needs **effect weakening** in `StackWf`

Tracing the authoritative gleam `Apply` inference
(`contextual.gleam` §`ir.Apply`: a fresh `test_eff` is unified with the function's latent
effect, then `unify(test_eff, eff)` against the ambient — **exact** match, no subsumption)
together with the CEK `fix` unrolling settles why `fix` is hard, and it is *not* just a
cascade:

* `fix`'s scheme is `(α →β α) →β α` with `β` = the **builder's latent effect**. For the
  usual recursive function (e.g. `fix (\self. \n. perform Log n; self (n-1))`), the
  builder's body is a *lambda* (building it is pure), so **`β = Empty`**, while the
  recursive function type is `α = Nat →⟨Log|μ⟩ R` (the `Log` fires when the function is
  *called*). So `β` (Empty) and `α`'s internal effect (`{Log|μ}`) are genuinely different
  — and gleam accepts this.
* The machine: when the recursive function (the `fixed` partial `: α`) is *called* at
  ambient `{Log|μ}`, `reduceCallBuiltin "fixed" [builder, arg]` pushes
  `Apply builder :: CallWith arg :: k`. The `Apply builder` frame applies the **pure**
  `builder : α →Empty α` **inside the `{Log|μ}` ambient**.
* `StackWf.applyf` requires the function's latent effect to **equal** the frame's ambient
  (`HasTypeV f (.fun argTy ε retTy)` with `ε` = the stack's row). Here that demands
  `Empty = {Log|μ}` — **false**. Preservation cannot type the successor.

**Diagnosis:** the uniform-ambient, exact-match `StackWf` (correct for T3–T5, where every
applied function's latent effect *was* the ambient by construction) cannot express
"apply a *pure* (or effect-smaller) function within an effectful context". `fix`'s
unrolling is the first place the machine does exactly that. The same gap means **a pure
builtin can only be applied in a pure ambient** in the current formalization
(`BuiltinAppPreserves`'s `HasTypeV (builtin partial) (.fun argTy ε retTy)` forces
`ε = Empty` via the scheme's `Empty` latent) — i.e. the *effectful* fragment currently has
no effect weakening at all; it happens not to bite before `fix` only because no earlier
rule applies a pure function under a non-empty row.

**What `fix` actually requires (a foundational change, not a cascade):** add **effect
weakening / row subsumption** to the application frames — e.g. an `applyf`/`callwith`
variant allowing the function's latent row to be a *sub-row* of the ambient (`Empty ⊆ ε`,
or general `ε_fun ⊑ ε`), with the attendant row-subsumption metatheory (a `RowSub`
relation + its interaction with `TyEquiv`/`EffContains`). Only then can `partialFixed`
(builder `: α →β α`, typed at `α`) be applied soundly at an ambient `⊇ β`. This is a core
type-system extension affecting `StackWf` and likely the `HasType.app` rule, comparable in
weight to `Handle`. It also subsumes the earlier "effect-consistency" worry (findings 2):
with weakening, the builder's `β` need not equal the ambient, only be contained in it.

## Recommended plan for next session

1. Add `partialFixed` to `HasTypeV` (Runtime.lean), plus its `conv` arm and a
   `canonical_fixed`/extended `canonical_arrow`.
2. Re-green the ~5 cascade sites with a `partialFixed` arm (mostly mirror
   `partialBuiltin`; the `applyf` arm in `preservation_V` is the real work).
3. Prove `FixPreserves`/`FixNoBadCrash` and feed them to `builtinAppPreserves`/
   `builtinAppNoBadCrash` to obtain the **fully unconditional** builtin obligations.

This is a self-contained mini-`Handle`; budget it as its own slice. It is lower
risk than the real `Handle` (no continuation capture, no row discharge), but it
does touch the `HasTypeV` mutual block, so do it as one atomic cascade.

## ⚠ Update (2026-06-17): finding 3 RESOLVED; two new precise constraints

The effect-weakening **consuming slice is delivered**
(`2026-06-17-T6b-effect-weakening-consuming-slice.md`): `StackWf.arg/applyf/callwith`
now carry `Ty.EffWeaken εf ε` and `HasType.app` is generalized. So **finding 3's blocker
is gone** — a pure (`∅`-latent) builder *can* now be applied under an effectful ambient
via the `applyf` frame's `EffWeaken` (with `effWeaken_empty`). Tracing the `fixed`
re-application against the new frames sharpened the remaining work into two concrete
constraints the next session must handle:

### Constraint A — `FixPreserves` needs `EffWeaken` threaded through `BuiltinAppPreserves`

The consuming slice **decoupled** the builtin hypotheses' function-latent from the stack
ambient *without* an `EffWeaken` premise (sound for general builtins — they don't perform,
the discharge ignores the latent). **`fix` is different:** the `fixed` re-application
pushes `Apply builder :: CallWith arg :: rest`, and the `Apply builder` frame needs
`EffWeaken ε_b ε_amb` (builder latent ⊑ call ambient) and `CallWith arg` needs
`EffWeaken εf ε_amb` (the recursion arrow's latent ⊑ ambient — *this* one is exactly the
`hw` the calling frame supplies). So the `fix` slice must **re-add an `EffWeaken εf ε`
premise to `BuiltinAppPreserves` and `FixPreserves`** (keeping the decoupled latent),
pass the frame's `hw` at the `hsat` call sites (preservation_V / reduce1Run_done_value_typed
applyf+callwith — the binders are already in scope, currently named `hw`/`_`), and ignore it
in the general-builtin discharge. `BuiltinAppNoBadCrash`/`FixNoBadCrash` need no change
(fix/fixed never `.done (.crash _)`; no stack reasoning).

### Constraint B — the *call-ambient* `EffWeaken ε_b ε_amb` is the real finding-2 crux

`partialFixed` stores `builder : .fun α ε_b α`. At the `Apply builder` frame (when the
fixed value, having **escaped** as a value of type `α`, is later called at ambient
`ε_amb`), preservation needs `EffWeaken ε_b ε_amb`. The calling frame only supplies
`EffWeaken γ ε_amb` where `γ` is `α`'s *internal* latent (the recursion effect) — **not**
`ε_b` (the builder's eval latent). For the **standard recursive function** the builder is
`\self. \x. e` and evaluating `builder self` returns a lambda purely, so `ε_b = ∅` and
`effWeaken_empty` discharges it — **so the pure-builder fix is achievable now.** For a
builder that performs *while building* (`ε_b ≠ ∅`), soundness would need `EffWeaken ε_b γ`
(builder effect ⊑ recursion effect — true semantically, since each unroll re-runs the
builder when the function is called), but that is a *proper sub-row* relation the
empty-restricted `EffWeaken` cannot express — it needs the **general row-variable-aware
subsumption** (deferred future work, per Open Question 3). 

**Recommended scoping for the next session:** deliver `partialFixed` + `FixPreserves`
**restricted to pure builders** (`ε_b = ∅`, via an explicit premise `Ty.TyEquiv ε_b .empty`
in the rule, discharged by `effWeaken_empty` at the `Apply builder` frame), which covers
all standard recursion. Confirm against `gleam_analysis` whether a non-`∅` builder latent
is even reachable through `do_infer`'s `fix` scheme; if `do_infer` forces the builder pure
(likely, since the scheme's `(α→β α)→β α` with `β` shared may pin `β=∅` in practice for
value-restricted let-bound `fix`), the restriction is complete, not partial. The α-vs-arrow
type mismatch in the stack (Constraint, original finding 2) is handled by converting the
builder via `HasTypeV.conv (… congrFun hα …)` to `.fun arrow ε_b arrow` so the
`CallWith arg` frame's exact-`.fun argTy εf retTy` input is met — no stack-conversion lemma
needed.
