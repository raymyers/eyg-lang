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
