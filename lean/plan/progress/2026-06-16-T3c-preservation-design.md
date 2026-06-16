---
date: 2026-06-16
milestone: T3c
status: design recorded; proof is the next slice
---

# T3c — preservation/progress design notes (the crux)

Definitions are in place and green: `HasType` (T3a), `HasTypeV`/`EnvWf`/
`BuiltinPartialWf` + `envwf_lookup` + canonical forms (T3b), `StackWf`/`MStateWf`
+ `mStateWf_initial` (T3c-i), and the `TyEquiv` head-shape inversion lemmas
`tyEquiv_{fun,integer,string,binary,record,union}_inv` (T1b-partial, this slice).
What remains for the first green theorem: `preservation`, `progress`, `soundness`.
This note records the design so the proof slice is mechanical.

## Statement shapes

```
preservation : MStateWf s τ ε → Reduce s μ s' → MStateWf s' τ ε
progress     : MStateWf s τ ε → s.IsValue ∨ ∃ μ s', Reduce s μ s' ∧ ¬ μ.IsCrashMove
soundness    : HasType [] prog τ ε(=empty) → evalR never `.done (.crash r)` for the bad reasons
```

`Reduce` has three constructors; for well-typed states:
- **`reply`** (source is a `wait`): `MStateWf (.wait …) = False`, so `exact hwf.elim`.
- **`perform`** (`reduce1Run cfg = .perform …`, target a `wait`, `MStateWf = False`):
  must be shown **impossible** for the pure core — the effect-safety obligation.
  `.perform` is only produced by `reducePerform`, reached only when a
  `.Partial (.Perform l) []` value is applied. No `HasTypeV` rule types a
  `Perform` partial, so a well-typed function value (canonical_arrow ⇒ `Closure`
  or builtin `Partial`) is never one ⇒ `reduce1Run` of a well-typed state is never
  `.perform`. Package this as `reduce1Run_not_perform` and reuse in both
  preservation (perform case) and progress (no crash via unhandled effect).
- **`tau`** (`reduce1Run cfg = .tau cfg'`): the real work — see below.

## The `tau` case: split on the control/stack, match `reduce1Run`

`MStateWf (.run (c, env, k))` unfolds by `c`:
- `.E e`: `∃ Γ τin, EnvWf env Γ ∧ HasType Γ e τin ε ∧ StackWf k τin ε τ`.
- `.V v`: `∃ τin, HasTypeV v τin ∧ StackWf k τin ε τ`.

`reduce1Run` dispatches `reduceEval`/`reduceApply`/`reduceCall`. Each arm's target
is **exactly** matched by a `StackWf`/`HasType`/`HasTypeV` constructor (the
`Machine.lean` frames were written to mirror `reduce1Run`), so each case is: invert
the typing, build the successor's witness. The closure-application case (the heart)
checks out by hand:

> `(.V argval, _, (Apply f fenv,a)::k)` with `argval : argTy`, `StackWf.applyf`
> giving `HasTypeV f (.fun argTy ε retTy)` and `StackWf k retTy ε τ`. `reduceCall`
> on `f = Closure x body cenv` (canonical_arrow) steps to
> `(.E body, (x,argval)::cenv, (Trace argval,a)::k)`. Closure inversion gives
> `EnvWf cenv Γc` and `HasType ((x,mono argTy)::Γc) body retTy ε`; the extended env
> realizes `(x,mono argTy)::Γc`; `StackWf.trace` re-wraps `k`. ⇒ successor is
> `MStateWf … τ ε`. ✓

The `let`/`lam`/`var`/`literal`/`Arg`-frame/`Trace`-frame cases are analogous and
were checked against the frame typings in `Machine.lean`.

## ⚠️ The one design change required: conversion at `StackWf.nil` (and friends)

A control `.E e` may be typed at `τin` via a derivation ending in `conv`, so when
`e` reduces to a value its *natural* type `τnat` only satisfies `TyEquiv τnat τin`,
while the stack expects `τin`. Two consequences:

1. **`StackWf.nil` must carry `TyEquiv`**, not exact equality. Change
   `nil : StackWf [] τ ε τ` to `nil {τin τout ε} : TyEquiv τin τout → StackWf [] τin ε τout`.
   Then the final answer is "a value of type `∼= τ`", and the soundness statement
   reads "terminal value has a type `TyEquiv`-equal to `τ`" — the honest claim for
   a row-equational system.
2. **`StackWf` must respect `TyEquiv` on the incoming type**:
   `stackWf_conv : StackWf k τin ε τ → TyEquiv τnat τin → StackWf k τnat ε τ`.
   For `nil` it composes the equiv; for the arrow-demanding frames
   (`arg`/`callwith`/`applyf`) it uses `tyEquiv_fun_inv` (this slice) to turn
   `TyEquiv τnat (.fun argTy ε retTy)` into `τnat = .fun a' e' r'` and then the
   **component** inversion `TyEquiv a' argTy ∧ TyEquiv e' ε ∧ TyEquiv r' retTy`
   (NOT yet proved — see below) plus `HasType.conv` on the stored arg node.

### Outstanding lemma: component inversion for arrows/rows

`tyEquiv_fun_inv` (delivered) only recovers the *head*. `stackWf_conv` for the
`arg`/`callwith` frames also needs the components:
`TyEquiv (.fun a e r) (.fun a' e' r') → TyEquiv a a' ∧ TyEquiv e e' ∧ TyEquiv r r'`.
This is "no-confusion up to `TyEquiv`". Cleanest via the **normalization** route
(finish T1b): `tyEquiv_iff : TyEquiv s t ↔ normalize s = normalize t`, with
`normalize (.fun …) = .fun (normalize a) (normalizeEff e) (normalize r)`, gives
component inversion by `injection` on the normal forms. So **finishing T1b
normalization is the prerequisite** for the `arg`/`callwith` conv handling.

Alternative (avoids component inversion): make `HasTypeV` itself `TyEquiv`-closed
(add `convV : HasTypeV v τ → TyEquiv τ τ' → HasTypeV v τ'`) and keep `StackWf`
frames exact; then the closure/value always presents *its* natural type and the
conv is absorbed when the value meets the frame via `HasTypeV` rather than via the
stack. This localizes conv to values and may sidestep `stackWf_conv` for the arrow
frames entirely — **evaluate this option first; it may be cheaper than finishing
normalization.** (Closure inversion would then yield the arrow up to `TyEquiv`,
and `tyEquiv_fun_inv` + component inversion is still needed to read off `argTy`.)

## Recommended order for the next slices

1. **Finish T1b normalization** (`normalize`/`normalizeRow`/`normalizeEff`/
   `rowInsert`, `normalize_tyEquiv`, `tyEquiv_normalize`, `tyEquiv_iff`, decidability,
   component inversion). Foundational and unblocks the conv handling cleanly.
2. **Amend `StackWf.nil` to the `TyEquiv` form** and prove `stackWf_conv`.
3. **`preservation`** (`tau` case split + `reduce1Run_not_perform`), then
   **`progress`**, then **`soundness` over `evalR`** (fold preservation across the
   fuel, conclude no bad-reason crash; permit `Unrepresentable` per the plan's crash
   list — but the *pure builtin-free* core never reaches it anyway).

The builtin-saturation preservation case stays a **T6** obligation (and `int_add`
can legitimately trap with `Unrepresentable`); the T3 green theorem is over the
pure λ/let/literal core, where no builtin partial is ever applied.

---

## UPDATE (infrastructure complete; recipe validated by hand)

All supporting lemmas are now green and axiom-clean:
- `HasTypeV` with conversion **baked into each constructor** (not a recursive
  `convV`) + `HasTypeV.conv` (derived) + canonical forms by pure `cases`.
- Generation lemmas `inv_{int,str,bin,var,builtin,lambda,let,app}` (T3c-ii(a)).
- `TyEquiv` head inversions + **component inversion** `tyEquiv_fun_components`.
- `envwf_lookup`, `StackWf`/`MStateWf`, `mStateWf_initial`.

**Key simplification discovered — no `stackWf_conv`, no `StackWf.nil` change needed.**
The earlier worry (a produced value's natural type only `∼=` the stack's incoming
type) dissolves: instead of converting the *stack's* incoming type, convert the
*control/value/result* type to **exactly** what the stack expects, using
`HasType.conv` / `HasTypeV.conv` (both available). The crux closure-application
case, fully hand-checked:

> State `(.V argval, _, (Apply f fenv,ann)::rest)`; `StackWf.applyf` gives
> `HasTypeV f (.fun argTy ε retTy)` and `StackWf rest retTy ε τ`, with
> `HasTypeV argval argTy`. `canonical_arrow f ⇒ Closure x body cenv`. Invert
> `HasTypeV (Closure …)` ⇒ `EnvWf cenv Γc`, `HasType ((x,mono argTy0)::Γc) body
> retTy0 εb0`, `heq : TyEquiv (.fun argTy0 εb0 retTy0) (.fun argTy ε retTy)`;
> `tyEquiv_fun_components heq ⇒ argTy0∼argTy, εb0∼ε, retTy0∼retTy`.
> Successor `(.E body, (x,argval)::cenv, (Trace argval,ann)::rest)`:
> - bind `x` at **argTy0** (not argTy): `HasTypeV.conv argval (argTy∼argTy0)` ⇒
>   `EnvWf ((x,argval)::cenv) ((x,mono argTy0)::Γc)`;
> - body: `HasType.conv hbody (retTy0∼retTy) (εb0∼ε)` ⇒
>   `HasType ((x,mono argTy0)::Γc) body retTy ε`;  ← convert the RESULT to retTy
> - stack: `StackWf.trace hrest` (incoming `retTy`, exactly what `rest` wants). ✓

The same "produce the value/result at the stack's exact expected type" pattern
handles `lam`/`int`/`str`/`bin`/`var` eval (use the generation lemma's `TyEquiv`
directly in the value constructor) and the `Arg`/`Assign`/`Trace`/`CallWith`
frames. The `var` case's "value found in env" comes from `envwf_lookup` — that is
exactly the **no-`UndefinedVariable`-crash** content of soundness.

### Two small consistency lemmas the `Builtin` *node* case needs

`(.E (.Builtin id), …) → (.V (.Partial (.Builtin id) []), …)` is a `tau` only if
`isBuiltin id` (else the machine crashes `UndefinedBuiltin`). So well-typedness
(`Builtins.scheme id = some s`) must imply:
1. `isBuiltin id = true` (the analyzer table ⊆ the interpreter's arity table), and
2. `s.instantiate args` is an **arrow** (every builtin scheme is a function), so
   `HasTypeV.partialBuiltin … BuiltinPartialWf.nil …` types the `[]`-partial.
Both are finite per-`id` facts over the T3 subset (`decide`/case split).

### Net remaining for the green theorem
1. (optional) the two `Builtin`-node consistency lemmas (or omit `Builtin` from the
   T3 theorem and keep it λ/let/literal-only — even simpler, fully sorry-free).
2. Write `preservation` (`tau` split per the recipe; `reply` via `MStateWf wait =
   False`; `perform` via `reduce1Run_not_perform`, itself immediate since no
   `HasTypeV` rule types a `Perform` partial so `canonical_arrow` never yields one).
3. `progress` (each well-typed non-value `reduce1Run` is `.tau`/value, never a bad
   crash) and `soundness` over `evalR` (fold preservation across fuel).
The **builtin application/saturation** case (`reduceCall` on a `Partial Builtin`)
remains the T6 obligation.
