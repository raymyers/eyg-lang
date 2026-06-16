# T5 — Un-pinning the effect row: `Perform` + `wait` typing + effect safety (design)

**Status:** design complete, not yet implemented. Prereqs T5a (`EffRow.lean`) and
T5b (`doPerformR`, transparent effect boundary) are **done and committed**. This
note records the fully worked-out design for the next, atomic "un-pin" slice so it
can be executed without re-deriving it.

## Why this is one atomic slice (cannot be split smaller)

Adding the `Perform` typing rule cascades through every exhaustive case-split:
- `not_perform` (preservation's `.perform` case) becomes **false** — a well-typed
  `Perform l` applied to an arg *does* reduce to `.perform`. So `not_perform` must
  be replaced by an effect-safety lemma in the same change.
- `MStateWf`'s `wait` (currently `False`) must become real typing, because
  `Reduce.perform` produces a `.wait` successor.
- `canonical_arrow`, `HasTypeV.conv`, `reduceCall_ne_perform`,
  `reduce1Run_done_value_typed`, `hasType_expr_form`, `preservation_E`, `progress`
  all `cases` on the partial switch / `HasType` forms and need the new `Perform`
  case.

So `Perform` cannot land "rule-only" and stay green. Budget it as one slice.

## The typing rules (from `contextual.gleam`)

`perform(l) = Fun(q0, EffectExtend(l, (q0,q1), Empty), q1)` (line 497). Declarative
rule — **use an arbitrary tail `μ`** (Koka "operation as a variable"), more
permissive than the scheme's literal `Empty` but exactly what makes effect safety
fall out:

```lean
-- Typing.lean
| perform {Γ l a b μ ε ann} :
    HasType Γ ⟨.Perform l, ann⟩ (.fun a (.effectExtend l a b μ) b) ε
```

The node `Perform l` is a *value* (a resting partial), so its ambient `ε` is free;
the **`app` rule forces the function's latent effect = ambient ε**, so
`Perform l arg` is typeable only when `ε ≃ effectExtend l a b μ`, i.e.
`EffContains ε l a b`. That *is* effect safety.

Runtime value typing (the resting partial `Partial (Perform l) []`):

```lean
-- Runtime.lean
| partialPerformNil {label a b μ τ} :
    Ty.TyEquiv (.fun a (.effectExtend label a b μ) b) τ →
    HasTypeV (.Partial (.Perform label) []) τ
```

Add the matching cases to `HasTypeV.conv` and `canonical_arrow` (it's an arrow ⇒
`Or.inr ⟨_, _, rfl⟩`), and `inv_perform` in `Generation.lean`, and the
`hasType_expr_form` disjunct (one more `Perform` arm + extend every `rcases` over
that lemma by one alternative, as done for `Extend`/`Overwrite`).

**Defer `Handle` to the next slice.** With no `Handle` rule, a well-typed `StackWf`
has **no `Delimit` frame** (none of the 6 frame constructors is `Delimit`). That is
the key simplification below.

## `wait` typing (the new `MStateWf` clause)

`Reduce.perform : reduce1Run cfg = .perform op lift envP kP → Reduce (.run cfg)
(.perform op lift) (.wait op envP kP)`, and `kP` is the stack **below** the consumed
`Apply` frame (`reduceCall` is handed `rest`; `reducePerform … env rest`). After a
reply, `Reduce.reply : .wait op env k → .run (.V v, env, k)`, so the reply value `v`
flows into `k`. Hence:

```lean
-- Machine.lean, MStateWf
| .wait op _ k, τ, ε => ∃ a b, Ty.EffContains ε op a b ∧ StackWf k b ε τ
```

`b` is the operation's **reply type**; `StackWf k b ε τ` says feeding the reply into
`k` yields the answer `τ`. `EffContains ε op a b` is the effect-safety witness
(`op ∈ ε`). `env` is irrelevant (the resumed control is a value).

## Effect safety: a well-typed `.perform` lands a typed `wait`

The performing state is `(.V argv, env, (Apply (Partial (Perform l) []) fenv, ann)
:: rest)`. The `applyf` frame gives `HasTypeV (Partial (Perform l) []) (fun argTy ε
retTy)` and `StackWf rest retTy ε τ`. Invert `partialPerformNil`: the arrow is
`fun a (effectExtend l a b μ) b`, so (`tyEquiv_fun_components`) `argTy ≃ a`,
`ε ≃ effectExtend l a b μ`, `retTy ≃ b`. From `ε ≃ effectExtend l a b μ` and
`EffContains (effectExtend l a b μ) l a b` (`.head`), `tyEquiv_effContains` gives
`EffContains ε l a' b'` with `a≃a'`, `b≃b'`. Convert `StackWf rest retTy ε τ` to
`StackWf rest b' ε τ` (need a `StackWf` input-conversion — see "lemma to add").
That discharges the new `wait` clause: `⟨a', b', hEff, hStack⟩`.

**Lemma to add (the one new infra piece):**
`stackWf_conv_in : Ty.TyEquiv σ σ' → StackWf k σ ε τ → StackWf k σ' ε τ`.
Mirror of `HasTypeV.conv`/`HasType.conv` but on the **input** index of `StackWf`.
Proof: `cases` the head frame; each frame's input type appears once, re-close with
`.conv`/`TyEquiv.trans`. The `nil` case uses `StackWf.nil` at the converted type —
this is the only place the input index of `nil` moves, and it is sound because
`nil`'s in=out, so `σ' = τ` follows. *(If `nil`'s in/out coupling makes a direct
conversion awkward, the alternative is `record_get`-style: re-thread the equality at
the leaf; either way it is local.)*

The "`.perform` ⇒ unhandled" fact (no `Delimit` in a typed stack ⇒ `doPerformR`
returns `UnhandledEffect`) is **not needed for preservation** (preservation only
needs that *the successor named by `Reduce.perform`* is typed, and the substrate
already says that successor is `.wait op env kP`). It **is** needed for `progress`
(to show the well-typed performing state actually has a `.perform` move, not a
crash) — prove by induction on `StackWf`:
`stackWf_doPerformR_unhandled : StackWf k _ _ _ → ∀ acc, doPerformR l arg env k acc
= .error (.UnhandledEffect l arg)` (every frame is non-`Delimit`, so `doPerformR`
walks to `[]`). Now transparent because `doPerformR` is a total `def` (T5b).

## The `.reply` case — the one genuine design decision

`Reduce.reply` fires for an **arbitrary** reply value `v` (the oracle/world supplies
it): `.wait op env k → .run (.V v, env, k)`. Typing the successor needs
`HasTypeV v b` (reply type), but `v` is universally quantified — so the current
unconditional

```lean
preservation : MStateWf s τ ε → Reduce s μ s' → MStateWf s' τ ε
```

is **false** for `μ = .reply` unless `v` is constrained. This is the algebraic-effects
"replies are well-typed by the handler/world" contract. Three options:

1. **(Recommended) Condition the `.reply` case on a typed reply.** State
   preservation as: for `μ = .reply op v`, additionally require `HasTypeV v b` where
   `b` is the wait's reply type (or thread a `WellTypedReply` predicate). Closed
   `evalR` **never replies** (a `.perform` is terminal in `evalR`, returning
   `.effect`), so `soundness_value` over `evalR` is **unaffected** — this slice keeps
   it green untouched. The reply contract only bites at `runR`/`BehaviorsR` (T6/T7),
   where the oracle must be well-typed; record it there.
2. Bake a typing proof into `Reduce.reply` — rejected: pollutes the substrate, and
   the substrate must stay executable/oracle-agnostic.
3. Drop `.reply` from preservation's universal and prove a separate
   `preservation_reply` taking the typed-reply hypothesis — same content as (1),
   more theorems.

Go with **(1)**: the headline `preservation` keeps `.tau`/`.perform` unconditional
(real effect safety) and makes the `.reply` obligation explicit. Update the
`preservation` match: `| perform h => …(typed wait)…` and `| reply hv => …(hv :
HasTypeV v b)…`.

## `progress` after un-pin

Add the **effect-escape clause**: a well-typed non-value state steps (`.tau`), is a
terminal value, ends in a *sanctioned* crash, **or** suspends with `.perform op`
where `op ∈ ε` (via `EffContains`, using `stackWf_doPerformR_unhandled` +
`partialPerformNil` inversion). Never an *unsanctioned* crash, never a perform
outside `ε`. The `Perform`-partial frame cases in both `applyf`/`callwith` blocks:
the call reduces via `reducePerform` to `.perform` (a non-crash), so `Or.inl`
(it steps) — actually `.perform` is not a `reduce1Run = .tau` step; restate
`progress`'s disjunction to include the `.perform` outcome explicitly, mirroring how
`evalR` treats it as a (non-crash) suspension.

## Concrete execution order (next iteration)

1. `Typing.lean`: `HasType.perform`; `Generation.lean`: `inv_perform`,
   `hasType_expr_form` arm + all `rcases` extended by one.
2. `Runtime.lean`: `HasTypeV.partialPerformNil` + `conv` + `canonical_arrow` cases.
3. `Machine.lean`: `MStateWf` `wait` clause; `stackWf_conv_in`.
4. `Soundness.lean`: `stackWf_doPerformR_unhandled`; replace `not_perform` usage in
   the `perform` case with the typed-`wait` proof; condition the `reply` case on a
   typed reply (option 1); add the `Perform` cases to `reduceCall`-dispatch in
   `preservation_V` (the perform partial *does* perform — handle, don't exclude),
   `reduce1Run_done_value_typed` (perform ≠ done-value), and `progress` (effect
   escape). Keep `soundness_value` over `evalR` green (replies never occur there).
5. Re-green; `#print axioms`; `lake exe spec` (dynamics unchanged ⇒ still 104/104).

## Files
- Done: `Eyg/Types/EffRow.lean` (T5a), `Eyg/Semantics/Reduction.lean` `doPerformR`
  (T5b).
- To touch: `Typing.lean`, `Generation.lean`, `Runtime.lean`, `Machine.lean`,
  `Soundness.lean`.
