---
date: 2026-06-16
milestone: T6 (let-generalization `gen`)
status: foundation DELIVERED (2 green commits); value lemma scoped with a sharpened boundary
---

# T6 `gen`: substitution infrastructure delivered + the value-lemma boundary

This session resolved the de Bruijn **convention blocker** from
`2026-06-16-T6-gen-scoping.md` and delivered the term-level substitution lemma, as
two independently-green, additive commits. It also surfaced a sharper boundary on
the *value*-level lemma than the original scoping anticipated.

## Delivered (green, axioms clean, `lake exe spec` 104/104)

### 1. Substitution infrastructure (`Eyg/Types/Scheme.lean`)
- `Ty.shift k` (renumber vars up by `k`) + `shift_zero` / `subst_shift`.
- **`Scheme.instantiate` switched to the shift convention**: an ambient (free)
  variable at body-index `i ≥ arity` denotes ambient-scope var `i - arity`. The
  quantifier prefix shifts the ambient scope up by `arity`; instantiation shifts it
  back down. For every *current* scheme (all closed builtins, or monomorphic) this
  yields an **identical normal form** — the whole project + spec stay green
  unchanged. The down-shift only bites once `gen` makes schemes with free ambient
  vars. This is the convention decision the scoping note demanded.
- `Scheme.substScheme σ` (apply an ambient `σ` to a scheme: fix the quantifiers,
  shift ambient substitutes up by `arity`) + `substScheme_mono`.
- `Scheme.subst_instantiate` (commutation for `args.length = arity`) and
  `Scheme.subst_instantiate'` (commutation for **any** `args`, via the witness
  `instArgs` that absorbs an under-applied scheme's leaked quantifier). The
  quantifier-prefix shift cancels: substitute shifted up by `arity`, instantiation
  shifts back down.
- `Scheme.scheme_substScheme` (builtin schemes are closed ⇒ `σ` fixes them).

### 2. Term-level substitution lemma (`Eyg/Types/Substitution.lean`, new)
- `substCtx σ Γ` + `substCtx_lookup` (lookup commutes with substitution).
- **`hasType_subst : HasType Γ e τ ε → HasType (substCtx σ Γ) e (subst σ τ) (subst σ ε)`**
  — direct induction on `HasType`; `var`/`builtin` re-instantiate the substituted
  scheme at `instArgs` via `subst_instantiate'`. This is the standard HM
  substitution/weakening result; it is **true and unconditional** (the term judgment
  has no value-presence side conditions).

## ⚠ The value-level lemma is FALSE in general (new finding)

The analogous runtime statement
```
hasTypeV_subst : HasTypeV v τ → HasTypeV v (Ty.subst σ τ)   -- FALSE for open rows
```
fails. The `HasTypeV.record` constructor requires *every* label in the row to be
present in the value's fields (`hpres`). If the row is open — `record {a:α | β}`
with `β` a **row variable** — then `RowContains` only yields the visible label `a`
(`β` being a bare `var` contributes no required labels), so `HasTypeV {a:=v}
(record {a:α | β})` holds. But `subst [β ↦ {b:int}]` makes the row
`{a:…, b:int}`, which now *requires* a field `b` the value lacks — so the
substituted typing is false. (Same for `Tagged` and open unions.)

Mechanically: a mutual `hasTypeV_subst`/`envWf_subst` would even get the right
induction hypotheses (the `record`/`partialMatch` constructors store their
field/branch typings as `∀`-functions, and Lean's recursor *does* provide an IH for
each output — verified), but the statement itself is unsound, so no proof exists.

## Resolution path (the proper, sound `gen` — next session)

The standard fix is the **value restriction**, and it lands cleanly here:

1. **Generalize only when `defn` is a syntactic value.** EYG's syntactic values
   evaluate (no reduction) to: `Closure` (arrow type), a literal (base type), an
   operator/builtin `Partial` (arrow type), `LinkedList []` (list type), or `unit`
   (`record .empty`, closed). **None** has an open record/union type with a
   generalizable row-tail variable — the non-empty `Record`/`Tagged` values that
   break the lemma arise only from *reducing applications*, which the value
   restriction excludes. So `hasTypeV_subst` holds for exactly the value forms `gen`
   can produce.
2. **`σ` fixes the captured context.** `gen Γ ε defnTy` generalizes only variables
   **not** free in `Γ`/`ε`, so the gen substitution `σ` is the identity on every var
   of the captured environment's context. Hence the `closure` case's `envWf_subst`
   obligation is trivial (`substCtx σ Γcap = Γcap`), side-stepping the need to
   substitute the *captured* env's (possibly record-valued) bindings.

So the remaining `gen` work is:
- a **value-restricted** `hasTypeV_subst` (literals/closure/partials/list-nil/unit
  forms; closure case discharged by "σ fixes Γcap", which needs a free-variable or
  "agrees-on-Γ" side condition threaded through);
- `gen Γ ε defnTy` (effect-safe close — mirror `close`/`close_eff`), a second
  `HasType.let_poly` rule (purely additive; keeps the monomorphic `let` and all
  existing theorems green), `inv_let_poly`;
- the `Assign`-frame preservation case for a polymorphic scheme: discharge
  `EnvWf.cons`'s `∀ args` via the value-restricted substitution lemma + `gen`'s
  identity-on-Γ property.

This is a focused slice (comparable to `fix`), now with the foundation in place and
the soundness argument pinned down. The two commits above are the durable progress;
the value lemma's restriction is the key design decision the next session starts from.
