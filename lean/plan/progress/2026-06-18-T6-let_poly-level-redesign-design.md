---
date: 2026-06-18
milestone: T6 — `let_poly` resolution design: the de-Bruijn-level redesign (option 1)
status: DESIGN (resolves the path after `generalizes_subst_false`; scopes the structural milestone)
---

# `let_poly` resolution — the de-Bruijn-level redesign, designed

`generalizes_subst_false` (machine-checked, `Generalization.lean`) proves the declarative
`Generalizes` + `hasType_subst` route cannot carry `let_poly`: substitution can collide a
generalized variable into `FV(Γ)`. The resolution is the de-Bruijn-**level** discipline the PLAN
deferred. This note designs it and pins the *non-obvious crux* a naive attempt would miss.

## The level-indexed generalization predicate

Replace the context-fixing `Generalizes` with a **level-indexed** form that is substitution-stable
by construction:

```
GeneralizesAt (n : Nat) (s : Scheme) (d : Ty) : Prop :=
  ∀ args, ∃ σ', s.instantiate args = Ty.subst σ' d ∧ ∀ i, i < n → σ' i = .var i
```

Read: every instantiation of `s` is a `subst σ' d` whose witnessing `σ'` **fixes the ambient region
`[0,n)`** — so `σ'` only moves the *generalized* variables, which live at indices `≥ n`. If
`FV(Γ) ⊆ [0,n)` then `GeneralizesAt n s d → Generalizes s Γ d` (a `σ'` fixing `[0,n)` fixes `Γ`), so
`GeneralizesAt` strengthens the old predicate exactly along the freshness axis it was missing.

The invariant tying it to the judgment: **`n` is the number of type variables in scope** — every
`FV` in `Γ`, `τ`, `ε` is `< n`, and a `let_poly` at this point generalizes variables `≥ n` (the
fresh boundary). `hasType_subst`'s `σ` becomes a **level map**: it acts on the ambient `[0,n)` and is
the identity on the fresh region `[n,∞)`. Because `σ` fixes `≥ n`, it cannot collide a generalized
variable into the (substituted) context — `generalizes_subst` is recovered *with* the level premise.

## ⚠ The crux a naive option-1 attempt misses: NESTED `let_poly` levels

A `let_poly` whose bound lambda's **body contains another `let_poly`** is the hard case (and the one
`hasType_subst` must traverse). The inner `let_poly` is typed at a **deeper** level `n' > n` (more
binders in scope: the lambda's argument + any intervening lets). Its generalized variables live at
`≥ n'`.

The keystone substitution `σ'` (from `GeneralizesAt n s d`, instantiating the *outer* let) **fixes
`[0,n)` but acts on all of `[n,∞)`** — which *includes* the inner let's generalized region `[n',∞)`.
So a single global `σ'` that only knows the outer level `n` can still disturb the inner
generalization. For soundness the substitution applied while traversing into the inner `let_poly`
must fix `[0,n')`, not just `[0,n)`.

**Resolution:** the level must be threaded *structurally* through typing, increasing at every binder,
and `hasType_subst` must be **re-levelled as it descends**: entering a binder bumps `n`, and the
substitution restricted to that scope must fix the *new* `[0,n')`. Equivalently, generalization at
deeper lets uses strictly higher fresh indices, and substitution at level `n` is the identity on
`[n,∞)` — so descending into a level-`n'` subterm, the *same* `σ` already fixes `[n,∞) ⊇ [n',∞)`
**only if** `σ`'s images for `[0,n)` stay `< n` (the ambient-into-ambient condition `∀ i<n, FV(σ i) ⊆
[0,n)`). That condition is exactly what makes the inner `[n',∞)` untouched and the inner
`GeneralizesAt n'` preserved. The keystone's `σ'` (instantiation by ambient-scope types) **does**
satisfy `FV(σ' i) ⊆ [0,n)` in a well-formed program (a let-use instantiates with types over the
current ambient scope), so the route closes — but only when the level invariant is carried so that
"ambient scope" is a tracked `n`, not an existential.

This is why it is a **structural** change, not a lemma: `n` (or the `FV ⊆ [0,n)` well-formedness)
must live on the judgment and be threaded, so that the descent of `hasType_subst` knows the current
level and the ambient-into-ambient condition is available at each binder.

## Scope of the milestone (estimate)

1. **`HasTypeAt n Γ e τ ε`** (or a `WfBelow n` side-invariant on the existing `HasType`) carrying the
   level; thread `n` through every rule (binders bump it). Alternatively keep `HasType` and add a
   *well-formedness* relation `CtxWf n Γ` + `TyWf n τ` consumed only where generalization/substitution
   happen — **less invasive**; evaluate first. The minimal-blast-radius choice is the key design call.
2. **`GeneralizesAt`** + its substitution-stability lemma (level map `σ`: `∀i≥n, σ i = var i` and
   `∀i<n, FV(σ i) ⊆ [0,n)`) → `GeneralizesAt n (substScheme σ s) (subst σ d)`. Uses `subst_instantiate'`
   (already proven). This is the standalone technical heart; **provable in isolation** (attempt it
   first as a green foundation), modulo the ∀-args quantifier bookkeeping.
3. **`hasType_subst`** re-stated with the level-map premise; its `let_poly` arm discharges via (2).
   Re-green its existing callers (they pass level maps — verify the keystone's `σ` qualifies).
4. The `let_poly` machine coupling from `2026-06-18-T6-let_poly-coupling-design-sharpened.md`
   (`StackWfV`, carried readiness, both preservation engines) — **unchanged in shape**, now on top of
   the level-aware `Generalizes`.

Items 1–3 are the new structural prerequisite (the genuine multi-session research milestone); item 4
is the previously-designed coupling. The minimal-blast-radius decision in (1) — full level-indexed
judgment vs. a `WfBelow n` side-invariant — should be made first, as it determines whether both
preservation engines must be re-typed or merely gain a side-premise.

## Status
- `generalizes_subst_false` proves the redesign is mandatory (committed, green).
- This note designs the redesign and pins the nested-level crux (the part a naive "add a level"
  attempt gets wrong). Next session: make the (1) blast-radius call, then land (2) as a standalone
  green lemma before threading.
- Tree green throughout: `lake build` 1772 + `lake exe spec` 104/104.
