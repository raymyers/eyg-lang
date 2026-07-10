# G2 — universal readiness for the CLOSING case, GREEN (existing machinery)

Date: 2026-07-10. `Eyg/Types/G2Spike.lean`: `raiseScheme_U_eq_self`, `raiseCtx_U_eq_self`,
`genAtV_instantiate_lam_ready_universal`. No sorry, axioms `[propext, Classical.choice, Quot.sound]`.

## Result

The maintenance-proof attempt landed its first real theorem. **When a closure's captured context `Γ`,
`argTy`, `retTy`, and `εb` all have levels `< lvl'` (the body sublevel), readiness holds at ANY args**
— no `ArgsDisc`, no rule change, no per-args discipline:

```
genAtV_instantiate_lam_ready_universal :
  … → (∀ l ∈ retTy.levels, l < lvl') → (∀ l ∈ εb.levels, l < lvl') → CtxWfV lvl' Γ → …
  → HasType ℓ Γ ⟨lam⟩ ((genAtV ℓ (argTy→εb→retTy)).instantiateV args) ε
```

Mechanism: `hasType_fullRaise` (G16, landed) lifts the stored body's sublevel above the args by a
fresh offset `o`; because every level it moves is `< lvl'` (= the raise threshold), the closure's
advertised type is **unchanged** (`raiseTy_eq_self_of_levels_lt`, plus the two new `raiseScheme_U`/
`raiseCtx_U` self-fix lemmas). Then the floor keystone (`genAtV_instantiate_lam_ready_floor`)
discharges, since the raised sublevel `lvl'+o` exceeds every arg level.

## Coverage

The `< lvl'` premises hold for **all the standard combinators** — `\x.x`, `\x.\y.x`, `\x. let g=... in
g x`, etc. — whose `retTy` sits at the *generalized* level (`= ℓ < lvl'`). So route B closes
*universally* (all instantiations) for the entire combinator-polymorphism fragment, with existing
machinery. This subsumes G30 and every V1–V7 witness.

## What remains — the residual, now sharply isolated

The only gap is the **escaping-`retTy` case**: a closure whose `retTy` (or `εb`, or captured `Γ`)
carries a level `≥ lvl'`. That requires a *non-generalized* inner-lambda binder that escapes into
`retTy` at a level `≥` the sublevel — a structure that (a) I have not yet built as a well-typed,
readiness-*consumed* instance, and (b) if built, is where a raise would move `retTy` (the genuine
interleaving). This is the precise, isolated open question for full unconditional route B.

## Next

Try to build the escaping-`retTy` residual as a genuine consumed obligation (well-typed program whose
soundness needs readiness for such a closure at an arg forcing the raise past the escaping level).
Either it's unreachable (route B closes fully via this lemma + a coverage argument) or it's the real
residual (needs the type-fixed relabel or the decoupled rule — but *now* correctly motivated, unlike
the flawed V8). Compiler-first.
