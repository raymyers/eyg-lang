# G2 — generation-semantics question SETTLED (moot); escaping-`retTy` is NOT the wall

Date: 2026-07-10. Machine-checked (`Eyg/Types/G2Validation.lean`: `r2_escaping_defn`,
`r2_retTy_not_below_sublevel`, `r3_escaping_closure`, `r3_retTy_not_below_sublevel`,
`r4_escaping_closure_ready_high_arg`). No sorry, axioms `[propext, Quot.sound]`. Additive; validated
with `lake env lean` (independent of the mid-migration-WIP `Soundness.lean`).

## The task and what settled it

Finding (8) left one open question: does the *program's inference* force escaping schemes (binder
level `=` ambient) or is it free to produce disciplined ones (binder levels below the sublevel)? The
directive was to read `Generation.lean` for the binder-level assignment.

**`Generation.lean` is the inversion-lemma file, not an inference algorithm.** It inverts each
syntactic form *up to `TyEquiv`* (`inv_lambda`, `inv_let`, …) — the inputs to preservation. The
binder-level assignment lives in the **rule** `HasType.lam` (`Typing.lean:111-115`):

```
| lam : lvl ≤ lvl' → (∀ l ∈ argTy.levels, l < lvl') →
        HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb → …
```

So a binder's levels are `< lvl'` with `lvl'` a **free** choice `≥` the ambient `lvl` — **not** pinned
to the ambient. And `Generalization.lean`'s own docstring settles the meta-point: *"an algorithm that
produces such a scheme is the (separate, T8) inference layer"* — i.e. **there is no inference layer in
this repo**; the judgment is purely **declarative**, `HasType.var` quantifying over *arbitrary*
instantiation args.

**Therefore the "forced vs free" dichotomy is moot.** There is no inference to force anything; the
entry derivation to `soundness` is an *arbitrary* well-typed derivation, and the declarative system
admits **both** disciplined (R1) and escaping (R2) derivations of the same syntax.

## The escaping-`retTy` residual is genuinely constructible… (R2/R3)

R2 (`r2_escaping_defn`): the K-ish defn `\a. \w2. a`, typed with the inner binder `w2` at level `1`
`=` the outer lambda's sublevel `1`, so the outer `retTy = .var 1 0 → .var 0 0` carries level `1`
`≥` its own sublevel (`r2_retTy_not_below_sublevel`). R3 (`r3_escaping_closure`): the closure **value**
`Closure "a" (\w2.a) []` type-checks at `(genAtV 0 …).instantiateV [.integer]`; at it the
universal-closing lemma's `hretTy < lvl'` premise **fails** (`r3_retTy_not_below_sublevel`).

## …but it is NOT a readiness wall (R4) — the key correction

R4 (`r4_escaping_closure_ready_high_arg`): readiness for the *same* escaping closure at a **high** arg
`[.var 5 0]` (level 5 ≥ the stored sublevel 1) **is establishable** — by **re-typing** the body
`\w2.a` at a *fresh* sublevel `6` that dominates both the arg (5) and the *fixed* escaping level (1).
The escaping level is a bounded constant of the program text, so a dominating sublevel always exists.

So escaping-`retTy` per se is a **level choice at readiness-construction time**, not an obstruction.
The universal-closing lemma's `hretTy < lvl'` premise is a limitation of *that lemma* (it reuses the
stored sublevel via `hasType_fullRaise`), **not** a fundamental wall.

Caveat kept honest: R4's body has **no captured polymorphic structure**, so it re-types trivially. It
proves the escaping-`retTy` *shape* is not the wall; it does not prove the general re-typing lemma.

## Verdict — the true residual is narrower than "escaping `retTy`"

The genuine remaining wall is a closure body with **internal generalization** — a captured
polymorphic `let` whose gen level a *uniform* raise (`hasType_fullRaise`) cannot move while keeping the
advertised type fixed. That is precisely the **G16 two-modes / interleaving** structure (of which V8
was the minimal — but, per the V8 correction note, *non-consumed* — depth-2 target). It is neither the
escaping-`retTy` framing nor the flawed V8 readiness-value framing.

## Next

Build the G16 internal-generalization interleaving witness: a **consumed** closure whose body is
itself a `let_poly` whose generalization level interleaves with an escaping binder, instantiated so a
raise is forced. Test it against **both** routes — the raise route (`hasType_fullRaise`, known to hit
the two-modes wall) *and* the re-typing route R4 exercises. If re-typing survives internal
generalization, route B closes with existing machinery + a general re-typing lemma; if it blocks, the
entry-premise restriction (`ArgsDisc`, §2/§4) or the decoupled-`let_poly` rule (finding 5,
`G2DecoupledSpike.lean`) is required — a judgment change needing Phase-0 sign-off. Compiler-first (no
in-head level reasoning — that caused the corrected V8 error).
