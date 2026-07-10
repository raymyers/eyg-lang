# G2 — the interleaving wall CONSTRUCTED (W2); prove-or-refute closed

Date: 2026-07-10. Machine-checked (`Eyg/Types/G2Validation.lean`: `w2_interleave_body`,
`w2_interleave_retTy_not_below_sublevel`, `w2_interleave_closure`). No sorry, axioms
`[propext, Quot.sound]`. Additive; validated with `lake env lean` (independent of the
mid-migration-WIP `Soundness.lean`).

## What this note settles

The W1 correction note flagged the escaping/interleaving residual as "not yet constructed as a genuine
blocked case — route B may close more broadly than feared." Findings (9) (R2–R4) then showed the
*escaping-`retTy`* framing is **not** the wall (readiness re-establishes by re-typing at a fresh
dominating sublevel). This note constructs the **true** wall — the **interleaving** case — and closes
the prove-or-refute.

## The actual readiness keystone is substitution/raise-based

`genAtV_closure_ready_value_node` (`Substitution.lean:168`) is the live readiness keystone. It takes
the **stored** body derivation (`inv_lambda_noGenAt`) and transports it via `hasType_substAt`
(substitution) — with the old args bound `l = 0 ∨ l = lvl`. The floor keystone
(`genAtV_instantiate_lam_ready_floor`) widens the bound to `l < lvl'`; the universal-closing lemma
(`genAtV_instantiate_lam_ready_universal`) covers *any* args when `retTy`/`argTy`/`εb`/`Γ` are all
`< lvl'`, by lifting the stored sublevel with `hasType_fullRaise`. **All three transport the stored
derivation.** None re-derives from scratch.

## W2 — the natural interleaving entry derivation

`w2_interleave_body`: V8's closure body `let g = \y.y in \w. g x`, typed with

- `g` generalized at its **low natural ambient** `3` (`genAtV 3 (β→β)`), and
- the `\w` binder chosen at level **3** — coinciding with `g`'s gen level, escaping into `retTy`.

Result: closure sublevel `3`, `retTy = .var 3 0 → .var 2 0` with level `3 =` sublevel `3`
(`w2_interleave_retTy_not_below_sublevel`). The closure value type-checks (`w2_interleave_closure`).
Per finding (9) the entry to `soundness` is an *arbitrary* well-typed derivation, so this interleaving
derivation is admissible.

## Why the keystone cannot discharge it — both routes fail

- **Universal-closing lemma:** its `∀ l ∈ retTy.levels, l < lvl'` premise **fails** (3 ⊀ 3).
- **Raise route:** to move `g`'s gen level `3`, the raise threshold `t ≤ 3` also moves `retTy`'s
  binder level `3`, changing the advertised type; any `t > 3` strands `g` at `3` where the
  instantiation `[.var 2 0]` still collides. `v8_moving_g_moves_retTy` / `v8_fixing_retTy_strands_g`
  pin this arithmetic — **now anchored to a *constructed* entry derivation**, not a hypothetical.

Yet readiness is **semantically true**: the SAME closure value is typeable with `g` re-generalized
fresh at `5` (`v8`), where `retTy {3,2} < 5` is disciplined. The two derivations genuinely differ, and
the substitution/raise keystone transports the stored (interleaving) one — it cannot reach the fresh
one.

## Verdict — prove-or-refute closed

The interleaving residual is **real and reachable** as an arbitrary entry, and the current
substitution/raise keystone **cannot** discharge its readiness. So unconditional `soundness` over
*unrestricted* entry derivations is **not** achievable with the existing machinery. Two ways forward:

1. **Entry-premise restriction (sign-off-ready).** Replace `soundness`'s entry premise (`HasTypeRT h`)
   with `ArgsDisc … h` (§2/§4) or migrate `let_poly` to a decoupled/chosen-fresh `gl` (finding 5,
   `G2DecoupledSpike.lean`). Both confine entry to *disciplined* derivations (`retTy < lvl'` at every
   closure), which the **universal-closing lemma already covers**. This is a judgment change of the
   authorized G20 spec-refinement class — needs Phase-0 sign-off.
2. **Re-derivation / structural-relabel keystone (higher risk).** Replace the substitution/raise
   transport with a keystone that *re-derives* the closure body at fresh levels (as `v8`/R4 do by
   hand). This is exactly the G16 type-fixed structural relabel; W2 + the two `v8_*` lemmas show no
   *threshold raise* provides it, so it would be genuinely new mathematics (essentially the unbuilt
   inference layer). No rule change if it lands.

## Next

Take Phase 0 to the user: sign off on the entry-premise restriction / decoupled-`let_poly` (path 1),
or authorize an attempt at the re-derivation keystone (path 2) before committing to the rule change.
Path 1 is the lower-risk close; the universal-closing lemma + floor keystone already discharge the
disciplined fragment it confines to. Compiler-first throughout.
