---
date: 2026-06-19
milestone: G1 (Caveat 5) — session determination: full nested let-poly is a Ty-datatype rewrite, not an additive slice
status: NO FURTHER SINGLE-SESSION SLICE — re-confirmed the wall from the datatype; next-session scaffold below
---

# G1 — full nested let-poly: the wall is in the `Ty` datatype, so there is no additive micro-slice

## What this session established

Re-verified, from the code (not just prior notes), that the headline is at its
maximally-advanced clean state and that the remaining G1 gap is the documented
multi-session foundational rewrite — **and pinned *why* no additive slice exists**:

- **Green baseline confirmed.** `lake build` 1773 jobs; `lake exe spec` 104/104
  (FBS≡interpreter 104/104, ir round-trip 21/21, CID 21/21); `#print axioms soundness`
  and `soundness_evalR` = `[propext, Classical.choice, Quot.sound]` only; no `sorry`.
  The "no regression" Definition-of-done item holds.

- **The obstruction, re-derived from the code this session.** `hasType_subst`'s
  `let_poly` arm (`Substitution.lean:85`) is discharged *only vacuously* — `simp only
  [Tree.Node.noLambdaLet] at hnl` collapses the hypothesis to `False` because a `let`
  binding a `Lambda` makes `noLambdaLet` `False`. For the full nested case the arm must
  instead *fire* under the instantiation witness `σ_args` fed by
  `closure_typed_of_lambda_subst` (`Substitution.lean:148`) → `genAt_closure_ready`. But
  `σ_args` is a **down-shift** on `[n+arity, ∞)` (`v ↦ var (v−n−arity)`), not a
  `LevelMap`, so `genAt_substScheme`/`generalizesAt_subst` cannot apply, and
  `generalizes_subst_false` proves no arbitrary-`σ` discharge exists. Confirmed by
  reconstructing the concrete failing program
  `let f = \x. (let g = \y. … in g x) in …`: `g`'s fresh band `n_inner ≥ n+arity_f` is
  shifted down by `σ_args`, breaking the inner generalization. (Same finding as
  `2026-06-18-T6-let_poly-instantiation-levelmap-gap.md`, independently re-checked.)

- **Why this is NOT an additive foundation like `EffSub'`/`EffWeaken` (the sharper point).**
  `Scheme.lean:13–18`: EYG `Ty` is **binder-free by construction** — every `var i` is one
  flat de-Bruijn-**level** scope, quantification living only at the `Scheme` boundary.
  That flat-level encoding is *exactly* what makes a quantified var and an
  instantiation-fresh var indistinguishable (both high-numbered). The only fix is to give
  `Ty`/`Scheme` a representation that marks rigid/quantified vars distinctly (a `.rigid`
  constructor, named/co-de-Bruijn vars, or explicit Scheme-level binding). **Any such
  change edits the `Ty` constructor set**, which ripples through `subst`, `subst_subst`,
  `TyEquiv`, `Scheme.instantiate`, every `HasType`/`HasTypeV` rule, and the interpreter
  port + CID matching. You cannot land it "alongside the old, green" the way `EffSub'` was
  planned — the datatype change is not additive. Hence **no single-session tested slice is
  available**; the rewrite needs a multi-session budget that ends with a full re-green.

## Determination

G2 is DONE (refuted). G1 is **maximally advanced for single-session work**: `noLet →
noLambdaLet` landed (`2026-06-19-G1-noLambdaLet-relaxation-path.md`), Caveat 5 narrowed to
exactly the nested-*generalizable*-let case, report updated. The counterexample fork stays
expected-empty (value-restricted HM is sound). Further progress requires the `Ty`-datatype
rigid-marker rewrite — out of scope for a tested slice, per the plan's own PARTIAL note and
the "don't rabbit-hole" guideline. Bailing here with this scaffold rather than starting an
un-landable WIP that would leave the tree red.

## Addendum (2026-06-19, second session) — the *re-levelling* route is also non-additive

The plan's readiness-keystone item offered **two** forks, not one: resolve "via the level
discipline (re-levelled body typing on descent) **or** [the rigid marker]". This session
independently re-derived the obstruction from the code and checked the **re-levelling** fork too,
so the next session does not re-open it expecting a lighter path:

- The wall is `Scheme.instantiate args = subst σ_args d` with
  `σ_args = fun j => if j < arity then args.getD j else var (j − arity)` — a **down-shift** of the
  ambient region `[arity,∞) → [0,∞)`. `generalizesAt_subst` needs `LevelMap n σ` (fix `[n,∞)`); a
  down-shift fixes nothing above the prefix, so it is structurally **not** a `LevelMap`
  (`Generalization.lean:218`). That is the exact reason the `let_poly` arm of `hasType_subst`
  (`Substitution.lean:85`) stays vacuous via `noLambdaLet`.
- The down-shift is **intrinsic to the scheme encoding** (quantifiers occupy the bottom `[0,arity)`
  of the one flat scope, ambient pushed up to `[arity,∞)`). "Re-levelling instantiate" to map the
  quantifier prefix to a *fresh top* region instead would make the substitution ambient-into-ambient
  (a `LevelMap`), but it changes what `instantiate` returns (fresh vars, not `args`) and therefore
  the meaning of `Scheme` / every `GeneralizesAt` consumer — i.e. it edits the representation, not
  just a proof. **Not additive**, same verdict as the `.rigid` route. Neither fork is a tested slice.

- **Baseline re-verified fresh this session** (not inherited): `lake build` 1773 jobs; `lake exe
  spec` 104/104 (FBS≡interpreter 104/104, ir round-trip 21/21, CID 21/21); `#print axioms` for
  `soundness` and `soundness_evalR` = `[propext, Classical.choice, Quot.sound]`; no `sorry`. The
  "no regression" Definition-of-done item holds.

## Next-session execution scaffold (the rigid-marker rewrite)

Do this as a dedicated multi-session milestone, not a slice:

1. **Pick the representation.** Recommended: add `Ty.rigid (i : Nat)` (a distinguished
   quantified/skolem var) rather than reusing `var`. `subst` ignores `.rigid` (or substitutes
   a separate rigid-map); `instantiate` turns a scheme's quantified prefix into `.rigid` skolems
   for the *body-typing* obligation, while `var` stays the ambient/flex scope. This is what lets
   the inner generalization band survive an outer instantiation: skolems are not in `σ_args`'s
   domain, so the down-shift can't disturb them.
2. **First brick (the keystone to prove green before touching `hasType_subst`):** the
   substitution-stability lemma the flat-level version lacked — `instantiate` of a rigid-marked
   scheme commutes with an *arbitrary* `σ` (no `LevelMap` premise), because `σ` acts only on
   `var`, never on `.rigid`. This is the analogue of `generalizesAt_subst` but unconditional.
3. **Re-green the cascade** the relaxation already maps: `let_poly` arm of `hasType_subst`
   (now provable for arbitrary `σ`), `closure_typed_of_lambda_subst` (drop `noLambdaLet`),
   `genAt_closure_ready`, the engines (unchanged coupling), drop `noLambdaLet` from
   `HasType.let_poly`. Budget for re-touching every `Ty`-matching site.
4. **Sanity example:** `let f = \x. (let g = \y.y in g x) in f 1` (the `h` row of the report's
   Caveat-5 table) typing at the expected type — the term `noLambdaLet` rejects today.
