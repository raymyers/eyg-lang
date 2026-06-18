---
date: 2026-06-18
milestone: T7 — `FixPreserves`/`FixPreservesB` DISCHARGED (user chose: narrow fix scheme to pure builder)
status: DONE — both changes landed; headline soundness now takes only `HasType [] prog τ ε`
---

> **✅ RESOLVED (same day).** The over-application gap below was closed by enforcing the
> strict-under-application invariant (`applied.length < arity`) on `HasTypeV.partialBuiltin`
> (bundled as `PartialBuiltinWf`, so destructuring keeps one hypothesis). With that **plus** the
> pure-builder narrowing, `fixPreserves`/`fixPreservesB` are *proved* and the headline
> `soundness`/`soundness_evalR`/`soundness_evalR_pure` are **unconditional** (commit "Discharge
> FixPreserves/FixPreservesB"). Axioms clean, no `sorry`, `lake build` 1772 + spec 104/104. The
> analysis below stands as the record of *why* both changes were needed.

# Discharging `FixPreserves` — the over-application gap (critical finding)

The user chose to **narrow `Builtins.scheme "fix"` to a pure builder** (`q1 → ∅`) to discharge
`FixPreserves`/`FixPreservesB`. The narrowing itself is correct, builds green, and handles the
**saturation/creation** case (`applied = []`): the `fix` partial's argument is then exactly
`partialFixed`'s pure builder `(self →⟨∅⟩ self)`, so the successor `fixed[builder]` (under the
pushed `Apply builder` frame) types via `partialFixed` + `StackWf.applyf` with `retTy = self`.

**But attempting the proof revealed `FixPreserves` is unsatisfiable as stated — independent of
builder purity** — so the narrowing alone cannot discharge it.

## The over-application gap (machine-checked)

`FixPreserves` quantifies over **all** `applied : List (Value m)`. For `fix`, an *over-applied*
partial `Partial (Builtin "fix") [b₀]` is **typeable**: `fix`'s scheme is
`(self →⟨∅⟩ self) →⟨∅⟩ self` with `self = q0 →⟨q2⟩ q3` an **arrow**, so peeling the builder `b₀`
leaves residual `self` — itself an arrow — and `HasTypeV.partialBuiltin` types
`Partial "fix" [b₀]` at `self = .fun A0 A2 A3`. (Contrast a base-codomain builtin like
`int_absolute : int → int`: peeling its arg leaves the non-arrow `int`, so `partialBuiltin`
rejects the over-applied form — over-application is auto-refuted there by the non-arrow codomain
via `hRna`. `fix` is the *only* schemed builtin whose return type is an arrow, so it is the only
one where over-application slips through.)

Applying that over-applied partial steps (machine-checked): `reduceCall (Partial "fix" [b₀]) arg
= reduceCallBuiltin "fix" [b₀, arg]` → length ≠ 1 → catch-all **accumulate** → `.tau (.V (Partial
"fix" [b₀, arg]), …)`. Preservation must type this successor at `retTy = A3` (the codomain `self`
was applied to). But `Partial "fix" [b₀, arg]` is typeable **only** via `partialBuiltin`, which
requires an **arrow** residual — and `A3` need not be an arrow (e.g. `fix (\self.\n. n) : Int→Int`
has `A3 = Int`). So the successor is **untypeable**, and `FixPreserves`'s `tau` clause is
unprovable for this case. Confirmed by `lake build` (the cons-case `partialBuiltin` application
type-mismatches exactly here).

The over-applied partial `Partial "fix" [b₀]` **never arises operationally** (the machine
saturates `fix` to `fixed[b₀]`, it never rests a 1-arg `fix` partial). So the statement is false
only on a *fiction* the typing admits — but the proof cannot use operational reachability, so the
fiction must be ruled out **in the typing**.

## Consequence: the existing `FixPreserves` hypothesis was unsatisfiable

`builtinAppPreserves (hfix : FixPreserves)` and `preservation_V` (line ~827, the
`canonical_arrow`→`partialBuiltin`→`hsat` path) invoke the obligation with **general** `applied`,
so the chain genuinely needs the cons case. The plan called `FixPreserves` a "satisfiable
(pure-builder-inhabitable) hypothesis"; this is **only true for `applied = []`** — the general
form is false, so the headline soundness was gated on an unsatisfiable premise for the
`fix`-containing fragment. (This was masked by leaving it an `axiom`-free *hypothesis*.)

## What a real discharge requires (the remaining work)

A **resting-only `fix` typing rule** — rule out the fictional over-applied `fix` partials in the
typing so `canonical_arrow` only yields `applied = []`:

- Add `id ≠ "fix"` to `HasTypeV.partialBuiltin` (so it no longer types any `fix` partial), and a
  dedicated `HasTypeV.partialFix` constructor for `Partial (Builtin "fix") []` **only**, typed at
  the full (narrowed) `fix` arrow.
- This is a `HasTypeV`-constructor cascade (comparable to `let_poly`): it breaks every `cases
  hv`/`cases hf` over `HasTypeV` (preservation_V Apply + its B-mirror, `canonical_arrow`, the
  no-bad-crash drivers, progress, ~10–15 case sites), each needing the new `partialFix` arm
  (fix-creation handling, the `applied = []` case worked out above) and the `id ≠ "fix"` field
  threaded through the `partialBuiltin` re-packaging sites.

With **both** changes — (1) the user's pure-builder narrowing (saturation) **and** (2) the
resting-only `partialFix` rule (over-application) — `FixPreserves`/`FixPreservesB` become provable
and the headline drops them. Neither alone suffices.

## Status
- Scheme narrowing + `fixPreserves` attempt **reverted** (build restored green, 1772 jobs, spec
  104/104). The narrowing is a correct prerequisite but pointless without (2), and committing it
  alone introduces analyzer-divergence with no payoff.
- This finding upgrades the `fix` discharge from "scheme narrowing (bounded edit)" to "scheme
  narrowing **+** a `partialFix` constructor cascade" — a focused milestone, not a quick edit.
