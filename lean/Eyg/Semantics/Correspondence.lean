import Eyg.Semantics.Lts

/-!
# FBS ⟷ LTS correspondence (Milestone S3)

The fuel-indexed interpreter `eval` and the relational `eygLTS` describe the same
finite executions. Both are phrased over the *same* `step` function, so the
proofs never evaluate `step` on a concrete config — they case on `step c e k`
abstractly (see `progress/2026-06-16-partial-def-irreducibility.md`).

This file currently establishes **determinism**; soundness/completeness of `eval`
against `eygLTS.MTr` follow.
-/

namespace Eyg.Semantics

open Eyg.Interpreter
open Eyg.Ir
open Cslib

/-- `eygLTS` is deterministic: a state has at most one `μ`-derivative. Each
transition is pinned by the function `step` (for `tau`/`perform`) or by the
label's own value (for `reply`), so the target is unique. -/
instance instDeterministic {m : Type} [BEq m] : (eygLTS (m := m)).Deterministic where
  deterministic s μ s2 s3 h1 h2 := by
    cases h1 <;> cases h2 <;> simp_all

end Eyg.Semantics
