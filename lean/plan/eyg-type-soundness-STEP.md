Perform these steps:

PLAN is `lean/plan/eyg-type-soundness.md`.

* Study PLAN and pick a next task.
* Check for pending git changes, your choice to finish them or reset.
* Attempt to complete a tested task slice.
  * If success: update PLAN and commit.
  * If failed: record in `lean/plan/progress/*.md` and reference in PLAN, commit only that plan and progress change.

# Tech Guidelines

This is a Lean project run with Nix.

Sometimes agents get caught up spinning their wheels with proofs about the built-ins. Don't get stuck rabbit holes. Bail and leave progress notes if you need to, set yourself up for success next time.

The Lean code is a port of the Gleam EYG interpreter. Generally, the Gleam version should be considered authoritative. It's type analyzer may be useful in understanding the rule: `packages/gleam_analysis`.
