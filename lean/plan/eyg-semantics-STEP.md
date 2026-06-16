Perform these steps:

PLAN is `lean/plan/eyg-semantics.md`.

* Study PLAN and pick a next task.
* Check for pending git changes, your choice to finish then or reset.
* Attempt to complete a tested task slice.
  * If success: update PLAN and commit.
  * If failed: record in `lean/plan/progress/*.md` and reference in PLAN, commit only that plan and progress change.

# Tech Guidelines

This is a Lean project run with Nix. Sometimes agents get caught up spinning their wheels with proofs about the built-ins. Don't get stuck rabbit holes. Bail and leave notes if you need to, set yourself up for success next time.

# Research hints

This the referenced work on Functional Big-step Semantics
https://cakeml.org/esop16.pdf

Records and effects are both meant to be implementations of Extensible records with scoped labels
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf

Article on CEK machine interpreters and semantics.
https://matt.might.net/articles/cek-machines/

CESK machine is from Abstracting Abstract Machines

https://arxiv.org/pdf/1007.4446
