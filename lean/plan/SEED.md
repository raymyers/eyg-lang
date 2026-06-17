Make a nix flake for lean and elan init a subproject including cslib

---

commit

---

lean/plan/eyg-difference-semantics.md packages/gleam_interpreter/src/eyg/interpreter/expression.gleam. Our goal is to implement a Lean interpreter for EYG, behaving just like the gleam interpreter, and probably code structured same since they are both pure languages. There will also be Functional Big Step semantics using the CSLib transition system. Create a plan for interpreter (including all tests passing from spec/) and a plan for the semantics. md files in lean/plan/ milestone sections with clear deliverables, task bullets.

---

Save my instructions to you in this convo to lean/plan/SEED.md with `---` lines between.

---

/goal Execute `lean/plan/eyg-interpreter-STEP.md` until PLAN complete.

---

Review the code diff from the recent commit range associated with PLAN `lean/plan/eyg-interpreter.md` completion. You are responsible for identifying any slop anti-patterns, overcoding, dumb stuff. Also confirm the claim that the tests pass. If there are any findings, append to PLAN as unfinished milestone. If it's a clean minimal solution we're good to go.

---

/goal Execute `lean/plan/eyg-interpreter-STEP.md` until PLAN complete.

---

/goal Execute `lean/plan/eyg-semantics-STEP.md` until PLAN complete.

---

Review the code diff from the recent commits since 8123d47f, which are associated with PLAN `lean/plan/eyg-semantics.md` completion. You are responsible for checking the claim that this semantics matches the interpreters (authoritative Gleam and Lean) and informal spec `spec/README.md`. 

Also identify any slop anti-patterns, overcoding, dumb stuff. If there are any findings, append to PLAN as unfinished milestone. If it's a sound minimal solution we're good to go.

---

commit plan changes

---

/goal Execute `lean/plan/eyg-semantics-STEP.md` until PLAN complete.

---

Study `lean/plan/eyg-semantics.md` and `lean/Eyg/Semantics`, create PLAN `lean/plan/eyg-type-soundness.md` to prove type soundness of the EYG semantics using Lean. This will involve Preservation and Progress theorems. Format as milestone sections with clear deliverables, `- [ ]` task bullets. Commit. Do you think you'll have what you need for this or are there more resources we should look up?

---

Based on your `## Do we have what we need?` section in PLAN `lean/plan/eyg-type-soundness.md`, retrieve the the desired docs and summarize the relevant information in md files in `lean/plan/references/*`, reference in PLAN. Commit.

---

Based on the current codebase and references, is PLAN `lean/plan/eyg-type-soundness.md` now set up for success? If you need to improve or streamline it (while keeping the same overall goal), you may do so and commit.

---

Is "Red" for reduce a convention? Would Reduce or something be clearer

---

commit plan changes

---

/goal Execute `lean/plan/eyg-type-soundness-STEP.md` until PLAN complete.

---

/goal Execute `lean/plan/eyg-type-soundness-STEP.md` until PLAN complete or you cannot make more progress.

---

Are you saying we can show EYG unsound?

---

Use nix flake to get the toolchain you need to run it

---

Add a new file in `lean/plan/progress` with an explanation of the `fix` soundness issue gleam code snippet showing the type checker and eval having those contradictory results. Should be self-contained besides including that eyg eval and analayzer.

---

Isn't fix (\x. int_add x 1) on a function type? Maybe this is just non-termination, not a bad crash?

---

There is a proposal to address this by changing `packages/gleam_analysis/src/eyg/analysis/inference/levels_j/contextual.gleam`
Before:
```
#("fix", t.Fun(t.Fun(q(0), q(1), q(0)), q(1), q(0))),
```
After:
```
#("fix", {
  let self = t.Fun(q(0), q(2), q(3))
  t.Fun(t.Fun(self, q(1), self), q(1), self)
}),
```
Does this address it? Confirm by running EYG tests with Nix. And then updating your Lean model.
---

/goal Execute `lean/plan/eyg-type-soundness-STEP.md` until PLAN complete or you cannot make more progress.

---
