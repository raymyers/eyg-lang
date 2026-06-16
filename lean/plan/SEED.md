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
