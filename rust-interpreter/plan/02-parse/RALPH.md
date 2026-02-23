Execute these steps.

1. From the unfinished tasks in `rust-interpreter/plan/02-parse/PLAN.md`, choose a logical one to do next.
2. If a progress file is specified in the task, study it. Otherwise create one in `rust-interpreter/plan/02-parse/progress/` and reference in the plan file task.
3. Any pending git changes are from a previous attempt. your choice to finish or reset.
4. Do ONLY that task, and related automated tests.
5. Verify (including `cargo test`).
6. If complete: update PLAN to mark complete, commit.
7. If not complete: update progress file and bail.

## Progress files

Choose unique short descriptive names 2-4 words formatted `LIKE_THIS.md`. If you need to avoid collision, numbers are fine.

The audience will be a coding agent that needs to continue your task with little help, or understand the history of the execution. Err towards terse mention of past steps (unless something went wrong), more detail on current state.

## Tech Guidelines

The Gleam implementation in `packages/gleam_*` should be considered authoratative.

Makefile has test, lint (clippy) and check (doing both).

For tests prefer data-driven from cases in in `rust-interpreter/testdata/*.json` listing input/output for examples (or reuse `spec` folder from root project without modifying).
