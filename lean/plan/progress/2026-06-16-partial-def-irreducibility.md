---
date: 2026-06-16
milestone: S2 (carries into S3/S5)
status: constraint recorded (not a blocker)
---

# `step` is irreducible — concrete transitions can't use `rfl`

The interpreter's machine (`Eyg.Interpreter.State`) is built from `partial def`
(`eval`, `apply`, `call`, `callBuiltin`, `doPerform`, `perform`, `deep`). Lean
compiles `partial def` to an opaque, irreducible implementation, so the kernel
will **not** unfold `step c e k` on a concrete configuration. Consequences:

- `#guard`/`#eval` still work (they use the compiled evaluator), which is why the
  FBS `eval`/`run` `#guard`s and the spec harness pass fine.
- **`rfl`/`decide`/`simp` cannot evaluate `step` on a concrete config.** So a
  concrete `Step (.run cfg) .tau s'` or `.perform …` transition cannot be proved
  by `Step.tau rfl`. Only the `reply` rule (which references no `step`) admits
  direct concrete proofs.

## Why this does *not* block S3/S5

The FBS↔LTS correspondence never needs to *reduce* `step` on a literal config.
Both `eval` (a structural `def` over fuel that pattern-matches on `step c e k`)
and `Step` (whose `tau`/`perform` constructors are *hypotheses* `step c e k =
Loop …` / `= Break …`) refer to the **same** abstract `step c e k`. The proofs
proceed by `cases h : step c e k` and relate the two — see `eval_succ_mono` and
`progress`, which already do exactly this. So:

- S3 `eval_sound`/`eval_complete`/`Deterministic`: case on `step c e k`
  abstractly; never evaluate it.
- Examples/tests of concrete runs: use the executable `eval`/`run` (compiled),
  not the relational `Step`.

## If a concrete relational transition is ever needed

Options, in order of preference:
1. Keep concrete checks on the executable side (`eval`/`run`) and reserve `Step`
   for abstract metatheory (current approach).
2. Add `@[simp]` equation lemmas for `step`'s branches (the `def`-level ones are
   fine; the `partial def` callees would each need a characterising lemma).
3. Last resort: re-found the machine as structural/`WellFounded` `def`s with a
   fuel parameter so it reduces — large, not currently justified.
