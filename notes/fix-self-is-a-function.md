---
name: fix self is a function
description: Why the !fix builtin is typed so the fixed point must be a function.
date: 2026-06-17
---

The `!fix` builtin is the Y-combinator. At runtime it calls the builder with
the recursive function itself as `self` (see `fixed` in
`packages/gleam_interpreter/src/eyg/interpreter/builtin.gleam`). The value
bound to `self` is a `Partial(Builtin("fixed"), [builder])`, i.e. always a
one-argument function.

The inference type used to be `((a) -> a) -> a`, leaving the fixed point `a`
open. That is unsound for EYG's eager `fixed`: it accepted
`!fix((x) -> { !int_add(x, 1) })`, inferred `Integer`, then crashed at runtime
because `x` (the recursive function) was added to an integer. The builtin is
now typed so that `a` is a function type `(arg) -> ret`, which is what `self`
actually is.

Trade-off: this also rejects degenerate-but-safe builders that ignore `self`
and return a non-function, e.g. `!fix((self) -> 5)`. Documented and sensible
recursion always returns a function (`!fix((self, n) -> ...)`), so requiring a
function fixed point matches real usage and keeps the type sound.
