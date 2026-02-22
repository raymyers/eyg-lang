# Initial Rust interpreter

Using Auggie CLI in a single-agent ralph loop.

## Running

```sh
npx @augmentcode/auggie --instruction-file rust-interpreter/plan/01-init/RALPH.md --print
```

# Seeding the plan doc

The result of this was lightly edited into `rust-interpreter/plan/01-init/PLAN.md`.

```md
Branch, new folder rust-interpreter, within it create plan/PLAN.md with milestones sections and bulleted task lists for creating an equivelant Rust port of packages/gleam_interpreter, passing all tests. Should take IR.json as input for now, Converting to well-typed AST. Since you're converting from Gleam, immutability and match statements should usually be a direct translation.
```
