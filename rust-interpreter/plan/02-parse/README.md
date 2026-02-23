# Rust Parser

Using OpenHands in a single-agent ralph loop.

## Running

```sh
openhands --headless -f rust-interpreter/plan/02-parse/RALPH.md --json
```

# Seeding the plan doc

```md
Study packages/gleam_parser and populate rust-interpreter/plan/01-init/PLAN.md with  milestone sections that have bullet task `* [ ]` lists. Goal is to implement an equivelent will-tested parser in the rust-interpreter. Its own crate, sharing IR, CLI can invoke with --parse-ir (goes to IR json), or --parse-exec (passes to interpreter). Also add the Log effect available by default.
```
