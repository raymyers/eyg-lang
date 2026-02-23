# Rust Parser

Using OpenHands in a single-agent ralph loop.

## Running

```sh
openhands --headless -f rust-interpreter/plan/03-analysis/RALPH.md --json
```

Or with the TUI.

```sh
openhands --yolo -f rust-interpreter/plan/03-analysis/RALPH.md
```

```sh
stakpak --approve-all  --ignore-agents-md --async --prompt-file rust-interpreter/plan/03-analysis/RALPH.md
```

# Seeding the plan doc

```md
Study `packages/gleam_analysis` and populate `rust-interpreter/plan/03-analysis/PLAN.md` with milestone sections that have bullet task `* [ ]` lists. Goal is to implement a type-checker in new `eyg-analysis` create, test-first,  rust-interpreter. Share IR crate, CLI should be able to type-check with --type-check, either in parse or IR mode.
```
