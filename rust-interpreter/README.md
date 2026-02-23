# EYG Rust Interpreter

A Rust port of the EYG interpreter and type-checker. Reads EYG programs as
dag-json IR or `.eyg` source, executes them using a CPS evaluator, and
optionally type-checks with Algorithm J + levels.

## Build

```sh
cargo build --release
```

## Usage

```sh
# Execute dag-json IR (default)
eyg-run program.json

# Execute EYG source
eyg-run --in eyg program.eyg

# Parse EYG source and dump dag-json IR
eyg-run --in eyg --dump-ir program.eyg

# Type-check a program (prints inferred type)
eyg-run --type-check program.json
eyg-run --in eyg --type-check program.eyg

# Execute with effect handlers
eyg-run program.json --effects handlers.json
```

### Input Formats

- `--in ir` (default): dag-json encoded IR tree
- `--in eyg`: EYG source text

### Modes

- **Execute** (default): run the program, print result to stdout
- `--dump-ir`: parse and emit dag-json IR to stdout
- `--type-check`: infer and print the top-level type; errors go to stderr (exit 1)

## Development

```sh
make check   # cargo test + clippy
make test    # cargo test
make lint    # cargo clippy -- -D warnings
```

Tests run the shared spec suites from `spec/evaluation/` (core, builtins, effects) and `spec/ir_suite.json`.
