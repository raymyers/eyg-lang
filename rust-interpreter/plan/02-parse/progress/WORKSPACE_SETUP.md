# Milestones 1-6: Workspace, Token, Lexer, Parser, API

## Status: ALL COMPLETE

## Milestone 1: Workspace setup
- Cargo workspace: `crates/eyg-ir`, `crates/eyg-parser`, root crate
- IR types extracted to `eyg-ir`, root re-exports via `src/ir/mod.rs`

## Milestone 2: Token types
- `crates/eyg-parser/src/token.rs`: 27+ Token variants matching Gleam
- `drop_whitespace`, `drop_comments`, `Display`

## Milestone 3: Lexer
- `crates/eyg-parser/src/lexer.rs`: byte-level scanner, all token types
- Keyword boundary guard (e.g. `letter` → Name, not Let + `ter`)

## Milestones 4-6: Parser + Public API
- `crates/eyg-parser/src/parser.rs`: complete recursive-descent parser
- All expression forms: atoms, lambdas, application, let, records, lists, match
- Auto-currying, destructuring, field access, spread, open match
- `from_string()`, `block_from_string()` in `lib.rs`
- 62 parser tests + 26 existing = 88 total, all pass, clippy clean

## Next: Milestone 7 (CLI Integration)
