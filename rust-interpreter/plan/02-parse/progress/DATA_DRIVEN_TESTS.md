# Data-Driven Test Fixtures — Milestone 8

## Done

- Created `testdata/parse_cases.json`: 46 parser test cases ported from all 22 Gleam parser test functions
  - Covers: literals, lambdas (single/multi/destructure), apply (single/chained/nested/multi-arg), let (simple/nested/sequential/field-access/destructure/shorthand/empty), lists (empty/elements/nested/complex/spread), records (empty/fields/complex/shorthand), overwrite (field/identity/shorthand), field access (simple/call/then-call), tagged, match (empty/subject/branches/open), perform (bare/applied), reference, named reference, comment, large integer
- Created `testdata/parse_error_cases.json`: 4 error cases (empty, whitespace-only, comment-only, unexpected token)
- Created `testdata/lex_cases.json`: 13 lexer test cases ported from all 8 Gleam lexer test functions + extras
  - Uses `drop_whitespace` filtered output with `["Tag:value", offset]` format
- Created `tests/parse_suite.rs`: data-driven test runner — parses source, serializes to dag-json, compares with expected JSON
- Created `tests/lex_suite.rs`: data-driven test runner — lexes source, filters whitespace, compares token tags + offsets
- Verified items 1-4 of Milestone 8 already satisfied by existing CLI tests (15) and interpreter tests (all pass)
- `make check` passes: 98 tests, clippy clean
