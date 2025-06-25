# Gleam Parser

A canonical lexer implementation for the EYG language, written in Gleam and based on the Go reference implementation.

## Features

- **Canonical tokenization**: Matches the reference Go implementation exactly
- **Comprehensive token support**: All EYG tokens including operators, keywords, literals
- **Robust error handling**: Proper error reporting for invalid input
- **Test-driven**: All tokenizer tests pass against canonical reference

## Token Types

### Literals
- `String`: String literals with escape sequence support
- `Number`: Numeric literals (integers and floats)
- `Identifier`: Variable and function names

### Operators
- Single character: `(`, `)`, `{`, `}`, `[`, `]`, `,`, `.`, `-`, `+`, `;`, `*`, `/`
- Multi-character: `->`, `..`, `||`, `!=`, `==`, `<=`, `>=`

### EYG-specific
- `@`: At symbol
- `:`: Colon
- `|`: Pipe
- `#`: Hash (for comments)
- `!`: Bang (including builtin functions like `!identifier`)

### Keywords
- `match`, `perform`, `handle`
- `and`, `or`, `not`, `if`, `else`, `nil`
- `_`: Underscore (special identifier)

## Usage

```gleam
import gleam_parser/lexer
import gleam_parser/token

let result = lexer.lex("(42 + 3.14)")
// Returns: LexResult with tokens and any errors
```

## Testing

Run the comprehensive test suite:

```bash
gleam test
```

The tests validate against the canonical tokenizer behavior defined in `tokenizer_tests.yaml`.

## Implementation Notes

- **Whitespace handling**: Whitespace and comments are skipped, not tokenized
- **Number parsing**: Supports both integers and floats with proper literal formatting
- **String escapes**: Full support for escape sequences (`\"`, `\\`, `\n`, `\t`, `\r`)
- **Comment support**: Both `#` hash comments and `//` line comments
- **Builtin functions**: Special handling for `!identifier` syntax

## Reference Implementation

This lexer is based on the canonical Go reference implementation found in the `go-ref` directory, ensuring compatibility with the official EYG language specification.