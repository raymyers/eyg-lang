import eyg/parse/lexer_canonical as lexer
import eyg/parse/token as t
import gleam/io
import gleam/list
import gleam/string

pub fn main() {
  test_parens()
  test_braces()
  test_brackets()
  test_ops()
  test_eyg_ops()
  test_hash_comment()
  test_tabs_spaces()
  test_multiline()
  test_string_lit()
  test_number_lit()
  test_identifier()
  test_eyg_keywords()
}

fn print_tokens(tokens: List(#(t.Token, Int))) {
  list.each(tokens, fn(token_pair) {
    let #(token, _pos) = token_pair
    case token {
      t.String(value) -> io.println(t.to_canonical_string(token, "\"" <> value <> "\"", value))
      t.Number(value) -> io.println(t.to_canonical_string(token, value, value))
      t.Identifier(value) -> io.println(t.to_canonical_string(token, value, ""))
      _ -> io.println(t.to_canonical_string(token, t.to_string(token), ""))
    }
  })
}

fn test_parens() {
  io.println("=== Parens Test ===")
  let result = lexer.lex("(())")
  print_tokens(result.tokens)
  io.println("")
}

fn test_braces() {
  io.println("=== Braces Test ===")
  let result = lexer.lex("{{}}")
  print_tokens(result.tokens)
  io.println("")
}

fn test_brackets() {
  io.println("=== Brackets Test ===")
  let result = lexer.lex("[[]]")
  print_tokens(result.tokens)
  io.println("")
}

fn test_ops() {
  io.println("=== Ops Test ===")
  let result = lexer.lex("({*.,+-;|})")
  print_tokens(result.tokens)
  io.println("")
}

fn test_eyg_ops() {
  io.println("=== EygOps Test ===")
  let result = lexer.lex("!@:->||..")
  print_tokens(result.tokens)
  io.println("")
}

fn test_hash_comment() {
  io.println("=== HashComment Test ===")
  let result = lexer.lex("()# comment")
  print_tokens(result.tokens)
  io.println("")
}

fn test_tabs_spaces() {
  io.println("=== TabsSpaces Test ===")
  let result = lexer.lex("( ){\t}")
  print_tokens(result.tokens)
  io.println("")
}

fn test_multiline() {
  io.println("=== MultiLine Test ===")
  let result = lexer.lex("(\n)")
  print_tokens(result.tokens)
  io.println("")
}

fn test_string_lit() {
  io.println("=== StringLit Test ===")
  let result = lexer.lex("( \"Hello World\" )")
  print_tokens(result.tokens)
  io.println("")
}

fn test_number_lit() {
  io.println("=== NumberLit Test ===")
  let result = lexer.lex("42 3.14 0.5 1757.7378")
  print_tokens(result.tokens)
  io.println("")
}

fn test_identifier() {
  io.println("=== Identifier Test ===")
  let result = lexer.lex("foo_bar a b _")
  print_tokens(result.tokens)
  io.println("")
}

fn test_eyg_keywords() {
  io.println("=== EygKeywords Test ===")
  let result = lexer.lex("match perform handle True False Ok Error Cat")
  print_tokens(result.tokens)
  io.println("")
}