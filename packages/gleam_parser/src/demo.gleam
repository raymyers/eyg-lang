import gleam_parser/lexer
import gleam_parser/token as t
import gleam/io
import gleam/list
import gleam/int

pub fn main() {
  io.println("🎯 EYG Canonical Lexer Demo")
  io.println("===========================")
  
  let examples = [
    #("Basic Expression", "(42 + 3.14)"),
    #("String Literal", "\"Hello, World!\""),
    #("EYG Operators", "!@:->||.."),
    #("Keywords", "match perform handle"),
    #("Complex Expression", "match x { 42 -> \"found\" | _ -> \"not found\" }"),
    #("Builtin Function", "!print(\"Hello\")"),
    #("Comments", "# This is a comment\n(42)"),
  ]
  
  list.each(examples, fn(example) {
    let #(name, input) = example
    io.println("\n📝 " <> name <> ":")
    io.println("Input: " <> input)
    
    let result = lexer.lex(input)
    
    io.println("Tokens:")
    list.each(result.tokens, fn(token_pair) {
      let #(token, pos) = token_pair
      let token_str = case token {
        t.String(lexeme, literal) -> "STRING(\"" <> lexeme <> "\" -> \"" <> literal <> "\")"
        t.Number(lexeme, literal) -> "NUMBER(" <> lexeme <> " -> " <> literal <> ")"
        t.Identifier(value) -> "IDENTIFIER(" <> value <> ")"
        _ -> t.to_string(token)
      }
      io.println("  " <> int.to_string(pos) <> ": " <> token_str)
    })
    
    case result.errors {
      [] -> io.println("✅ No errors")
      errors -> {
        io.println("❌ Errors:")
        list.each(errors, fn(error) {
          io.println("  " <> error)
        })
      }
    }
  })
  
  io.println("\n🎉 Demo complete!")
}