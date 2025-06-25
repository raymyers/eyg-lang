import eyg/parse/lexer
import eyg/parse/token as t
import gleam/io
import gleam/list
import gleam/string
import gleam/int

pub fn main() {
  io.println("Testing canonical lexer in eyg-lang...")
  
  let result = lexer.lex("(42 + 3.14)")
  
  io.println("Tokens:")
  list.each(result.tokens, fn(token_pair) {
    let #(token, pos) = token_pair
    io.println("  " <> t.to_string(token) <> " at " <> int.to_string(pos))
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
}