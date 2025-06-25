import eyg/parse/lexer
import eyg/parse/token as t
import gleam/io
import gleam/list
import gleam/string
import gleam/int

pub fn main() {
  io.println("Testing EYG lexer...")
  
  // Test basic tokenization
  let result1 = lexer.lex("let x = 42")
  io.println("Test 1 - 'let x = 42':")
  list.each(result1, fn(token) {
    let #(tok, pos) = token
    io.println("  " <> string.inspect(tok) <> " at " <> int.to_string(pos))
  })
  
  // Test grouping
  let result2 = lexer.lex("()")
  io.println("\nTest 2 - '()':")
  list.each(result2, fn(token) {
    let #(tok, pos) = token
    io.println("  " <> string.inspect(tok) <> " at " <> int.to_string(pos))
  })
  
  // Test string
  let result3 = lexer.lex("\"hello\"")
  io.println("\nTest 3 - '\"hello\"':")
  list.each(result3, fn(token) {
    let #(tok, pos) = token
    io.println("  " <> string.inspect(tok) <> " at " <> int.to_string(pos))
  })
  
  io.println("\nLexer tests completed successfully!")
}