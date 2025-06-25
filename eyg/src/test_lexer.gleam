import eyg/parse/lexer
import eyg/parse/token as t
import gleam/io

pub fn main() {
  // Test basic tokenization
  let result = lexer.lex("let x = 42")
  io.debug(result)
  
  // Test grouping
  let result2 = lexer.lex("()")
  io.debug(result2)
  
  // Test string
  let result3 = lexer.lex("\"hello\"")
  io.debug(result3)
  
  io.println("Lexer tests completed")
}