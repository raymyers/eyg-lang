import gleam_parser/lexer

pub fn main() {
  // Main entry point for the gleam_parser package
  let result = lexer.lex("(42 + 3.14)")
  result
}
