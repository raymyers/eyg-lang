
import gleam_parser/lexer

pub fn main() {
  let result = lexer.lex("|| {}")
  io.debug(result.tokens)
}
