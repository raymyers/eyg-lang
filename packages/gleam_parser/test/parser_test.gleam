import gleam_parser/parser
import gleam_parser/ast
import gleam/io
import gleam/list
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

pub fn basic_parser_test() {
  // Test basic literal parsing
  let input = "42.0"
  case parser.parse(input) {
    Ok(expr) -> {
      let result = ast.expr_to_string(expr)
      io.println("Expected: 42.0")
      io.println("Actual: " <> result)
      result |> should.equal("42.0")
    }
    Error(errors) -> {
      io.println("Parse errors:")
      list.each(errors, fn(err) { io.println(err.message) })
      should.fail()
    }
  }
}

pub fn parser_tests_test() {
  // TODO: Read parser_tests.yaml and run all test cases
  // For now, just run a basic test
  basic_parser_test()
}