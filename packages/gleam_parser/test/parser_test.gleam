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

pub fn addition_test() {
  let input = "2 + 3"
  case parser.parse(input) {
    Ok(expr) -> {
      let result = ast.expr_to_string(expr)
      io.println("Addition test - Expected: (+ 2.0 3.0)")
      io.println("Addition test - Actual: " <> result)
      result |> should.equal("(+ 2.0 3.0)")
    }
    Error(errors) -> {
      io.println("Addition parse errors:")
      list.each(errors, fn(err) { io.println(err.message) })
      should.fail()
    }
  }
}

pub fn multiplication_test() {
  let input = "4 * 6"
  case parser.parse(input) {
    Ok(expr) -> {
      let result = ast.expr_to_string(expr)
      io.println("Multiplication test - Expected: (* 4.0 6.0)")
      io.println("Multiplication test - Actual: " <> result)
      result |> should.equal("(* 4.0 6.0)")
    }
    Error(errors) -> {
      io.println("Multiplication parse errors:")
      list.each(errors, fn(err) { io.println(err.message) })
      should.fail()
    }
  }
}

pub fn precedence_test() {
  let input = "2 + 3 * 4"
  case parser.parse(input) {
    Ok(expr) -> {
      let result = ast.expr_to_string(expr)
      io.println("Precedence test - Expected: (+ 2.0 (* 3.0 4.0))")
      io.println("Precedence test - Actual: " <> result)
      result |> should.equal("(+ 2.0 (* 3.0 4.0))")
    }
    Error(errors) -> {
      io.println("Precedence parse errors:")
      list.each(errors, fn(err) { io.println(err.message) })
      should.fail()
    }
  }
}

pub fn grouping_test() {
  let input = "(2 + 3)"
  case parser.parse(input) {
    Ok(expr) -> {
      let result = ast.expr_to_string(expr)
      io.println("Grouping test - Expected: (group (+ 2.0 3.0))")
      io.println("Grouping test - Actual: " <> result)
      result |> should.equal("(group (+ 2.0 3.0))")
    }
    Error(errors) -> {
      io.println("Grouping parse errors:")
      list.each(errors, fn(err) { io.println(err.message) })
      should.fail()
    }
  }
}

pub fn function_call_test() {
  let input = "foo(42)"
  case parser.parse(input) {
    Ok(expr) -> {
      let result = ast.expr_to_string(expr)
      io.println("Function call test - Expected: (call foo 42.0)")
      io.println("Function call test - Actual: " <> result)
      result |> should.equal("(call foo 42.0)")
    }
    Error(errors) -> {
      io.println("Function call parse errors:")
      list.each(errors, fn(err) { io.println(err.message) })
      should.fail()
    }
  }
}

pub fn parser_tests_test() {
  // Run individual tests
  addition_test()
  multiplication_test()
  precedence_test()
  grouping_test()
  function_call_test()
}