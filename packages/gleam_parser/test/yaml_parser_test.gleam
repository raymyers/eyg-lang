import gleam_parser/parser
import gleam_parser/ast
import gleam_parser/token
import gleam_parser/lexer
import gleam/io
import gleam/list
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

pub type TestCase {
  TestCase(name: String, input: String, expected: String)
}

// Test a few basic cases manually since we don't have file I/O in tests
pub fn manual_yaml_tests_test() {
  let test_cases = [
    TestCase("Number", "42", "42.0"),
    TestCase("String", "\"hello\"", "hello"),
    TestCase("Addition", "2 + 3", "(+ 2.0 3.0)"),
    TestCase("Multiplication", "4 * 6", "(* 4.0 6.0)"),
    TestCase("ComplexExpression", "2 + 3 * 4", "(+ 2.0 (* 3.0 4.0))"),
    TestCase("GroupedExpression", "(2 + 3) * 4", "(* (group (+ 2.0 3.0)) 4.0)"),
    TestCase("FunctionCallOneArg", "foo(42)", "(call foo 42.0)"),
    TestCase("FunctionCallMultipleArgs", "foo(1, 2, 3)", "(call foo 1.0 2.0 3.0)"),
    TestCase("Subtraction", "5 - 2", "(- 5.0 2.0)"),
    TestCase("Division", "8 / 2", "(/ 8.0 2.0)"),
    TestCase("Comparison", "3 < 5", "(< 3.0 5.0)"),
    TestCase("Equality", "1 == 1", "(== 1.0 1.0)"),
    TestCase("Inequality", "1 != 2", "(!= 1.0 2.0)"),
    TestCase("UnaryMinus", "-42", "(- 42.0)"),
    TestCase("EmptyRecord", "{}", "{}"),
    TestCase("Boolean", "True({})", "(union True {})"),
    TestCase("BuiltinCall", "!int_add(1, 2)", "(call (builtin int_add) 1.0 2.0)"),
    TestCase("LogicalNot", "!True({})", "(! (union True {}))"),
    TestCase("FunctionCallNoArgs", "foo({})", "(call foo {})"),
    TestCase("NestedGrouping", "((1 + 2) * 3)", "(group (* (group (+ 1.0 2.0)) 3.0))"),
    TestCase("MixedTypes", "\"hello\" == \"world\"", "(== hello world)"),
  ]
  
  run_test_cases(test_cases)
}

fn run_test_cases(test_cases: List(TestCase)) -> Nil {
  list.each(test_cases, run_single_test)
}

fn run_single_test(test_case: TestCase) -> Nil {
  io.println("Running test: " <> test_case.name)
  case parser.parse(test_case.input) {
    Ok(expr) -> {
      let result = ast.expr_to_string(expr)
      case result == test_case.expected {
        True -> {
          io.println("✓ " <> test_case.name <> " passed")
        }
        False -> {
          io.println("✗ " <> test_case.name <> " failed")
          io.println("  Input: " <> test_case.input)
          io.println("  Expected: " <> test_case.expected)
          io.println("  Actual: " <> result)

          should.fail()
        }
      }
    }
    Error(errors) -> {
      io.println("✗ " <> test_case.name <> " failed with parse errors:")
      list.each(errors, fn(err) { io.println("  " <> err.message) })

      should.fail()
    }
  }
}