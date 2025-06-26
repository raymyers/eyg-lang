import gleam/io
import gleam/list
import gleam/string
import gleam_parser/ast
import gleam_parser/file_utils
import gleam_parser/json_test_parser
import gleam_parser/parser
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

pub fn parser_tests_test() {
  case file_utils.read_file("parser_tests.json") {
    Ok(content) -> {
      case json_test_parser.parse_parser_tests(content) {
        Ok(json_test_parser.ParserTests(tests)) -> {
          run_json_tests(tests)
        }
        Ok(json_test_parser.TokenizerTests(_)) -> {
          io.println("Expected parser tests but got tokenizer tests")
          should.fail()
        }
        Error(err) -> {
          io.println("Failed to parse JSON: " <> string.inspect(err))
          should.fail()
        }
      }
    }
    Error(_) -> {
      io.println("Failed to read parser_tests.json")
      should.fail()
    }
  }
}

fn run_json_tests(tests: List(json_test_parser.TestCase)) -> Nil {
  list.each(tests, fn(test_case) {
    io.println("Running test: " <> test_case.name)
    case parser.parse(test_case.input) {
      Ok(expr) -> {
        let actual = ast.expr_to_string(expr)
        let expected = string.trim(test_case.expected)
        case actual == expected {
          True -> io.println("✓ " <> test_case.name <> " passed")
          False -> {
            io.println("✗ " <> test_case.name <> " failed")
            io.println("Expected: " <> expected)
            io.println("Actual: " <> actual)
            should.fail()
          }
        }
      }
      Error(err) -> {
        io.println(
          "✗ " <> test_case.name <> " failed to parse: " <> string.inspect(err),
        )
        should.fail()
      }
    }
  })
}

// Test a few basic cases manually for backup
pub fn manual_json_tests_test() {
  let test_cases = [
    json_test_parser.TestCase("Number", "42", "42.0"),
    json_test_parser.TestCase("String", "\"hello\"", "hello"),
    json_test_parser.TestCase("Addition", "2 + 3", "(+ 2.0 3.0)"),
    json_test_parser.TestCase("Multiplication", "4 * 6", "(* 4.0 6.0)"),
    json_test_parser.TestCase(
      "ComplexExpression",
      "2 + 3 * 4",
      "(+ 2.0 (* 3.0 4.0))",
    ),
    json_test_parser.TestCase(
      "GroupedExpression",
      "(2 + 3) * 4",
      "(* (group (+ 2.0 3.0)) 4.0)",
    ),
    json_test_parser.TestCase(
      "FunctionCallOneArg",
      "foo(42)",
      "(call foo 42.0)",
    ),
    json_test_parser.TestCase(
      "FunctionCallMultipleArgs",
      "foo(1, 2, 3)",
      "(call foo 1.0 2.0 3.0)",
    ),
    json_test_parser.TestCase("Subtraction", "5 - 2", "(- 5.0 2.0)"),
    json_test_parser.TestCase("Division", "8 / 2", "(/ 8.0 2.0)"),
    json_test_parser.TestCase("Comparison", "3 < 5", "(< 3.0 5.0)"),
    json_test_parser.TestCase("Equality", "1 == 1", "(== 1.0 1.0)"),
    json_test_parser.TestCase("Inequality", "1 != 2", "(!= 1.0 2.0)"),
    json_test_parser.TestCase("UnaryMinus", "-42", "(- 42.0)"),
    json_test_parser.TestCase("EmptyRecord", "{}", "{}"),
    json_test_parser.TestCase("Boolean", "True({})", "(union True {})"),
    json_test_parser.TestCase(
      "BuiltinCall",
      "!int_add(1, 2)",
      "(call (builtin int_add) 1.0 2.0)",
    ),
    json_test_parser.TestCase("LogicalNot", "!True({})", "(! (union True {}))"),
    json_test_parser.TestCase("FunctionCallNoArgs", "foo({})", "(call foo {})"),
    json_test_parser.TestCase(
      "NestedGrouping",
      "((1 + 2) * 3)",
      "(group (* (group (+ 1.0 2.0)) 3.0))",
    ),
    json_test_parser.TestCase(
      "MixedTypes",
      "\"hello\" == \"world\"",
      "(== hello world)",
    ),
    json_test_parser.TestCase(
      "Records",
      "{name: \"Alice\", age: 30}",
      "(record (field name Alice) (field age 30.0))",
    ),
    json_test_parser.TestCase(
      "RecordAccess",
      "alice.name",
      "(access alice name)",
    ),
    json_test_parser.TestCase("List", "[1, 2, 3]", "(list 1.0 2.0 3.0)"),
    json_test_parser.TestCase(
      "ListSpread",
      "[0, ..items]",
      "(list 0.0 (spread items))",
    ),
    json_test_parser.TestCase(
      "Effects",
      "perform Log(\"hello\")",
      "(perform Log hello)",
    ),
    json_test_parser.TestCase(
      "LetBinding",
      "x = 5; x + 10",
      "(let x 5.0 (+ x 10.0))",
    ),
    json_test_parser.TestCase(
      "Lambda",
      "|x, y| { !int_add(x, y) }",
      "(lambda (args x y) (call (builtin int_add) x y))",
    ),
    json_test_parser.TestCase(
      "Block",
      "{ perform Log(\"a\"); perform Log(\"b\") }",
      "(block (perform Log a) (perform Log b))",
    ),
    json_test_parser.TestCase(
      "ChainedCalls",
      "foo({})(bar)",
      "(call (call foo {}) bar)",
    ),
    json_test_parser.TestCase("Thunk", "|| {}", "(thunk {})"),
    json_test_parser.TestCase(
      "Handle",
      "handle Alert(|value, resume| { resume({}) }, |_| { {} })",
      "(handle Alert (lambda (args value resume) (call resume {})) (lambda (args _) {}))",
    ),
    json_test_parser.TestCase("NamedRef", "@std:1", "(named_ref std 1)"),
    json_test_parser.TestCase(
      "Match",
      "match value { Ok(x) -> x, Error(_) -> 0 }",
      "(match value (case (pattern Ok x) x) (case (pattern Error _) 0.0))",
    ),
  ]

  run_test_cases(test_cases)
}

fn run_test_cases(test_cases: List(json_test_parser.TestCase)) -> Nil {
  list.each(test_cases, run_single_test)
}

fn run_single_test(test_case: json_test_parser.TestCase) -> Nil {
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
