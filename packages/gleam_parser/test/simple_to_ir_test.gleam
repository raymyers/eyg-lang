import eyg/ir/tree as ir
import gleam/io
import gleam_parser/ast
import gleam_parser/to_ir

pub fn main() {
  io.println("Testing to_ir function...")

  // Test variable conversion
  let source = ast.Variable("x", 1)
  let result = to_ir.to_annotated(source, [])
  let expected = ir.variable("x")

  case result |> ir.clear_annotation() == expected {
    True -> io.println("✓ Variable test passed")
    False -> io.println("✗ Variable test failed")
  }

  // Test integer conversion
  let source2 = ast.Literal(ast.NumberValue(42.0), 1)
  let result2 = to_ir.to_annotated(source2, [])
  let expected2 = ir.integer(42)

  case result2 |> ir.clear_annotation() == expected2 {
    True -> io.println("✓ Integer test passed")
    False -> io.println("✗ Integer test failed")
  }

  // Test string conversion
  let source3 = ast.Literal(ast.StringValue("hello"), 1)
  let result3 = to_ir.to_annotated(source3, [])
  let expected3 = ir.string("hello")

  case result3 |> ir.clear_annotation() == expected3 {
    True -> io.println("✓ String test passed")
    False -> io.println("✗ String test failed")
  }

  io.println("to_ir tests completed!")
}
