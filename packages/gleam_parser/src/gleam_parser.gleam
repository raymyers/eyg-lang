import argv
import dag_json
import eyg/interpreter/expression
import eyg/ir/dag_json as ir_dag_json
import eyg/ir/tree
import gleam/dynamic
import gleam/io
import gleam/list
import gleam/result
import gleam/string
import gleam_parser/ast
import gleam_parser/file_utils
import gleam_parser/lexer
import gleam_parser/parser
import gleam_parser/to_ir

@external(javascript, "./gleam_parser_ffi.mjs", "jsonStringify")
fn json_stringify(obj: dynamic.Dynamic) -> String

pub type Phase {
  Lex
  Parse
  IR
  Eval
}

pub type CliArgs {
  CliArgs(
    phase: String,
    source: String,
    from_file: Bool,
  )
}

pub type CliError {
  InvalidPhase(String)
  InvalidArgs(String)
  FileError(String)
  LexError(List(String))
  ParseError(List(parser.ParseError))
  IRError(String)
  InterpretError(String)
}

pub fn main() {
  let args = argv.load().arguments
  
  case args {
    [] -> {
      let welcome_message = "
🎯 EYG Parser CLI
=================

Welcome to the EYG Language Parser!

📋 Usage Options:
  • Use 'gleam run -m cli' for the full interactive CLI
  • Use run_with_args() function for programmatic access
  • See CLI_USAGE.md for complete documentation

🚀 Quick Start:
  gleam run -m cli -- lex -c \"42 + 3.14\"
  gleam run -m cli -- parse -f \"example.gleam\"
  gleam run -m cli -- ir -c \"let x = 42; x\"
"
      io.println(welcome_message)
      print_usage()
    }
    _ -> {
      io.println("⚠️  Note: For full CLI functionality, use 'gleam run -m cli'")
      io.println("This module provides the core parser functions.")
      print_usage()
    }
  }
}

pub fn run_with_args(phase: Phase, source: String, from_file: Bool) -> Result(String, CliError) {
  let phase_str = case phase {
    Lex -> "lex"
    Parse -> "parse"
    IR -> "ir"
    Eval -> "eval"
  }
  let args = CliArgs(phase: phase_str, source: source, from_file: from_file)
  run_pipeline(args)
}

fn run_pipeline(args: CliArgs) -> Result(String, CliError) {
  // Get source code
  use source <- result.try(get_source(args.source, args.from_file))
  
  // Run lexing phase
  use lex_result <- result.try(run_lex_phase(source))
  case args.phase {
    "lex" -> Ok(format_lex_result(lex_result))
    _ -> {
      // Continue to parsing phase
      use ast <- result.try(run_parse_phase(source))
      case args.phase {
        "parse" -> Ok(format_parse_result(ast))
        _ -> {
          // Continue to IR phase
          use ir_tree <- result.try(run_ir_phase(ast))
          case args.phase {
            "ir" -> {
              use ir_str <- result.try(format_ir_for_display(ir_tree))
              Ok(format_ir_result(ir_str))
            }
            "eval" -> run_interpret_phase(ir_tree)
            _ -> Error(InvalidPhase("Unknown phase"))
          }
        }
      }
    }
  }
}

fn get_source(source_or_file: String, from_file: Bool) -> Result(String, CliError) {
  case from_file {
    True -> {
      case file_utils.read_file(source_or_file) {
        Ok(content) -> Ok(content)
        Error(_) -> Error(FileError("Could not read file: " <> source_or_file))
      }
    }
    False -> Ok(source_or_file)
  }
}

fn run_lex_phase(source: String) -> Result(lexer.LexResult, CliError) {
  let result = lexer.lex(source)
  case result.errors {
    [] -> Ok(result)
    errors -> Error(LexError(errors))
  }
}

fn run_parse_phase(source: String) -> Result(ast.Expr, CliError) {
  case parser.parse(source) {
    Ok(ast) -> Ok(ast)
    Error(errors) -> Error(ParseError(errors))
  }
}

fn run_ir_phase(ast: ast.Expr) -> Result(tree.Node(List(Int)), CliError) {
  let ir_tree = to_ir.to_ir(ast)
  Ok(ir_tree)
}

fn format_ir_for_display(ir_tree: tree.Node(List(Int))) -> Result(String, CliError) {
  let binary_data = ir_dag_json.to_block(ir_tree)
  // Convert binary data to a readable JSON string
  case dag_json.decode(binary_data) {
    Ok(decoded) -> Ok(json_stringify(decoded))
    Error(err) -> Error(IRError("Failed to decode DAG JSON: " <> err))
  }
}

fn run_interpret_phase(ir_tree: tree.Node(List(Int))) -> Result(String, CliError) {
  // Execute the IR tree with an empty scope
  let result = expression.execute(ir_tree, [])
  
  case result {
    Ok(value) -> Ok("Result: " <> string.inspect(value))
    Error(err) -> Error(InterpretError("Evaluation failed: " <> string.inspect(err)))
  }
}

fn format_lex_result(result: lexer.LexResult) -> String {
  let tokens_str = 
    result.tokens
    |> list.map(fn(token_pair) { 
      let #(token, pos) = token_pair
      string.inspect(token) <> " at " <> string.inspect(pos)
    })
    |> string.join("\n")
  
  "Tokens:\n" <> tokens_str
}

fn format_parse_result(ast: ast.Expr) -> String {
  "AST:\n" <> ast.expr_to_string(ast)
}

fn format_ir_result(ir: String) -> String {
  "IR:\n" <> ir
}

pub fn format_error(error: CliError) -> String {
  case error {
    InvalidPhase(phase) -> "Invalid phase: " <> phase
    InvalidArgs(msg) -> "Invalid arguments: " <> msg
    FileError(msg) -> "File error: " <> msg
    LexError(errors) -> "Lexing errors: " <> string.join(errors, ", ")
    ParseError(errors) -> {
      let error_msgs = list.map(errors, fn(err) { err.message })
      "Parse errors: " <> string.join(error_msgs, ", ")
    }
    IRError(msg) -> "IR error: " <> msg
    InterpretError(msg) -> "Interpretation error: " <> msg
  }
}

fn print_usage() {
  io.println("Usage: gleam_parser [phase] [options]")
  io.println("")
  io.println("Phases:")
  io.println("  lex        - Tokenize source code")
  io.println("  parse      - Parse tokens into AST")
  io.println("  ir         - Convert AST to IR")
  io.println("  eval       - Interpret IR (not implemented)")
  io.println("")
  io.println("Options:")
  io.println("  -c \"code\"   - Specify source code directly")
  io.println("  -f file    - Read source code from file")
  io.println("")
  io.println("Examples:")
  io.println("  gleam_parser lex -c \"42 + 3\"")
  io.println("  gleam_parser parse -f example.gleam")
  io.println("  gleam_parser ir -c \"let x = 42; x + 1\"")
}
