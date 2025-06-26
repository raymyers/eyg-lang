import gleam_parser/token.{type Token}
import gleam/list
import gleam/string
import gleam/int
import gleam/float

// Value represents a runtime value in the EYG language
pub type Value {
  StringValue(val: String)
  NumberValue(val: Float)
  BoolValue(val: Bool)
  NilValue
  BinaryValue(val: BitArray)
  UnionValue(constructor: String, value: Value)
  RecordValue(fields: List(#(String, Value)))
  ListValue(elements: List(Value))
  ErrorValue(message: String, line: Int)
}

// Expression represents an expression in the AST
pub type Expr {
  // Basic expressions
  Binary(left: Expr, operator: Token, right: Expr, line: Int)
  Grouping(expression: Expr, line: Int)
  Literal(value: Value, line: Int)
  Unary(operator: Token, right: Expr, line: Int)
  Variable(name: String, line: Int)
  
  // Control flow
  IfStatement(condition: Expr, then_branch: Expr, else_branch: Expr, line: Int)
  Block(statements: List(Expr), line: Int)
  
  // Functions and calls
  Call(callee: Expr, arguments: List(Expr), line: Int)
  Lambda(parameters: List(String), body: Expr, line: Int)
  Builtin(name: String, line: Int)
  
  // Data structures
  Record(fields: List(RecordField), line: Int)
  EmptyRecord(line: Int)
  List(elements: List(Expr), line: Int)
  Access(object: Expr, name: String, line: Int)
  
  // Pattern matching and unions
  Union(constructor: String, value: Expr, line: Int)
  ConstructorPattern(constructor: String, value: Expr, line: Int)
  Match(value: Expr, cases: List(MatchCase), line: Int)
  
  // Effects
  Perform(effect: String, arguments: List(Expr), line: Int)
  Handle(effect: String, handler: Expr, fallback: Expr, line: Int)
  
  // Advanced features
  NamedRef(module: String, index: Int, line: Int)
  Thunk(body: Expr, line: Int)
  Spread(expression: Expr, line: Int)
  Destructure(fields: List(RecordField), line: Int)
  Var(pattern: Expr, value: Expr, body: Expr, line: Int)
  Wildcard(line: Int)
}

pub type RecordField {
  RecordField(name: String, value: Expr)
}

pub type MatchCase {
  MatchCase(pattern: Expr, body: Expr)
}

// Convert AST to canonical string representation for testing
pub fn expr_to_string(expr: Expr) -> String {
  case expr {
    Binary(left, operator, right, _) -> {
      let op_str = case operator {
        token.Plus -> "+"
        token.Minus -> "-"
        token.Star -> "*"
        token.Slash -> "/"
        token.EqualEqual -> "=="
        token.BangEqual -> "!="
        token.Less -> "<"
        token.LessEqual -> "<="
        token.Greater -> ">"
        token.GreaterEqual -> ">="
        token.And -> "and"
        token.Or -> "or"
        _ -> "unknown_op"
      }
      "(" <> op_str <> " " <> expr_to_string(left) <> " " <> expr_to_string(right) <> ")"
    }
    
    Unary(operator, right, _) -> {
      let op_str = case operator {
        token.Minus -> "-"
        token.Bang -> "!"
        token.Not -> "not"
        _ -> "unknown_unary_op"
      }
      "(" <> op_str <> " " <> expr_to_string(right) <> ")"
    }
    
    Grouping(expression, _) -> 
      "(group " <> expr_to_string(expression) <> ")"
    
    Literal(value, _) -> value_to_string(value)
    
    Variable(name, _) -> name
    
    Call(callee, arguments, _) -> {
      let args_str = arguments
        |> list.map(expr_to_string)
        |> string.join(" ")
      case args_str {
        "" -> "(call " <> expr_to_string(callee) <> ")"
        _ -> "(call " <> expr_to_string(callee) <> " " <> args_str <> ")"
      }
    }
    
    Builtin(name, _) -> "(builtin " <> name <> ")"
    
    Union(constructor, value, _) -> 
      "(union " <> constructor <> " " <> expr_to_string(value) <> ")"
    
    ConstructorPattern(constructor, value, _) ->
      constructor <> " " <> expr_to_string(value)
    
    EmptyRecord(_) -> "{}"
    
    Record(fields, _) -> {
      let fields_str = fields
        |> list.map(fn(field) { 
          "(field " <> field.name <> " " <> expr_to_string(field.value) <> ")"
        })
        |> string.join(" ")
      "(record " <> fields_str <> ")"
    }
    
    List(elements, _) -> {
      let elements_str = elements
        |> list.map(expr_to_string)
        |> string.join(" ")
      case elements_str {
        "" -> "(list)"
        _ -> "(list " <> elements_str <> ")"
      }
    }
    
    Access(object, name, _) -> 
      "(access " <> expr_to_string(object) <> " " <> name <> ")"
    
    Lambda(parameters, body, _) -> {
      let params_str = string.join(parameters, " ")
      "(lambda (args " <> params_str <> ") " <> expr_to_string(body) <> ")"
    }
    
    Match(value, cases, _) -> {
      let cases_str = cases
        |> list.map(fn(case_) {
          "(case (pattern " <> expr_to_string(case_.pattern) <> ") " <> expr_to_string(case_.body) <> ")"
        })
        |> string.join(" ")
      "(match " <> expr_to_string(value) <> " " <> cases_str <> ")"
    }
    
    Perform(effect, arguments, _) -> {
      let args_str = arguments
        |> list.map(expr_to_string)
        |> string.join(" ")
      case args_str {
        "" -> "(perform " <> effect <> ")"
        _ -> "(perform " <> effect <> " " <> args_str <> ")"
      }
    }
    
    Handle(effect, handler, fallback, _) -> 
      "(handle " <> effect <> " " <> expr_to_string(handler) <> " " <> expr_to_string(fallback) <> ")"
    
    Block(statements, _) -> {
      let stmts_str = statements
        |> list.map(expr_to_string)
        |> string.join(" ")
      "(block " <> stmts_str <> ")"
    }
    
    Var(pattern, value, body, _) -> 
      "(let " <> expr_to_string(pattern) <> " " <> expr_to_string(value) <> " " <> expr_to_string(body) <> ")"
    
    Destructure(fields, _) -> {
      let fields_str = fields
        |> list.map(fn(field) { 
          "(field " <> field.name <> " " <> field.value |> expr_to_string <> ")"
        })
        |> string.join(" ")
      "(destructure " <> fields_str <> ")"
    }
    
    NamedRef(module, index, _) -> 
      "(named_ref " <> module <> " " <> int.to_string(index) <> ")"
    
    Thunk(body, _) -> 
      "(thunk " <> expr_to_string(body) <> ")"
    
    Spread(expression, _) -> 
      "(spread " <> expr_to_string(expression) <> ")"
    
    Wildcard(_) -> "_"
    
    IfStatement(condition, then_branch, else_branch, _) -> 
      "(if " <> expr_to_string(condition) <> " " <> expr_to_string(then_branch) <> " " <> expr_to_string(else_branch) <> ")"
  }
}

fn value_to_string(value: Value) -> String {
  case value {
    StringValue(val) -> val
    NumberValue(val) -> float.to_string(val)
    BoolValue(True) -> "true"
    BoolValue(False) -> "false"
    NilValue -> "nil"
    BinaryValue(_) -> "<binary>"
    UnionValue(constructor, val) -> constructor <> "(" <> value_to_string(val) <> ")"
    RecordValue(fields) -> {
      let fields_str = fields
        |> list.map(fn(field) { field.0 <> ": " <> value_to_string(field.1) })
        |> string.join(", ")
      "{" <> fields_str <> "}"
    }
    ListValue(elements) -> {
      let elements_str = elements
        |> list.map(value_to_string)
        |> string.join(", ")
      "[" <> elements_str <> "]"
    }
    ErrorValue(message, line) -> "Error(" <> message <> " at line " <> int.to_string(line) <> ")"
  }
}