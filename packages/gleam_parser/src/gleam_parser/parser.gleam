import gleam_parser/token.{type Token}
import gleam_parser/ast.{type Expr}
import gleam_parser/lexer
import gleam/list
import gleam/string
import gleam/float

pub type ParseError {
  ParseError(message: String, line: Int)
}

pub type ParseResult {
  ParseResult(expr: Expr, errors: List(ParseError))
}

// Parse a string into an AST
pub fn parse(source: String) -> Result(Expr, List(ParseError)) {
  let lex_result = lexer.lex(source)
  case lex_result.errors {
    [] -> {
      let tokens = list.map(lex_result.tokens, fn(token_pair) { token_pair.0 })
      parse_tokens(tokens)
    }
    errors -> {
      let parse_errors = list.map(errors, fn(err) { ParseError(err, 0) })
      Error(parse_errors)
    }
  }
}

// Parse a list of tokens into an AST
fn parse_tokens(tokens: List(Token)) -> Result(Expr, List(ParseError)) {
  case tokens {
    [] -> Error([ParseError("Empty input", 0)])
    [token.Number(value), ..] -> {
      // The lexer stores numbers as "lexeme|literal", extract the literal part
      let parts = string.split(value, "|")
      case parts {
        [_, literal] -> {
          case float.parse(literal) {
            Ok(num) -> Ok(ast.Literal(ast.NumberValue(num), 1))
            Error(_) -> Error([ParseError("Invalid number literal: " <> literal, 1)])
          }
        }
        _ -> Error([ParseError("Invalid number format: " <> value, 1)])
      }
    }
    [token.String(value), ..] -> Ok(ast.Literal(ast.StringValue(value), 1))
    [token.Identifier(name), ..] -> Ok(ast.Variable(name, 1))
    _ -> Error([ParseError("Unsupported token", 1)])
  }
}