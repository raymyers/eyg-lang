import gleam_parser/token.{type Token}
import gleam_parser/ast.{type Expr}
import gleam_parser/lexer
import gleam/list
import gleam/string
import gleam/float

pub type ParseError {
  ParseError(message: String, line: Int)
}

pub type Parser {
  Parser(tokens: List(Token), current: Int, errors: List(ParseError))
}

// Parse a string into an AST
pub fn parse(source: String) -> Result(Expr, List(ParseError)) {
  let lex_result = lexer.lex(source)
  case lex_result.errors {
    [] -> {
      let tokens = list.map(lex_result.tokens, fn(token_pair) { token_pair.0 })
      let parser = Parser(tokens, 0, [])
      case parse_expression(parser) {
        #(Ok(expr), final_parser) -> {
          case final_parser.errors {
            [] -> Ok(expr)
            errors -> Error(list.reverse(errors))
          }
        }
        #(Error(err), final_parser) -> Error(list.reverse([err, ..final_parser.errors]))
      }
    }
    errors -> {
      let parse_errors = list.map(errors, fn(err) { ParseError(err, 0) })
      Error(parse_errors)
    }
  }
}

// Get current token
fn peek(parser: Parser) -> Token {
  case list.drop(parser.tokens, parser.current) {
    [token, ..] -> token
    [] -> token.Eof
  }
}

// Check if we're at the end
fn is_at_end(parser: Parser) -> Bool {
  case peek(parser) {
    token.Eof -> True
    _ -> False
  }
}

// Advance to next token
fn advance(parser: Parser) -> Parser {
  case is_at_end(parser) {
    True -> parser
    False -> Parser(..parser, current: parser.current + 1)
  }
}

// Check if current token matches any of the given types
fn match_tokens(parser: Parser, types: List(Token)) -> #(Bool, Parser) {
  case list.any(types, fn(t) { token_matches(peek(parser), t) }) {
    True -> #(True, advance(parser))
    False -> #(False, parser)
  }
}

// Check if two tokens are of the same type (ignoring values)
fn token_matches(token1: Token, token2: Token) -> Bool {
  case token1, token2 {
    token.Number(_), token.Number(_) -> True
    token.String(_), token.String(_) -> True
    token.Identifier(_), token.Identifier(_) -> True
    token.LeftParen, token.LeftParen -> True
    token.RightParen, token.RightParen -> True
    token.LeftBrace, token.LeftBrace -> True
    token.RightBrace, token.RightBrace -> True
    token.Comma, token.Comma -> True
    token.Plus, token.Plus -> True
    token.Minus, token.Minus -> True
    token.Star, token.Star -> True
    token.Slash, token.Slash -> True
    token.EqualEqual, token.EqualEqual -> True
    token.BangEqual, token.BangEqual -> True
    token.Less, token.Less -> True
    token.LessEqual, token.LessEqual -> True
    token.Greater, token.Greater -> True
    token.GreaterEqual, token.GreaterEqual -> True
    token.Bang, token.Bang -> True
    token.And, token.And -> True
    token.Or, token.Or -> True
    _, _ -> False
  }
}

// Parse expression with precedence
fn parse_expression(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  parse_equality(parser)
}

// Parse equality expressions (== !=)
fn parse_equality(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  let #(left_result, parser1) = parse_comparison(parser)
  case left_result {
    Ok(left) -> parse_equality_rest(parser1, left)
    Error(err) -> #(Error(err), parser1)
  }
}

fn parse_equality_rest(parser: Parser, left: Expr) -> #(Result(Expr, ParseError), Parser) {
  let current_token = peek(parser)
  let #(matched, parser1) = match_tokens(parser, [token.BangEqual, token.EqualEqual])
  case matched {
    True -> {
      let operator = current_token
      let #(right_result, parser2) = parse_comparison(parser1)
      case right_result {
        Ok(right) -> {
          let binary = ast.Binary(left, operator, right, 1)
          parse_equality_rest(parser2, binary)
        }
        Error(err) -> #(Error(err), parser2)
      }
    }
    False -> #(Ok(left), parser)
  }
}

// Parse comparison expressions (< <= > >=)
fn parse_comparison(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  let #(left_result, parser1) = parse_term(parser)
  case left_result {
    Ok(left) -> parse_comparison_rest(parser1, left)
    Error(err) -> #(Error(err), parser1)
  }
}

fn parse_comparison_rest(parser: Parser, left: Expr) -> #(Result(Expr, ParseError), Parser) {
  let current_token = peek(parser)
  let #(matched, parser1) = match_tokens(parser, [token.Greater, token.GreaterEqual, token.Less, token.LessEqual])
  case matched {
    True -> {
      let operator = current_token
      let #(right_result, parser2) = parse_term(parser1)
      case right_result {
        Ok(right) -> {
          let binary = ast.Binary(left, operator, right, 1)
          parse_comparison_rest(parser2, binary)
        }
        Error(err) -> #(Error(err), parser2)
      }
    }
    False -> #(Ok(left), parser)
  }
}

// Parse term expressions (+ -)
fn parse_term(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  let #(left_result, parser1) = parse_factor(parser)
  case left_result {
    Ok(left) -> parse_term_rest(parser1, left)
    Error(err) -> #(Error(err), parser1)
  }
}

fn parse_term_rest(parser: Parser, left: Expr) -> #(Result(Expr, ParseError), Parser) {
  let current_token = peek(parser)
  let #(matched, parser1) = match_tokens(parser, [token.Minus, token.Plus])
  case matched {
    True -> {
      let operator = current_token
      let #(right_result, parser2) = parse_factor(parser1)
      case right_result {
        Ok(right) -> {
          let binary = ast.Binary(left, operator, right, 1)
          parse_term_rest(parser2, binary)
        }
        Error(err) -> #(Error(err), parser2)
      }
    }
    False -> #(Ok(left), parser)
  }
}

// Parse factor expressions (* /)
fn parse_factor(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  let #(left_result, parser1) = parse_unary(parser)
  case left_result {
    Ok(left) -> parse_factor_rest(parser1, left)
    Error(err) -> #(Error(err), parser1)
  }
}

fn parse_factor_rest(parser: Parser, left: Expr) -> #(Result(Expr, ParseError), Parser) {
  let current_token = peek(parser)
  let #(matched, parser1) = match_tokens(parser, [token.Slash, token.Star])
  case matched {
    True -> {
      let operator = current_token
      let #(right_result, parser2) = parse_unary(parser1)
      case right_result {
        Ok(right) -> {
          let binary = ast.Binary(left, operator, right, 1)
          parse_factor_rest(parser2, binary)
        }
        Error(err) -> #(Error(err), parser2)
      }
    }
    False -> #(Ok(left), parser)
  }
}

// Parse unary expressions (- !)
fn parse_unary(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  let current_token = peek(parser)
  let #(matched, parser1) = match_tokens(parser, [token.Bang, token.Minus])
  case matched {
    True -> {
      let operator = current_token
      let #(right_result, parser2) = parse_unary(parser1)
      case right_result {
        Ok(right) -> #(Ok(ast.Unary(operator, right, 1)), parser2)
        Error(err) -> #(Error(err), parser2)
      }
    }
    False -> parse_call(parser)
  }
}

// Parse function calls
fn parse_call(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  let #(expr_result, parser1) = parse_primary(parser)
  case expr_result {
    Ok(expr) -> parse_call_rest(parser1, expr)
    Error(err) -> #(Error(err), parser1)
  }
}

fn parse_call_rest(parser: Parser, expr: Expr) -> #(Result(Expr, ParseError), Parser) {
  let #(matched, parser1) = match_tokens(parser, [token.LeftParen])
  case matched {
    True -> {
      let #(args_result, parser2) = parse_arguments(parser1)
      case args_result {
        Ok(args) -> {
          let #(matched_close, parser3) = match_tokens(parser2, [token.RightParen])
          case matched_close {
            True -> {
              // Check if this should be a union constructor or function call
              let result_expr = case expr, args {
                ast.Variable(name, _), [single_arg] -> {
                  // If identifier starts with capital letter and has one argument, treat as union
                  case is_capitalized(name) {
                    True -> ast.Union(name, single_arg, 1)
                    False -> ast.Call(expr, args, 1)
                  }
                }
                _, _ -> ast.Call(expr, args, 1)
              }
              parse_call_rest(parser3, result_expr)
            }
            False -> #(Error(ParseError("Expected ')' after arguments", 1)), parser2)
          }
        }
        Error(err) -> #(Error(err), parser2)
      }
    }
    False -> #(Ok(expr), parser)
  }
}

// Check if a string starts with a capital letter
fn is_capitalized(name: String) -> Bool {
  case string.first(name) {
    Ok(first_char) -> {
      let code = string.to_utf_codepoints(first_char)
      case code {
        [codepoint] -> {
          let value = string.utf_codepoint_to_int(codepoint)
          value >= 65 && value <= 90  // A-Z
        }
        _ -> False
      }
    }
    Error(_) -> False
  }
}

// Parse function arguments
fn parse_arguments(parser: Parser) -> #(Result(List(Expr), ParseError), Parser) {
  case peek(parser) {
    token.RightParen -> #(Ok([]), parser)
    _ -> {
      let #(first_result, parser1) = parse_expression(parser)
      case first_result {
        Ok(first) -> parse_arguments_rest(parser1, [first])
        Error(err) -> #(Error(err), parser1)
      }
    }
  }
}

fn parse_arguments_rest(parser: Parser, args: List(Expr)) -> #(Result(List(Expr), ParseError), Parser) {
  let #(matched, parser1) = match_tokens(parser, [token.Comma])
  case matched {
    True -> {
      let #(expr_result, parser2) = parse_expression(parser1)
      case expr_result {
        Ok(expr) -> parse_arguments_rest(parser2, [expr, ..args])
        Error(err) -> #(Error(err), parser2)
      }
    }
    False -> #(Ok(list.reverse(args)), parser)
  }
}

// Parse primary expressions (literals, identifiers, grouping)
fn parse_primary(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  case peek(parser) {
    token.Number(value) -> {
      let parser1 = advance(parser)
      // The lexer stores numbers as "lexeme|literal", extract the literal part
      let parts = string.split(value, "|")
      case parts {
        [_, literal] -> {
          case float.parse(literal) {
            Ok(num) -> #(Ok(ast.Literal(ast.NumberValue(num), 1)), parser1)
            Error(_) -> #(Error(ParseError("Invalid number literal: " <> literal, 1)), parser1)
          }
        }
        _ -> #(Error(ParseError("Invalid number format: " <> value, 1)), parser1)
      }
    }
    
    token.String(value) -> {
      let parser1 = advance(parser)
      #(Ok(ast.Literal(ast.StringValue(value), 1)), parser1)
    }
    
    token.Identifier(name) -> {
      let parser1 = advance(parser)
      // Check if this is a builtin identifier (starts with !)
      case string.starts_with(name, "!") {
        True -> {
          let builtin_name = string.slice(name, 1, string.length(name) - 1)
          #(Ok(ast.Builtin(builtin_name, 1)), parser1)
        }
        False -> #(Ok(ast.Variable(name, 1)), parser1)
      }
    }
    
    token.LeftParen -> {
      let parser1 = advance(parser)
      let #(expr_result, parser2) = parse_expression(parser1)
      case expr_result {
        Ok(expr) -> {
          let #(matched, parser3) = match_tokens(parser2, [token.RightParen])
          case matched {
            True -> #(Ok(ast.Grouping(expr, 1)), parser3)
            False -> #(Error(ParseError("Expected ')' after expression", 1)), parser2)
          }
        }
        Error(err) -> #(Error(err), parser2)
      }
    }
    
    token.LeftBrace -> {
      let parser1 = advance(parser)
      let #(matched, parser2) = match_tokens(parser1, [token.RightBrace])
      case matched {
        True -> #(Ok(ast.EmptyRecord(1)), parser2)
        False -> #(Error(ParseError("Record parsing not yet implemented", 1)), parser1)
      }
    }
    
    _ -> #(Error(ParseError("Unexpected token", 1)), parser)
  }
}