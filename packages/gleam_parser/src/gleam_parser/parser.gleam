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
    token.LeftBracket, token.LeftBracket -> True
    token.RightBracket, token.RightBracket -> True
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
    token.Colon, token.Colon -> True
    token.Dot, token.Dot -> True
    token.DotDot, token.DotDot -> True
    token.Perform, token.Perform -> True
    token.Equal, token.Equal -> True
    token.Semicolon, token.Semicolon -> True
    token.Pipe, token.Pipe -> True
    token.PipePipe, token.PipePipe -> True
    token.Handle, token.Handle -> True
    _, _ -> False
  }
}

// Parse expression with precedence
fn parse_expression(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  parse_assignment(parser)
}

// Parse assignment expressions (let bindings)
fn parse_assignment(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  let #(expr_result, parser1) = parse_equality(parser)
  case expr_result {
    Ok(expr) -> {
      // Check if this is a variable that could be assigned to
      case expr {
        ast.Variable(name, _) -> {
          let #(matched_equal, parser2) = match_tokens(parser1, [token.Equal])
          case matched_equal {
            True -> {
              let #(value_result, parser3) = parse_assignment(parser2)
              case value_result {
                Ok(value) -> {
                  // Check for semicolon and body
                  let #(matched_semi, parser4) = match_tokens(parser3, [token.Semicolon])
                  case matched_semi {
                    True -> {
                      let #(body_result, parser5) = parse_assignment(parser4)
                      case body_result {
                        Ok(body) -> #(Ok(ast.Var(expr, value, body, 1)), parser5)
                        Error(err) -> #(Error(err), parser5)
                      }
                    }
                    False -> #(Error(ParseError("Expected ';' after assignment", 1)), parser3)
                  }
                }
                Error(err) -> #(Error(err), parser3)
              }
            }
            False -> #(Ok(expr), parser1)
          }
        }
        _ -> #(Ok(expr), parser1)
      }
    }
    Error(err) -> #(Error(err), parser1)
  }
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
  // Check for function call
  let #(matched_paren, parser1) = match_tokens(parser, [token.LeftParen])
  case matched_paren {
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
    False -> {
      // Check for record access
      let #(matched_dot, parser_dot) = match_tokens(parser, [token.Dot])
      case matched_dot {
        True -> {
          case peek(parser_dot) {
            token.Identifier(field_name) -> {
              let parser_field = advance(parser_dot)
              let access_expr = ast.Access(expr, field_name, 1)
              parse_call_rest(parser_field, access_expr)
            }
            _ -> #(Error(ParseError("Expected field name after '.'", 1)), parser_dot)
          }
        }
        False -> #(Ok(expr), parser)
      }
    }
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
      // Check if this is a record or a block
      // If the next token is an identifier followed by colon, it's a record
      // Otherwise, it's a block
      case peek(parser1) {
        token.RightBrace -> {
          // Empty record
          let parser2 = advance(parser1)
          #(Ok(ast.EmptyRecord(1)), parser2)
        }
        token.Identifier(_) -> {
          // Look ahead to see if there's a colon (record) or not (block)
          let next_parser = advance(parser1)
          case peek(next_parser) {
            token.Colon -> parse_record(parser1)
            _ -> parse_block(parser1)
          }
        }
        _ -> parse_block(parser1)
      }
    }
    
    token.LeftBracket -> {
      let parser1 = advance(parser)
      parse_list(parser1)
    }
    
    token.Perform -> {
      let parser1 = advance(parser)
      let #(effect_result, parser2) = parse_expression(parser1)
      case effect_result {
        Ok(effect_expr) -> {
          // Extract effect name and arguments from the parsed expression
          case effect_expr {
            ast.Union(constructor, value, _) -> {
              // Convert single value to list of arguments
              #(Ok(ast.Perform(constructor, [value], 1)), parser2)
            }
            ast.Call(ast.Variable(name, _), args, _) -> {
              // Direct function call as effect
              #(Ok(ast.Perform(name, args, 1)), parser2)
            }
            ast.Variable(name, _) -> {
              // Effect with no arguments
              #(Ok(ast.Perform(name, [], 1)), parser2)
            }
            _ -> #(Error(ParseError("Invalid effect expression", 1)), parser2)
          }
        }
        Error(err) -> #(Error(err), parser2)
      }
    }
    
    token.Pipe -> {
      let parser1 = advance(parser)
      // This is a lambda: |params| { body }
      parse_lambda(parser1)
    }
    
    token.PipePipe -> {
      // This is a thunk: || { body }
      let parser1 = advance(parser)
      let #(matched_brace, parser2) = match_tokens(parser1, [token.LeftBrace])
      case matched_brace {
        True -> {
          // Check if this is an empty thunk
          case peek(parser2) {
            token.RightBrace -> {
              let parser3 = advance(parser2)
              #(Ok(ast.Thunk(ast.EmptyRecord(1), 1)), parser3)
            }
            _ -> {
              let #(body_result, parser3) = parse_expression(parser2)
              case body_result {
                Ok(body) -> {
                  let #(matched_close, parser4) = match_tokens(parser3, [token.RightBrace])
                  case matched_close {
                    True -> #(Ok(ast.Thunk(body, 1)), parser4)
                    False -> #(Error(ParseError("Expected '}' after thunk body", 1)), parser3)
                  }
                }
                Error(err) -> #(Error(err), parser3)
              }
            }
          }
        }
        False -> #(Error(ParseError("Expected '{' after thunk '||'", 1)), parser1)
      }
    }
    
    token.Handle -> {
      // Parse handle: handle Effect(handler, fallback)
      let parser1 = advance(parser)
      parse_handle(parser1)
    }
    
    _ -> {
      let current_token = peek(parser)
      #(Error(ParseError("Unexpected token: " <> string.inspect(current_token), 1)), parser)
    }
  }
}

// Parse record: {} or {field: value, field2: value2}
fn parse_record(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  // Check if it's an empty record
  let #(matched_empty, parser1) = match_tokens(parser, [token.RightBrace])
  case matched_empty {
    True -> #(Ok(ast.EmptyRecord(1)), parser1)
    False -> {
      // Parse record fields
      let #(fields_result, parser2) = parse_record_fields(parser, [])
      case fields_result {
        Ok(fields) -> {
          let #(matched_close, parser3) = match_tokens(parser2, [token.RightBrace])
          case matched_close {
            True -> #(Ok(ast.Record(fields, 1)), parser3)
            False -> #(Error(ParseError("Expected '}' after record fields", 1)), parser2)
          }
        }
        Error(err) -> #(Error(err), parser2)
      }
    }
  }
}

// Parse record fields: field: value, field2: value2
fn parse_record_fields(parser: Parser, fields: List(ast.RecordField)) -> #(Result(List(ast.RecordField), ParseError), Parser) {
  case peek(parser) {
    token.Identifier(field_name) -> {
      let parser1 = advance(parser)
      let #(matched_colon, parser2) = match_tokens(parser1, [token.Colon])
      case matched_colon {
        True -> {
          let #(value_result, parser3) = parse_expression(parser2)
          case value_result {
            Ok(value) -> {
              let field = ast.RecordField(field_name, value)
              let new_fields = [field, ..fields]
              
              // Check if there's a comma for more fields
              let #(matched_comma, parser4) = match_tokens(parser3, [token.Comma])
              case matched_comma {
                True -> parse_record_fields(parser4, new_fields)
                False -> #(Ok(list.reverse(new_fields)), parser3)
              }
            }
            Error(err) -> #(Error(err), parser3)
          }
        }
        False -> #(Error(ParseError("Expected ':' after field name", 1)), parser1)
      }
    }
    _ -> #(Error(ParseError("Expected field name in record", 1)), parser)
  }
}

// Parse list: [] or [1, 2, 3] or [0, ..items]
fn parse_list(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  // Check if it's an empty list
  let #(matched_empty, parser1) = match_tokens(parser, [token.RightBracket])
  case matched_empty {
    True -> #(Ok(ast.List([], 1)), parser1)
    False -> {
      // Parse list elements
      let #(elements_result, parser2) = parse_list_elements(parser, [])
      case elements_result {
        Ok(elements) -> {
          let #(matched_close, parser3) = match_tokens(parser2, [token.RightBracket])
          case matched_close {
            True -> #(Ok(ast.List(elements, 1)), parser3)
            False -> #(Error(ParseError("Expected ']' after list elements", 1)), parser2)
          }
        }
        Error(err) -> #(Error(err), parser2)
      }
    }
  }
}

// Parse list elements: 1, 2, 3 or 0, ..items
fn parse_list_elements(parser: Parser, elements: List(Expr)) -> #(Result(List(Expr), ParseError), Parser) {
  // Check for spread operator
  let #(matched_spread, parser_spread) = match_tokens(parser, [token.DotDot])
  case matched_spread {
    True -> {
      // Parse the spread expression
      let #(expr_result, parser_expr) = parse_expression(parser_spread)
      case expr_result {
        Ok(expr) -> {
          let spread_expr = ast.Spread(expr, 1)
          let new_elements = [spread_expr, ..elements]
          #(Ok(list.reverse(new_elements)), parser_expr)
        }
        Error(err) -> #(Error(err), parser_expr)
      }
    }
    False -> {
      // Parse regular expression
      let #(expr_result, parser_expr) = parse_expression(parser)
      case expr_result {
        Ok(expr) -> {
          let new_elements = [expr, ..elements]
          
          // Check if there's a comma for more elements
          let #(matched_comma, parser_comma) = match_tokens(parser_expr, [token.Comma])
          case matched_comma {
            True -> parse_list_elements(parser_comma, new_elements)
            False -> #(Ok(list.reverse(new_elements)), parser_expr)
          }
        }
        Error(err) -> #(Error(err), parser_expr)
      }
    }
  }
}

// Parse lambda: |x, y| { body }
fn parse_lambda(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  // Parse parameter list
  let #(params_result, parser1) = parse_lambda_params(parser, [])
  case params_result {
    Ok(params) -> {
      let #(matched_pipe, parser2) = match_tokens(parser1, [token.Pipe])
      case matched_pipe {
        True -> {
          let #(matched_brace, parser3) = match_tokens(parser2, [token.LeftBrace])
          case matched_brace {
            True -> {
              let #(body_result, parser4) = parse_expression(parser3)
              case body_result {
                Ok(body) -> {
                  let #(matched_close, parser5) = match_tokens(parser4, [token.RightBrace])
                  case matched_close {
                    True -> #(Ok(ast.Lambda(params, body, 1)), parser5)
                    False -> #(Error(ParseError("Expected '}' after lambda body", 1)), parser4)
                  }
                }
                Error(err) -> #(Error(err), parser4)
              }
            }
            False -> #(Error(ParseError("Expected '{' after lambda parameters", 1)), parser2)
          }
        }
        False -> #(Error(ParseError("Expected '|' after lambda parameters", 1)), parser1)
      }
    }
    Error(err) -> #(Error(err), parser1)
  }
}

// Parse lambda parameters: x, y
fn parse_lambda_params(parser: Parser, params: List(String)) -> #(Result(List(String), ParseError), Parser) {
  case peek(parser) {
    token.Identifier(param_name) -> {
      let parser1 = advance(parser)
      let new_params = list.append(params, [param_name])
      
      // Check what comes next
      case peek(parser1) {
        token.Comma -> {
          let parser2 = advance(parser1)
          parse_lambda_params(parser2, new_params)
        }
        token.Pipe -> {
          // End of parameters
          #(Ok(new_params), parser1)
        }
        _ -> #(Error(ParseError("Expected ',' or '|' after lambda parameter", 1)), parser1)
      }
    }
    token.Pipe -> {
      // No parameters, just return empty list
      #(Ok(params), parser)
    }
    token.Underscore -> {
      // Underscore parameter
      let parser1 = advance(parser)
      let new_params = list.append(params, ["_"])
      
      // Check what comes next
      case peek(parser1) {
        token.Comma -> {
          let parser2 = advance(parser1)
          parse_lambda_params(parser2, new_params)
        }
        token.Pipe -> {
          // End of parameters
          #(Ok(new_params), parser1)
        }
        _ -> #(Error(ParseError("Expected ',' or '|' after lambda parameter", 1)), parser1)
      }
    }
    _ -> #(Error(ParseError("Expected parameter name in lambda", 1)), parser)
  }
}

// Parse block: { stmt1; stmt2; ... }
fn parse_block(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  parse_block_statements(parser, [])
}

// Parse block statements
fn parse_block_statements(parser: Parser, statements: List(Expr)) -> #(Result(Expr, ParseError), Parser) {
  case peek(parser) {
    token.RightBrace -> {
      let parser1 = advance(parser)
      #(Ok(ast.Block(list.reverse(statements), 1)), parser1)
    }
    _ -> {
      let #(stmt_result, parser1) = parse_expression(parser)
      case stmt_result {
        Ok(stmt) -> {
          let new_statements = [stmt, ..statements]
          // Check for optional semicolon or newline
          case peek(parser1) {
            token.Semicolon -> {
              let parser2 = advance(parser1)
              parse_block_statements(parser2, new_statements)
            }
            _ -> parse_block_statements(parser1, new_statements)
          }
        }
        Error(err) -> #(Error(err), parser1)
      }
    }
  }
}

// Parse handle: handle Effect(handler, fallback)
fn parse_handle(parser: Parser) -> #(Result(Expr, ParseError), Parser) {
  // Expect effect name (identifier)
  case peek(parser) {
    token.Identifier(effect_name) -> {
      let parser1 = advance(parser)
      // Expect opening parenthesis
      let #(matched_paren, parser2) = match_tokens(parser1, [token.LeftParen])
      case matched_paren {
        True -> {
          // Parse handler lambda
          let #(handler_result, parser3) = parse_expression(parser2)
          case handler_result {
            Ok(handler) -> {
              // Expect comma
              let #(matched_comma, parser4) = match_tokens(parser3, [token.Comma])
              case matched_comma {
                True -> {
                  // Parse fallback lambda
                  let #(fallback_result, parser5) = parse_expression(parser4)
                  case fallback_result {
                    Ok(fallback) -> {
                      // Expect closing parenthesis
                      let #(matched_close, parser6) = match_tokens(parser5, [token.RightParen])
                      case matched_close {
                        True -> #(Ok(ast.Handle(effect_name, handler, fallback, 1)), parser6)
                        False -> #(Error(ParseError("Expected ')' after handle fallback", 1)), parser5)
                      }
                    }
                    Error(err) -> #(Error(err), parser5)
                  }
                }
                False -> #(Error(ParseError("Expected ',' after handle handler", 1)), parser3)
              }
            }
            Error(err) -> #(Error(err), parser3)
          }
        }
        False -> #(Error(ParseError("Expected '(' after handle effect name", 1)), parser1)
      }
    }
    _ -> #(Error(ParseError("Expected effect name after 'handle'", 1)), parser)
  }
}