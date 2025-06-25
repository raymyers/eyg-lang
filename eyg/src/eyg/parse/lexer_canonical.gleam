import eyg/parse/token as t
import gleam/string
import gleam/list
import gleam/result
import gleam/float

pub type LexResult {
  LexResult(tokens: List(#(t.Token, Int)), errors: List(String))
}

pub fn lex(source: String) -> LexResult {
  do_lex(source, 0, [], [])
}

fn do_lex(source: String, at: Int, tokens: List(#(t.Token, Int)), errors: List(String)) -> LexResult {
  case string.slice(source, at, 1) {
    "" -> LexResult(list.reverse([#(t.Eof, at), ..tokens]), errors)
    
    // Grouping
    "(" -> do_lex(source, at + 1, [#(t.LeftParen, at), ..tokens], errors)
    ")" -> do_lex(source, at + 1, [#(t.RightParen, at), ..tokens], errors)
    "{" -> do_lex(source, at + 1, [#(t.LeftBrace, at), ..tokens], errors)
    "}" -> do_lex(source, at + 1, [#(t.RightBrace, at), ..tokens], errors)
    "[" -> do_lex(source, at + 1, [#(t.LeftBracket, at), ..tokens], errors)
    "]" -> do_lex(source, at + 1, [#(t.RightBracket, at), ..tokens], errors)
    
    // Single character operators
    "*" -> do_lex(source, at + 1, [#(t.Star, at), ..tokens], errors)
    "," -> do_lex(source, at + 1, [#(t.Comma, at), ..tokens], errors)
    "+" -> do_lex(source, at + 1, [#(t.Plus, at), ..tokens], errors)
    ";" -> do_lex(source, at + 1, [#(t.Semicolon, at), ..tokens], errors)
    "@" -> do_lex(source, at + 1, [#(t.At, at), ..tokens], errors)
    ":" -> do_lex(source, at + 1, [#(t.Colon, at), ..tokens], errors)
    
    // Multi-character operators
    "." -> {
      case string.slice(source, at + 1, 1) {
        "." -> do_lex(source, at + 2, [#(t.DotDot, at), ..tokens], errors)
        _ -> do_lex(source, at + 1, [#(t.Dot, at), ..tokens], errors)
      }
    }
    
    "-" -> {
      case string.slice(source, at + 1, 1) {
        ">" -> do_lex(source, at + 2, [#(t.Arrow, at), ..tokens], errors)
        _ -> do_lex(source, at + 1, [#(t.Minus, at), ..tokens], errors)
      }
    }
    
    "!" -> {
      case string.slice(source, at + 1, 1) {
        "=" -> do_lex(source, at + 2, [#(t.BangEqual, at), ..tokens], errors)
        _ -> {
          // Check for builtin function !identifier
          let next_char = string.slice(source, at + 1, 1)
          case is_lowercase_letter(next_char) {
            True -> {
              let #(identifier, new_at) = read_identifier(source, at + 1, "")
              do_lex(source, new_at, [#(t.Identifier("!" <> identifier), at), ..tokens], errors)
            }
            False -> do_lex(source, at + 1, [#(t.Bang, at), ..tokens], errors)
          }
        }
      }
    }
    
    "=" -> {
      case string.slice(source, at + 1, 1) {
        "=" -> do_lex(source, at + 2, [#(t.EqualEqual, at), ..tokens], errors)
        _ -> do_lex(source, at + 1, [#(t.Equal, at), ..tokens], errors)
      }
    }
    
    "<" -> {
      case string.slice(source, at + 1, 1) {
        "=" -> do_lex(source, at + 2, [#(t.LessEqual, at), ..tokens], errors)
        _ -> do_lex(source, at + 1, [#(t.Less, at), ..tokens], errors)
      }
    }
    
    ">" -> {
      case string.slice(source, at + 1, 1) {
        "=" -> do_lex(source, at + 2, [#(t.GreaterEqual, at), ..tokens], errors)
        _ -> do_lex(source, at + 1, [#(t.Greater, at), ..tokens], errors)
      }
    }
    
    "/" -> {
      case string.slice(source, at + 1, 1) {
        "/" -> {
          // Line comment - skip to end of line
          let new_at = skip_line_comment(source, at + 2)
          do_lex(source, new_at, tokens, errors)
        }
        _ -> do_lex(source, at + 1, [#(t.Slash, at), ..tokens], errors)
      }
    }
    
    "|" -> {
      case string.slice(source, at + 1, 1) {
        "|" -> do_lex(source, at + 2, [#(t.PipePipe, at), ..tokens], errors)
        _ -> do_lex(source, at + 1, [#(t.Pipe, at), ..tokens], errors)
      }
    }
    
    "#" -> {
      // Hash comment - skip to end of line
      let new_at = skip_line_comment(source, at + 1)
      do_lex(source, new_at, tokens, errors)
    }
    
    // Whitespace - skip
    " " | "\t" | "\r" -> do_lex(source, at + 1, tokens, errors)
    "\n" -> do_lex(source, at + 1, tokens, errors)
    
    // String literals
    "\"" -> {
      let #(string_result, new_at) = read_string(source, at + 1, "")
      case string_result {
        Ok(value) -> do_lex(source, new_at, [#(t.String(value), at), ..tokens], errors)
        Error(value) -> do_lex(source, new_at, [#(t.UnterminatedString(value), at), ..tokens], ["Unterminated string", ..errors])
      }
    }
    
    // Numbers and identifiers
    char -> {
      case is_digit(char) {
        True -> {
          let #(number, new_at) = read_number(source, at, "")
          // Parse as float to get the literal value
          case float.parse(number) {
            Ok(float_val) -> {
              let formatted = format_number(float_val)
              do_lex(source, new_at, [#(t.Number(formatted), at), ..tokens], errors)
            }
            Error(_) -> do_lex(source, new_at, [#(t.Number(number), at), ..tokens], ["Invalid number: " <> number, ..errors])
          }
        }
        False -> {
          case is_letter(char) || char == "_" {
            True -> {
              let #(identifier, new_at) = read_identifier(source, at, "")
              let token = get_keyword_token(identifier)
              do_lex(source, new_at, [#(token, at), ..tokens], errors)
            }
            False -> do_lex(source, at + 1, [#(t.UnexpectedGrapheme(char), at), ..tokens], ["Unexpected character: " <> char, ..errors])
          }
        }
      }
    }
  }
}

fn skip_line_comment(source: String, at: Int) -> Int {
  case string.slice(source, at, 1) {
    "" -> at
    "\n" -> at + 1
    _ -> skip_line_comment(source, at + 1)
  }
}

fn read_string(source: String, at: Int, acc: String) -> #(Result(String, String), Int) {
  case string.slice(source, at, 1) {
    "" -> #(Error(acc), at)
    "\"" -> #(Ok(acc), at + 1)
    "\\" -> {
      case string.slice(source, at + 1, 1) {
        "" -> #(Error(acc <> "\\"), at + 1)
        "\"" -> read_string(source, at + 2, acc <> "\"")
        "\\" -> read_string(source, at + 2, acc <> "\\")
        "n" -> read_string(source, at + 2, acc <> "\n")
        "t" -> read_string(source, at + 2, acc <> "\t")
        "r" -> read_string(source, at + 2, acc <> "\r")
        char -> read_string(source, at + 2, acc <> char)
      }
    }
    "\n" -> read_string(source, at + 1, acc <> "\n")
    char -> read_string(source, at + 1, acc <> char)
  }
}

fn read_number(source: String, at: Int, acc: String) -> #(String, Int) {
  case string.slice(source, at, 1) {
    "" -> #(acc, at)
    char -> {
      case is_digit(char) || char == "." {
        True -> read_number(source, at + 1, acc <> char)
        False -> #(acc, at)
      }
    }
  }
}

fn read_identifier(source: String, at: Int, acc: String) -> #(String, Int) {
  case string.slice(source, at, 1) {
    "" -> #(acc, at)
    char -> {
      case is_letter(char) || is_digit(char) || char == "_" {
        True -> read_identifier(source, at + 1, acc <> char)
        False -> #(acc, at)
      }
    }
  }
}

fn get_keyword_token(identifier: String) -> t.Token {
  case identifier {
    "_" -> t.Underscore
    "and" -> t.And
    "else" -> t.Else
    "if" -> t.If
    "nil" -> t.Nil
    "or" -> t.Or
    "match" -> t.Match
    "perform" -> t.Perform
    "handle" -> t.Handle
    "not" -> t.Not
    _ -> t.Identifier(identifier)
  }
}

fn format_number(float_val: Float) -> String {
  // Format with minimum 1 decimal place but only as many as needed
  let formatted = float.to_string(float_val)
  // If no decimal point, add .0
  case string.contains(formatted, ".") {
    True -> formatted
    False -> formatted <> ".0"
  }
}

fn is_digit(char: String) -> Bool {
  case char {
    "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" -> True
    _ -> False
  }
}

fn is_letter(char: String) -> Bool {
  is_lowercase_letter(char) || is_uppercase_letter(char)
}

fn is_lowercase_letter(char: String) -> Bool {
  case char {
    "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z" -> True
    _ -> False
  }
}

fn is_uppercase_letter(char: String) -> Bool {
  case char {
    "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M" | "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z" -> True
    _ -> False
  }
}

// Helper function to extract just the tokens for compatibility
pub fn lex_tokens(source: String) -> List(#(t.Token, Int)) {
  let result = lex(source)
  result.tokens
}