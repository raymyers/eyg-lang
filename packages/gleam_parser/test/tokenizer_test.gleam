import gleam/io
import gleam/list
import gleam/string
import gleam_parser/file_utils
import gleam_parser/json_test_parser
import gleam_parser/lexer
import gleam_parser/token as t

import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

pub fn tokenizer_tests_test() {
  case file_utils.read_file("tokenizer_tests.json") {
    Ok(content) -> {
      case json_test_parser.parse_tokenizer_tests(content) {
        Ok(json_test_parser.TokenizerTests(tests)) -> {
          run_json_tests(tests)
        }
        Ok(json_test_parser.ParserTests(_)) -> {
          io.println("Expected tokenizer tests but got parser tests")
          should.fail()
        }
        Error(err) -> {
          io.println("Failed to parse JSON: " <> string.inspect(err))
          should.fail()
        }
      }
    }
    Error(_) -> {
      io.println("Failed to read tokenizer_tests.json")
      should.fail()
    }
  }
}

fn run_json_tests(tests: List(json_test_parser.TestCase)) -> Nil {
  list.each(tests, fn(test_case) {
    io.println("Running tokenizer test: " <> test_case.name)
    let tokens = lexer.lex_tokens(test_case.input)
    let actual = tokens_to_string(tokens)
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
  })
}

fn tokens_to_string(tokens: List(#(t.Token, Int))) -> String {
  tokens
  |> list.map(fn(token_pair) {
    let #(token, _pos) = token_pair
    case token {
      t.String(lexeme, literal) -> t.to_canonical_string(token, lexeme, literal)
      t.Number(lexeme, literal) -> t.to_canonical_string(token, lexeme, literal)
      t.Identifier(value) -> t.to_canonical_string(token, value, "")
      t.LeftParen -> t.to_canonical_string(token, "(", "")
      t.RightParen -> t.to_canonical_string(token, ")", "")
      t.LeftBrace -> t.to_canonical_string(token, "{", "")
      t.RightBrace -> t.to_canonical_string(token, "}", "")
      t.LeftBracket -> t.to_canonical_string(token, "[", "")
      t.RightBracket -> t.to_canonical_string(token, "]", "")
      t.Comma -> t.to_canonical_string(token, ",", "")
      t.Dot -> t.to_canonical_string(token, ".", "")
      t.Minus -> t.to_canonical_string(token, "-", "")
      t.Plus -> t.to_canonical_string(token, "+", "")
      t.Semicolon -> t.to_canonical_string(token, ";", "")
      t.Star -> t.to_canonical_string(token, "*", "")
      t.Slash -> t.to_canonical_string(token, "/", "")
      t.Bang -> t.to_canonical_string(token, "!", "")
      t.BangEqual -> t.to_canonical_string(token, "!=", "")
      t.Equal -> t.to_canonical_string(token, "=", "")
      t.EqualEqual -> t.to_canonical_string(token, "==", "")
      t.Greater -> t.to_canonical_string(token, ">", "")
      t.GreaterEqual -> t.to_canonical_string(token, ">=", "")
      t.Less -> t.to_canonical_string(token, "<", "")
      t.LessEqual -> t.to_canonical_string(token, "<=", "")
      t.Arrow -> t.to_canonical_string(token, "->", "")
      t.DotDot -> t.to_canonical_string(token, "..", "")
      t.PipePipe -> t.to_canonical_string(token, "||", "")
      t.At -> t.to_canonical_string(token, "@", "")
      t.Colon -> t.to_canonical_string(token, ":", "")
      t.Pipe -> t.to_canonical_string(token, "|", "")
      t.Hash -> t.to_canonical_string(token, "#", "")
      t.And -> t.to_canonical_string(token, "and", "")
      t.Else -> t.to_canonical_string(token, "else", "")
      t.If -> t.to_canonical_string(token, "if", "")
      t.Nil -> t.to_canonical_string(token, "nil", "")
      t.Or -> t.to_canonical_string(token, "or", "")
      t.Match -> t.to_canonical_string(token, "match", "")
      t.Perform -> t.to_canonical_string(token, "perform", "")
      t.Handle -> t.to_canonical_string(token, "handle", "")
      t.Not -> t.to_canonical_string(token, "not", "")
      t.Underscore -> t.to_canonical_string(token, "_", "")
      t.Eof -> t.to_canonical_string(token, "", "")
      t.UnterminatedString(value) ->
        t.to_canonical_string(token, "\"" <> value, value)
      t.UnexpectedGrapheme(value) -> t.to_canonical_string(token, value, "")
    }
  })
  |> string.join("\n")
}
