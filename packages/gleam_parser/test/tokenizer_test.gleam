import gleam_parser/lexer
import gleam_parser/token as t
import gleam/string
import gleam/list

import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

pub fn tokenizer_tests_test() {
  let tests = get_test_cases()
  run_all_tests(tests)
}

type TestCase {
  TestCase(name: String, input: String, expected: String)
}

fn get_test_cases() -> List(TestCase) {
  [
    TestCase("Parens", "(())", "LEFT_PAREN ( null\nLEFT_PAREN ( null\nRIGHT_PAREN ) null\nRIGHT_PAREN ) null\nEOF  null"),
    TestCase("Braces", "{{}}", "LEFT_BRACE { null\nLEFT_BRACE { null\nRIGHT_BRACE } null\nRIGHT_BRACE } null\nEOF  null"),
    TestCase("Brackets", "[[]]", "LEFT_BRACKET [ null\nLEFT_BRACKET [ null\nRIGHT_BRACKET ] null\nRIGHT_BRACKET ] null\nEOF  null"),
    TestCase("Ops", "({*.,+-;|})", "LEFT_PAREN ( null\nLEFT_BRACE { null\nSTAR * null\nDOT . null\nCOMMA , null\nPLUS + null\nMINUS - null\nSEMICOLON ; null\nPIPE | null\nRIGHT_BRACE } null\nRIGHT_PAREN ) null\nEOF  null"),
    TestCase("EygOps", "!@:->||..", "BANG ! null\nAT @ null\nCOLON : null\nARROW -> null\nPIPE_PIPE || null\nDOT_DOT .. null\nEOF  null"),
    TestCase("HashComment", "()# comment", "LEFT_PAREN ( null\nRIGHT_PAREN ) null\nEOF  null"),
    TestCase("TabsSpaces", "( ){\t}", "LEFT_PAREN ( null\nRIGHT_PAREN ) null\nLEFT_BRACE { null\nRIGHT_BRACE } null\nEOF  null"),
    TestCase("MultiLine", "(\n)", "LEFT_PAREN ( null\nRIGHT_PAREN ) null\nEOF  null"),
    TestCase("StringLit", "( \"Hello World\" )", "LEFT_PAREN ( null\nSTRING \"Hello World\" Hello World\nRIGHT_PAREN ) null\nEOF  null"),
    TestCase("NumberLit", "42 3.14 0.5 1757.7378", "NUMBER 42 42.0\nNUMBER 3.14 3.14\nNUMBER 0.5 0.5\nNUMBER 1757.7378 1757.7378\nEOF  null"),
    TestCase("Identifier", "foo_bar a b _", "IDENTIFIER foo_bar null\nIDENTIFIER a null\nIDENTIFIER b null\nUNDERSCORE _ null\nEOF  null"),
    TestCase("EygKeywords", "match perform handle True False Ok Error Cat", "MATCH match null\nPERFORM perform null\nHANDLE handle null\nIDENTIFIER True null\nIDENTIFIER False null\nIDENTIFIER Ok null\nIDENTIFIER Error null\nIDENTIFIER Cat null\nEOF  null")
  ]
}

fn run_all_tests(tests: List(TestCase)) -> Nil {
  list.each(tests, run_single_test)
}

fn run_single_test(test_case: TestCase) -> Nil {
  let result = lexer.lex(test_case.input)
  let actual = tokens_to_string(result.tokens)
  
  actual
  |> should.equal(test_case.expected)
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
      t.UnterminatedString(value) -> t.to_canonical_string(token, "\"" <> value, value)
      t.UnexpectedGrapheme(value) -> t.to_canonical_string(token, value, "")
    }
  })
  |> string.join("\n")
}