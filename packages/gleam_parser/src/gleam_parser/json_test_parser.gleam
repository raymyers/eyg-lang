import gleam/dynamic/decode
import gleam/json

pub type TestCase {
  TestCase(name: String, input: String, expected: String)
}

pub type TestSuite {
  TokenizerTests(tests: List(TestCase))
  ParserTests(tests: List(TestCase))
}

fn test_case_decoder() {
  use name <- decode.field("name", decode.string)
  use input <- decode.field("input", decode.string)
  use expected <- decode.field("expected", decode.string)
  decode.success(TestCase(name:, input:, expected:))
}

fn tokenizer_tests_decoder() {
  use tests <- decode.field("tokenizer_tests", decode.list(test_case_decoder()))
  decode.success(TokenizerTests(tests:))
}

fn parser_tests_decoder() {
  use tests <- decode.field("parser_tests", decode.list(test_case_decoder()))
  decode.success(ParserTests(tests:))
}

pub fn parse_tokenizer_tests(
  json_string: String,
) -> Result(TestSuite, json.DecodeError) {
  json.parse(from: json_string, using: tokenizer_tests_decoder())
}

pub fn parse_parser_tests(
  json_string: String,
) -> Result(TestSuite, json.DecodeError) {
  json.parse(from: json_string, using: parser_tests_decoder())
}
