// Data-driven lexer test suite
// Reads testdata/lex_cases.json and verifies lex + drop_whitespace produces expected tokens

use eyg_parser::lexer;
use eyg_parser::token::{self, Token};
use serde::Deserialize;
use serde_json::Value as JsonValue;
use std::fs;

fn token_to_tag(tok: &Token) -> String {
    match tok {
        Token::Name(s) => format!("Name:{s}"),
        Token::Uppername(s) => format!("Uppername:{s}"),
        Token::Integer(s) => format!("Integer:{s}"),
        Token::String(s) => format!("String:{s}"),
        Token::Comment(s) => format!("Comment:{s}"),
        Token::Whitespace(s) => format!("Whitespace:{s}"),
        Token::UnexpectedGrapheme(s) => format!("UnexpectedGrapheme:{s}"),
        Token::UnterminatedString(s) => format!("UnterminatedString:{s}"),
        Token::Let => "Let".to_string(),
        Token::Match => "Match".to_string(),
        Token::Perform => "Perform".to_string(),
        Token::Deep => "Deep".to_string(),
        Token::Handle => "Handle".to_string(),
        Token::Equal => "Equal".to_string(),
        Token::Comma => "Comma".to_string(),
        Token::DotDot => "DotDot".to_string(),
        Token::Dot => "Dot".to_string(),
        Token::Colon => "Colon".to_string(),
        Token::RightArrow => "RightArrow".to_string(),
        Token::Minus => "Minus".to_string(),
        Token::Bang => "Bang".to_string(),
        Token::Bar => "Bar".to_string(),
        Token::Hash => "Hash".to_string(),
        Token::At => "At".to_string(),
        Token::LeftParen => "LeftParen".to_string(),
        Token::RightParen => "RightParen".to_string(),
        Token::LeftBrace => "LeftBrace".to_string(),
        Token::RightBrace => "RightBrace".to_string(),
        Token::LeftSquare => "LeftSquare".to_string(),
        Token::RightSquare => "RightSquare".to_string(),
    }
}

#[derive(Debug, Deserialize)]
struct LexCase {
    name: String,
    source: String,
    expected: Vec<JsonValue>,
}

#[test]
fn test_lex_suite() {
    let content =
        fs::read_to_string("testdata/lex_cases.json").expect("Failed to read lex_cases.json");
    let cases: Vec<LexCase> =
        serde_json::from_str(&content).expect("Failed to parse lex_cases.json");

    assert!(!cases.is_empty(), "No lex test cases found");

    for case in &cases {
        let tokens = lexer::lex(&case.source);
        let tokens = token::drop_whitespace(tokens);

        let got: Vec<(String, usize)> = tokens
            .iter()
            .map(|(tok, pos)| (token_to_tag(tok), *pos))
            .collect();

        let expected: Vec<(String, usize)> = case
            .expected
            .iter()
            .map(|entry| {
                let arr = entry.as_array().expect("each token should be [tag, offset]");
                let tag = arr[0].as_str().expect("tag should be string").to_string();
                let offset = arr[1].as_u64().expect("offset should be number") as usize;
                (tag, offset)
            })
            .collect();

        assert_eq!(
            got, expected,
            "Test '{}': token mismatch for {:?}\n  got:      {:?}\n  expected: {:?}",
            case.name, case.source, got, expected
        );
    }

    println!("All {} lex cases passed", cases.len());
}
