// Data-driven parser test suite
// Reads testdata/parse_cases.json and verifies from_string produces expected dag-json

use serde::Deserialize;
use serde_json::Value as JsonValue;
use std::fs;

#[derive(Debug, Deserialize)]
struct ParseCase {
    name: String,
    source: String,
    expected: JsonValue,
}

#[derive(Debug, Deserialize)]
struct ParseErrorCase {
    name: String,
    source: String,
    error: String,
}

#[test]
fn test_parse_suite() {
    let content = fs::read_to_string("testdata/parse_cases.json")
        .expect("Failed to read testdata/parse_cases.json");
    let cases: Vec<ParseCase> =
        serde_json::from_str(&content).expect("Failed to parse parse_cases.json");

    assert!(!cases.is_empty(), "No test cases found");

    for case in &cases {
        let node = eyg_parser::from_string(&case.source).unwrap_or_else(|e| {
            panic!("Test '{}': parse failed for {:?}: {}", case.name, case.source, e)
        });

        let got: JsonValue = serde_json::to_value(&node).unwrap_or_else(|e| {
            panic!("Test '{}': serialization failed: {}", case.name, e)
        });

        assert_eq!(
            got, case.expected,
            "Test '{}': IR mismatch for {:?}\n  got:      {}\n  expected: {}",
            case.name, case.source, got, case.expected
        );
    }

    println!("All {} parse cases passed", cases.len());
}

#[test]
fn test_parse_error_suite() {
    let content = fs::read_to_string("testdata/parse_error_cases.json")
        .expect("Failed to read testdata/parse_error_cases.json");
    let cases: Vec<ParseErrorCase> =
        serde_json::from_str(&content).expect("Failed to parse parse_error_cases.json");

    assert!(!cases.is_empty(), "No error test cases found");

    for case in &cases {
        let result = eyg_parser::from_string(&case.source);
        assert!(
            result.is_err(),
            "Test '{}': expected parse error for {:?}, but got Ok",
            case.name, case.source
        );
        let err_msg = format!("{}", result.unwrap_err());
        let err_lower = err_msg.to_lowercase();
        assert!(
            err_lower.contains(&case.error),
            "Test '{}': error message {:?} does not contain {:?}",
            case.name, err_msg, case.error
        );
    }

    println!("All {} parse error cases passed", cases.len());
}
