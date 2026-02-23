// Data-driven type checker test suite
// Reads testdata/type_check_cases.json and verifies inferred types and errors

use eyg_analysis::debug;
use eyg_analysis::infer::{self, Context};
use eyg_ir::ast::Node;
use serde::Deserialize;
use std::fs;

#[derive(Debug, Deserialize)]
struct TypeCheckCase {
    name: String,
    #[serde(default)]
    source: Option<String>,
    #[serde(default)]
    source_ir: Option<String>,
    expected_type: Option<String>,
    expected_errors: Vec<String>,
}

fn parse_source(case: &TypeCheckCase) -> Result<Node, String> {
    if let Some(ref src) = case.source {
        eyg_parser::from_string(src).map_err(|e| format!("parse error: {:?}", e))
    } else if let Some(ref ir) = case.source_ir {
        serde_json::from_str(ir).map_err(|e| format!("IR decode error: {}", e))
    } else {
        Err("no source or source_ir field".to_string())
    }
}

#[test]
fn test_type_check_suite() {
    let content = fs::read_to_string("testdata/type_check_cases.json")
        .expect("Failed to read type_check_cases.json");
    let cases: Vec<TypeCheckCase> =
        serde_json::from_str(&content).expect("Failed to parse type_check_cases.json");

    assert!(!cases.is_empty(), "No type check test cases found");

    let mut passed = 0;
    let mut failed = Vec::new();

    for case in &cases {
        let node = match parse_source(case) {
            Ok(n) => n,
            Err(e) => {
                failed.push(format!("Test '{}': {}", case.name, e));
                continue;
            }
        };

        let context = Context::pure();
        let analysis = infer::check(context, &node);

        // Check top-level type
        if let Some(ref expected_type) = case.expected_type {
            let got_type = debug::render_mono(&analysis.type_of());
            if got_type != *expected_type {
                failed.push(format!(
                    "Test '{}': type mismatch\n  expected: {}\n  got:      {}",
                    case.name, expected_type, got_type
                ));
                continue;
            }
        }

        // Collect all errors from annotations
        let errors: Vec<String> = analysis
            .annotations
            .iter()
            .filter_map(|info| {
                if let Err(ref reason) = info.result {
                    Some(debug::render_reason(reason))
                } else {
                    None
                }
            })
            .collect();

        // Check expected errors
        if case.expected_errors.is_empty() {
            if !errors.is_empty() {
                failed.push(format!(
                    "Test '{}': expected no errors, got: {:?}",
                    case.name, errors
                ));
                continue;
            }
        } else {
            let mut all_found = true;
            for expected in &case.expected_errors {
                if !errors.iter().any(|e| e.contains(expected.as_str())) {
                    failed.push(format!(
                        "Test '{}': expected error containing '{}', got: {:?}",
                        case.name, expected, errors
                    ));
                    all_found = false;
                    break;
                }
            }
            if !all_found {
                continue;
            }
            if errors.len() != case.expected_errors.len() {
                failed.push(format!(
                    "Test '{}': expected {} errors, got {} errors: {:?}",
                    case.name,
                    case.expected_errors.len(),
                    errors.len(),
                    errors
                ));
                continue;
            }
        }

        passed += 1;
    }

    if !failed.is_empty() {
        let msg = failed.join("\n\n");
        panic!(
            "{} of {} type check cases failed:\n\n{}",
            failed.len(),
            cases.len(),
            msg
        );
    }

    println!("All {} type check cases passed", passed);
}
