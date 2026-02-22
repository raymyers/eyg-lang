// Evaluation test suite
// Reads spec/evaluation/*.json and runs all test fixtures

use rust_interpreter::interpreter::break_reason::BreakReason;
use rust_interpreter::interpreter::expression;
use rust_interpreter::interpreter::value::Value;
use rust_interpreter::ir::ast::Node;
use serde::Deserialize;
use serde_json::Value as JsonValue;
use std::collections::HashMap;
use std::fs;
use std::rc::Rc;

#[derive(Debug, Deserialize)]
struct Fixture {
    name: String,
    source: JsonValue,
    #[serde(default)]
    effects: Vec<Effect>,
    #[serde(flatten)]
    expectation: Expectation,
}

#[derive(Debug, Deserialize)]
struct Effect {
    label: String,
    lift: JsonValue,
    reply: JsonValue,
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum Expectation {
    Value { value: JsonValue },
    Break { r#break: JsonValue },
}

fn deserialize_value(json: &JsonValue) -> Value {
    if let Some(i) = json.get("integer") {
        return Value::Integer(i.as_i64().expect("integer should be i64"));
    }
    if let Some(s) = json.get("string") {
        return Value::Str(s.as_str().expect("string should be str").to_string());
    }
    if let Some(b) = json.get("binary") {
        // Binary is encoded as dag-json: {"/":{bytes":"<base64>"}}
        let dag_obj = b.as_object().expect("binary should be object");
        let bytes_obj = dag_obj
            .get("/")
            .expect("binary should have / field")
            .as_object()
            .expect("/ should be object");
        let bytes_str = bytes_obj
            .get("bytes")
            .expect("binary should have bytes field")
            .as_str()
            .expect("bytes should be string");
        // Use base64 engine for decoding
        use base64::Engine;
        let bytes = base64::engine::general_purpose::URL_SAFE_NO_PAD
            .decode(bytes_str)
            .expect("bytes should be valid base64");
        return Value::Binary(bytes);
    }
    if let Some(list) = json.get("list") {
        let items: Vec<Rc<Value>> = list
            .as_array()
            .expect("list should be array")
            .iter()
            .map(|v| Rc::new(deserialize_value(v)))
            .collect();
        return Value::LinkedList(items);
    }
    if let Some(record) = json.get("record") {
        let fields: HashMap<String, Rc<Value>> = record
            .as_object()
            .expect("record should be object")
            .iter()
            .map(|(k, v)| (k.clone(), Rc::new(deserialize_value(v))))
            .collect();
        return Value::Record(fields);
    }
    if let Some(tagged) = json.get("tagged") {
        let label = tagged
            .get("label")
            .expect("tagged should have label")
            .as_str()
            .expect("label should be string")
            .to_string();
        let value = Rc::new(deserialize_value(
            tagged.get("value").expect("tagged should have value"),
        ));
        return Value::Tagged { label, value };
    }
    panic!("Unknown value type: {:?}", json);
}

fn deserialize_break_reason(json: &JsonValue) -> BreakReason {
    if let Some(var) = json.get("UndefinedVariable") {
        return BreakReason::UndefinedVariable(
            var.as_str().expect("variable should be string").to_string(),
        );
    }
    if let Some(builtin) = json.get("UndefinedBuiltin") {
        return BreakReason::UndefinedBuiltin(
            builtin
                .as_str()
                .expect("builtin should be string")
                .to_string(),
        );
    }
    if json.get("NotImplemented").is_some() {
        return BreakReason::Vacant;
    }
    if json.get("Vacant").is_some() {
        return BreakReason::Vacant;
    }
    panic!("Unknown break reason: {:?}", json);
}

fn values_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Integer(a), Value::Integer(b)) => a == b,
        (Value::Str(a), Value::Str(b)) => a == b,
        (Value::Binary(a), Value::Binary(b)) => a == b,
        (Value::LinkedList(a), Value::LinkedList(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| values_equal(x, y))
        }
        (Value::Record(a), Value::Record(b)) => {
            a.len() == b.len()
                && a.iter()
                    .all(|(k, v)| b.get(k).map_or(false, |bv| values_equal(v, bv)))
        }
        (
            Value::Tagged {
                label: la,
                value: va,
            },
            Value::Tagged {
                label: lb,
                value: vb,
            },
        ) => la == lb && values_equal(va, vb),
        _ => false,
    }
}

fn run_fixture(fixture: Fixture) {
    let name = &fixture.name;

    // Deserialize the source IR node
    let source: Node = serde_json::from_value(fixture.source.clone())
        .unwrap_or_else(|e| panic!("Failed to deserialize source for '{}': {}", name, e));

    // Execute the program
    let mut result = expression::execute(source, vec![]);

    // Handle effects
    for effect in &fixture.effects {
        match &result {
            Err(debug) => {
                let (reason, _meta, env, stack) = &**debug;
                match reason {
                    BreakReason::UnhandledEffect(label, value) => {
                        let expected_label = &effect.label;
                        let expected_lift = deserialize_value(&effect.lift);

                        assert_eq!(
                            label, expected_label,
                            "Test '{}': Expected effect label '{}', got '{}'",
                            name, expected_label, label
                        );

                        assert!(
                            values_equal(value, &expected_lift),
                            "Test '{}': Effect '{}' lift value mismatch.\nExpected: {:?}\nGot: {:?}",
                            name, label, expected_lift, value
                        );

                        // Resume with the reply value
                        let reply = Rc::new(deserialize_value(&effect.reply));
                        println!("  Resuming effect '{}' with reply: {:?}", label, reply);
                        println!("  Stack: {:?}", stack);
                        result = expression::resume(reply, env.clone(), stack.clone());
                        println!("  After resume, result is: {:?}", match &result {
                            Ok(v) => format!("Ok({:?})", v),
                            Err(d) => format!("Err({:?})", d.0),
                        });
                    }
                    _ => panic!(
                        "Test '{}': Expected UnhandledEffect, got {:?}",
                        name, reason
                    ),
                }
            }
            Ok(_) => panic!(
                "Test '{}': Expected UnhandledEffect for '{}', but execution succeeded",
                name, effect.label
            ),
        }
    }

    // Check final result
    match &fixture.expectation {
        Expectation::Value { value: expected_json } => {
            let expected = deserialize_value(expected_json);
            match result {
                Ok(got) => {
                    assert!(
                        values_equal(&got, &expected),
                        "Test '{}': Value mismatch.\nExpected: {:?}\nGot: {:?}",
                        name, expected, got
                    );
                }
                Err(debug) => {
                    let (reason, _, _, _) = &*debug;
                    panic!(
                        "Test '{}': Expected value {:?}, but got error: {:?}",
                        name, expected, reason
                    );
                }
            }
        }
        Expectation::Break { r#break: expected_json } => {
            let expected = deserialize_break_reason(expected_json);
            match result {
                Err(debug) => {
                    let (reason, _, _, _) = &*debug;
                    // Compare break reasons - we need to implement PartialEq or do manual comparison
                    assert!(
                        break_reasons_equal(reason, &expected),
                        "Test '{}': Break reason mismatch.\nExpected: {:?}\nGot: {:?}",
                        name, expected, reason
                    );
                }
                Ok(value) => {
                    panic!(
                        "Test '{}': Expected break {:?}, but got value: {:?}",
                        name, expected, value
                    );
                }
            }
        }
    }
}

fn break_reasons_equal(a: &BreakReason, b: &BreakReason) -> bool {
    match (a, b) {
        (BreakReason::UndefinedVariable(a), BreakReason::UndefinedVariable(b)) => a == b,
        (BreakReason::UndefinedBuiltin(a), BreakReason::UndefinedBuiltin(b)) => a == b,
        (BreakReason::Vacant, BreakReason::Vacant) => true,
        (BreakReason::NoMatch(_), BreakReason::NoMatch(_)) => true,
        (BreakReason::MissingField(a), BreakReason::MissingField(b)) => a == b,
        _ => false,
    }
}

fn run_suite(file_path: &str) {
    let content = fs::read_to_string(file_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", file_path, e));

    let fixtures: Vec<Fixture> = serde_json::from_str(&content)
        .unwrap_or_else(|e| panic!("Failed to parse {}: {}", file_path, e));

    for fixture in fixtures {
        println!("Running test: {}", fixture.name);
        run_fixture(fixture);
    }
}

#[test]
fn test_core_suite() {
    run_suite("../spec/evaluation/core_suite.json");
}

#[test]
fn test_builtins_suite() {
    run_suite("../spec/evaluation/builtins_suite.json");
}

#[test]
fn test_effects_suite() {
    run_suite("../spec/evaluation/effects_suite.json");
}

