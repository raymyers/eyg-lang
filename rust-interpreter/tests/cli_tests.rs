// CLI integration tests
use std::fs;
use std::process::Command;

#[test]
fn test_cli_integer() {
    let json = r#"{"0":"i","v":42}"#;
    let temp_file = "/tmp/eyg_test_integer.json";
    fs::write(temp_file, json).unwrap();

    let output = Command::new("./target/debug/eyg-run")
        .arg(temp_file)
        .output()
        .expect("Failed to execute command");

    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
}

#[test]
fn test_cli_string() {
    let json = r#"{"0":"s","v":"hello"}"#;
    let temp_file = "/tmp/eyg_test_string.json";
    fs::write(temp_file, json).unwrap();

    let output = Command::new("./target/debug/eyg-run")
        .arg(temp_file)
        .output()
        .expect("Failed to execute command");

    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "\"hello\"");
}

#[test]
fn test_cli_error() {
    let json = r#"{"0":"v","l":"x"}"#;
    let temp_file = "/tmp/eyg_test_error.json";
    fs::write(temp_file, json).unwrap();

    let output = Command::new("./target/debug/eyg-run")
        .arg(temp_file)
        .output()
        .expect("Failed to execute command");

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("Undefined variable: x"));
}

#[test]
fn test_cli_lambda_application() {
    let json = r#"{
        "0": "a",
        "f": {
            "0": "f",
            "l": "x",
            "b": {
                "0": "v",
                "l": "x"
            }
        },
        "a": {
            "0": "i",
            "v": 42
        }
    }"#;
    let temp_file = "/tmp/eyg_test_lambda.json";
    fs::write(temp_file, json).unwrap();

    let output = Command::new("./target/debug/eyg-run")
        .arg(temp_file)
        .output()
        .expect("Failed to execute command");

    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
}

#[test]
fn test_cli_file_not_found() {
    let output = Command::new("./target/debug/eyg-run")
        .arg("/tmp/nonexistent_file.json")
        .output()
        .expect("Failed to execute command");

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("Error reading file"));
}

#[test]
fn test_cli_invalid_json() {
    let json = r#"not valid json"#;
    let temp_file = "/tmp/eyg_test_invalid.json";
    fs::write(temp_file, json).unwrap();

    let output = Command::new("./target/debug/eyg-run")
        .arg(temp_file)
        .output()
        .expect("Failed to execute command");

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("Error parsing JSON"));
}

