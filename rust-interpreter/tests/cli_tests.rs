// CLI integration tests
use std::fs;
use std::process::Command;

fn eyg_run() -> Command {
    Command::new("./target/debug/eyg-run")
}

// --- --in eyg --dump-ir tests ---

#[test]
fn test_dump_ir_integer() {
    let source = "42";
    let temp = "/tmp/eyg_test_dump_ir_int.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", "--dump-ir", temp])
        .output()
        .expect("Failed to execute");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), r#"{"0":"i","v":42}"#);
}

#[test]
fn test_dump_ir_let() {
    let source = "let x = 1\nx";
    let temp = "/tmp/eyg_test_dump_ir_let.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", "--dump-ir", temp])
        .output()
        .expect("Failed to execute");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let parsed: serde_json::Value = serde_json::from_str(stdout.trim()).unwrap();
    assert_eq!(parsed["0"], "l");
    assert_eq!(parsed["l"], "x");
}

#[test]
fn test_dump_ir_parse_error() {
    let source = "!!bad";
    let temp = "/tmp/eyg_test_dump_ir_err.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", "--dump-ir", temp])
        .output()
        .expect("Failed to execute");

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("Parse error"));
}

// --- --in eyg (execute) tests ---

#[test]
fn test_eyg_exec_integer() {
    let source = "42";
    let temp = "/tmp/eyg_test_exec_int.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", temp])
        .output()
        .expect("Failed to execute");

    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
}

#[test]
fn test_eyg_exec_lambda() {
    let source = r#"let id = (x) -> { x }
id(99)"#;
    let temp = "/tmp/eyg_test_exec_lambda.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", temp])
        .output()
        .expect("Failed to execute");

    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "99");
}

// --- Log handler tests ---

#[test]
fn test_eyg_exec_log() {
    let source = r#"perform Log("hi")"#;
    let temp = "/tmp/eyg_test_exec_log.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", temp])
        .output()
        .expect("Failed to execute");

    assert!(output.status.success(), "stderr: {}", String::from_utf8_lossy(&output.stderr));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("\"hi\""), "stderr was: {}", stderr);
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "{}");
}

#[test]
fn test_eyg_exec_log_chained() {
    let source = r#"let _ = perform Log("a")
perform Log("b")"#;
    let temp = "/tmp/eyg_test_exec_log_chain.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", temp])
        .output()
        .expect("Failed to execute");

    assert!(output.status.success(), "stderr: {}", String::from_utf8_lossy(&output.stderr));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("\"a\""), "stderr was: {}", stderr);
    assert!(stderr.contains("\"b\""), "stderr was: {}", stderr);
}

#[test]
fn test_cli_integer() {
    let json = r#"{"0":"i","v":42}"#;
    let temp_file = "/tmp/eyg_test_integer.json";
    fs::write(temp_file, json).unwrap();

    let output = eyg_run()
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

    let output = eyg_run()
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

    let output = eyg_run()
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

    let output = eyg_run()
        .arg(temp_file)
        .output()
        .expect("Failed to execute command");

    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
}

#[test]
fn test_cli_file_not_found() {
    let output = eyg_run()
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

    let output = eyg_run()
        .arg(temp_file)
        .output()
        .expect("Failed to execute command");

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("Error parsing JSON"));
}

#[test]
fn test_cli_with_effects() {
    // Test program that performs two effects: Foo(1) -> 2, then Bar(2) -> 34
    let program_json = r#"{
  "0": "l",
  "l": "a",
  "t": {
    "0": "a",
    "a": {
      "0": "v",
      "l": "a"
    },
    "f": {
      "0": "p",
      "l": "Bar"
    }
  },
  "v": {
    "0": "a",
    "a": {
      "0": "i",
      "v": 1
    },
    "f": {
      "0": "p",
      "l": "Foo"
    }
  }
}"#;

    let effects_json = r#"[
  {
    "label": "Foo",
    "lift": {
      "integer": 1
    },
    "reply": {
      "integer": 2
    }
  },
  {
    "label": "Bar",
    "lift": {
      "integer": 2
    },
    "reply": {
      "integer": 34
    }
  }
]"#;

    let program_file = "/tmp/eyg_test_effects_program.json";
    let effects_file = "/tmp/eyg_test_effects_handlers.json";
    fs::write(program_file, program_json).unwrap();
    fs::write(effects_file, effects_json).unwrap();

    let output = eyg_run()
        .args([program_file, "--effects", effects_file])
        .output()
        .expect("Failed to execute command");

    assert!(
        output.status.success(),
        "Command failed with stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "34");
}

#[test]
fn test_cli_unhandled_effect() {
    // Test program that performs an effect without a handler
    let program_json = r#"{
  "0": "a",
  "a": {
    "0": "i",
    "v": 1
  },
  "f": {
    "0": "p",
    "l": "Foo"
  }
}"#;

    let program_file = "/tmp/eyg_test_unhandled_effect.json";
    fs::write(program_file, program_json).unwrap();

    let output = eyg_run()
        .arg(program_file)
        .output()
        .expect("Failed to execute command");

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("Unhandled effect 'Foo'"));
}

// --- --type-check tests ---

#[test]
fn test_type_check_well_typed_eyg() {
    let source = "5";
    let temp = "/tmp/eyg_test_tc_int.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", "--type-check", temp])
        .output()
        .expect("Failed to execute");

    assert!(output.status.success(), "stderr: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "Integer");
}

#[test]
fn test_type_check_well_typed_json() {
    let json = r#"{"0":"i","v":42}"#;
    let temp = "/tmp/eyg_test_tc_int.json";
    fs::write(temp, json).unwrap();

    let output = eyg_run()
        .args(["--type-check", temp])
        .output()
        .expect("Failed to execute");

    assert!(output.status.success(), "stderr: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "Integer");
}

#[test]
fn test_type_check_string() {
    let source = r#""hello""#;
    let temp = "/tmp/eyg_test_tc_str.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", "--type-check", temp])
        .output()
        .expect("Failed to execute");

    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "String");
}

#[test]
fn test_type_check_function() {
    let source = "(x) -> { x }";
    let temp = "/tmp/eyg_test_tc_fn.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", "--type-check", temp])
        .output()
        .expect("Failed to execute");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Identity fn: (a) -> a — the var IDs may vary
    assert!(stdout.contains("->"), "stdout was: {}", stdout);
}

#[test]
fn test_type_check_ill_typed() {
    // Missing variable → type error
    let source = "x";
    let temp = "/tmp/eyg_test_tc_err.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", "--type-check", temp])
        .output()
        .expect("Failed to execute");

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("missing variable"), "stderr was: {}", stderr);
}

#[test]
fn test_type_check_parse_error() {
    let source = "!!bad";
    let temp = "/tmp/eyg_test_tc_parse_err.eyg";
    fs::write(temp, source).unwrap();

    let output = eyg_run()
        .args(["--in", "eyg", "--type-check", temp])
        .output()
        .expect("Failed to execute");

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("Parse error"), "stderr was: {}", stderr);
}

#[test]
fn test_type_check_vacant() {
    // Vacant (todo) produces a type error
    let json = r#"{"0":"z"}"#;
    let temp = "/tmp/eyg_test_tc_vacant.json";
    fs::write(temp, json).unwrap();

    let output = eyg_run()
        .args(["--type-check", temp])
        .output()
        .expect("Failed to execute");

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("code incomplete"), "stderr was: {}", stderr);
}

