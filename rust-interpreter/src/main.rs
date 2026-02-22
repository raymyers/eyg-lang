use clap::Parser;
use rust_interpreter::interpreter::{break_reason::BreakReason, expression, value_json};
use rust_interpreter::ir::ast::Node;
use serde::Deserialize;
use serde_json::Value as JsonValue;
use std::fs;
use std::process;
use std::rc::Rc;

#[derive(Parser, Debug)]
#[command(name = "eyg-run")]
#[command(about = "EYG Rust Interpreter - Execute EYG programs from dag-json files", long_about = None)]
struct Args {
    /// Path to the JSON file containing the EYG program
    file: String,

    /// Path to JSON file containing effect handlers
    #[arg(long)]
    effects: Option<String>,
}

#[derive(Debug, Deserialize)]
struct EffectHandler {
    label: String,
    #[allow(dead_code)] // Reserved for future validation of lift values
    lift: JsonValue,
    reply: JsonValue,
}

fn main() {
    let args = Args::parse();

    // Read the program file
    let contents = match fs::read_to_string(&args.file) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error reading file '{}': {}", args.file, e);
            process::exit(1);
        }
    };

    // Parse the JSON into a Node
    let node: Node = match serde_json::from_str(&contents) {
        Ok(n) => n,
        Err(e) => {
            eprintln!("Error parsing JSON: {}", e);
            process::exit(1);
        }
    };

    // Load effect handlers if provided
    let effect_handlers: Vec<EffectHandler> = if let Some(effects_file) = &args.effects {
        let effects_contents = match fs::read_to_string(effects_file) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Error reading effects file '{}': {}", effects_file, e);
                process::exit(1);
            }
        };
        match serde_json::from_str(&effects_contents) {
            Ok(h) => h,
            Err(e) => {
                eprintln!("Error parsing effects JSON: {}", e);
                process::exit(1);
            }
        }
    } else {
        vec![]
    };

    // Execute the program
    let mut result = expression::execute(node, im::Vector::new());

    // Handle effects
    for handler in &effect_handlers {
        match &result {
            Err(debug) => {
                let (reason, _meta, env, stack) = &**debug;
                match reason {
                    BreakReason::UnhandledEffect(label, _lift_value) => {
                        // Verify the effect label matches
                        if label != &handler.label {
                            eprintln!(
                                "Error: Expected effect '{}', but got '{}'",
                                handler.label, label
                            );
                            process::exit(1);
                        }

                        // Optionally verify the lift value matches expected
                        // (for now we just accept any lift value and use the handler's reply)

                        // Resume with the reply value
                        let reply = Rc::new(value_json::deserialize_value(&handler.reply));
                        result = expression::resume(reply, env.clone(), stack.clone());
                    }
                    _ => {
                        eprintln!("Error: Expected UnhandledEffect, got: {}", reason);
                        process::exit(1);
                    }
                }
            }
            Ok(_) => {
                eprintln!(
                    "Error: Expected UnhandledEffect for '{}', but execution succeeded",
                    handler.label
                );
                process::exit(1);
            }
        }
    }

    // Final result
    match result {
        Ok(value) => {
            println!("{}", value);
        }
        Err(debug) => {
            // Debug is Box<(BreakReason, (), Env, Stack)>
            let (reason, _, _, _) = *debug;
            eprintln!("Error: {}", reason);
            process::exit(1);
        }
    }
}
