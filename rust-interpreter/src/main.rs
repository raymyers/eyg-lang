use clap::Parser;
use rust_interpreter::interpreter::expression;
use rust_interpreter::ir::ast::Node;
use std::fs;
use std::process;

#[derive(Parser, Debug)]
#[command(name = "eyg-run")]
#[command(about = "EYG Rust Interpreter - Execute EYG programs from dag-json files", long_about = None)]
struct Args {
    /// Path to the JSON file containing the EYG program
    file: String,
}

fn main() {
    let args = Args::parse();

    // Read the file
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

    // Execute the program
    match expression::execute(node, vec![]) {
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
