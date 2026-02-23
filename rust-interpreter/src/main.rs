use clap::{Parser, ValueEnum};
use eyg_analysis::debug as type_debug;
use eyg_analysis::infer::{self, Context};
use rust_interpreter::interpreter::{
    break_reason::BreakReason, expression, value, value_json,
};
use rust_interpreter::ir::ast::Node;
use serde::Deserialize;
use serde_json::Value as JsonValue;
use std::fs;
use std::process;
use std::rc::Rc;

#[derive(ValueEnum, Clone, Debug, Default)]
enum InputFormat {
    /// dag-json IR format (default)
    #[default]
    Ir,
    /// EYG source text
    Eyg,
}

#[derive(Parser, Debug)]
#[command(name = "eyg-run")]
#[command(about = "EYG Rust Interpreter - Execute EYG programs", long_about = None)]
struct Args {
    /// Path to EYG program file
    file: String,

    /// Input format: ir (dag-json, default) or eyg (source text)
    #[arg(long = "in", default_value = "ir")]
    input_format: InputFormat,

    /// Dump parsed IR as dag-json instead of executing
    #[arg(long)]
    dump_ir: bool,

    /// Type-check the program and print the inferred type
    #[arg(long)]
    type_check: bool,

    /// Path to JSON file containing effect handlers
    #[arg(long)]
    effects: Option<String>,
}

#[derive(Debug, Deserialize)]
struct EffectHandler {
    label: String,
    #[allow(dead_code)]
    lift: JsonValue,
    reply: JsonValue,
}

fn read_file(path: &str) -> String {
    match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error reading file '{}': {}", path, e);
            process::exit(1);
        }
    }
}

fn parse_source(path: &str) -> Node {
    let source = read_file(path);
    match eyg_parser::from_string(&source) {
        Ok(node) => node,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            process::exit(1);
        }
    }
}

fn load_effects(path: &str) -> Vec<EffectHandler> {
    let contents = read_file(path);
    match serde_json::from_str(&contents) {
        Ok(h) => h,
        Err(e) => {
            eprintln!("Error parsing effects JSON: {}", e);
            process::exit(1);
        }
    }
}

/// Execute a node, handling Log effects automatically and explicit effect handlers.
fn run(node: Node, effect_handlers: &[EffectHandler]) {
    let mut result = expression::execute(node, im::Vector::new());

    // Handle explicit effect handlers first
    for handler in effect_handlers {
        match &result {
            Err(debug) => {
                let (reason, _meta, env, stack) = &**debug;
                match reason {
                    BreakReason::UnhandledEffect(label, _lift_value) => {
                        if label != &handler.label {
                            eprintln!(
                                "Error: Expected effect '{}', but got '{}'",
                                handler.label, label
                            );
                            process::exit(1);
                        }
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

    // Handle Log effects in a loop (built-in extrinsic)
    while let Err(debug) = &result {
        let (reason, _meta, env, stack) = &**debug;
        if let BreakReason::UnhandledEffect(label, lift_value) = reason
            && label == "Log"
        {
            eprintln!("{}", lift_value);
            let reply = Rc::new(value::unit());
            result = expression::resume(reply, env.clone(), stack.clone());
        } else {
            break;
        }
    }

    match result {
        Ok(val) => {
            println!("{}", val);
        }
        Err(debug) => {
            let (reason, _, _, _) = *debug;
            eprintln!("Error: {}", reason);
            process::exit(1);
        }
    }
}

fn load_node(path: &str, format: &InputFormat) -> Node {
    match format {
        InputFormat::Eyg => parse_source(path),
        InputFormat::Ir => {
            let contents = read_file(path);
            match serde_json::from_str(&contents) {
                Ok(n) => n,
                Err(e) => {
                    eprintln!("Error parsing JSON: {}", e);
                    process::exit(1);
                }
            }
        }
    }
}

fn type_check(node: &Node) {
    let context = Context::unpure();
    let analysis = infer::check(context, node);
    let top_type = analysis.type_of();
    let type_str = type_debug::render_mono(&top_type);

    let errors: Vec<_> = analysis
        .annotations
        .iter()
        .filter_map(|info| info.result.as_ref().err())
        .collect();

    if errors.is_empty() {
        println!("{}", type_str);
    } else {
        for reason in &errors {
            eprintln!("Type error: {}", type_debug::render_reason(reason));
        }
        println!("{}", type_str);
        process::exit(1);
    }
}

fn main() {
    let args = Args::parse();
    let node = load_node(&args.file, &args.input_format);

    if args.dump_ir {
        match serde_json::to_string(&node) {
            Ok(json) => println!("{}", json),
            Err(e) => {
                eprintln!("Error serializing to JSON: {}", e);
                process::exit(1);
            }
        }
        return;
    }

    if args.type_check {
        type_check(&node);
        return;
    }

    let handlers = args
        .effects
        .as_deref()
        .map(load_effects)
        .unwrap_or_default();
    run(node, &handlers);
}
