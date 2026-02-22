// execute / call / resume
// Mirrors packages/gleam_interpreter/src/eyg/interpreter/expression.gleam

use super::state::{Control, Env, EvalResult, Next, Stack};
use super::value::{Scope, Value};
use crate::ir::ast::Node;
use std::collections::HashMap;
use std::rc::Rc;

/// Main evaluation loop
pub fn eval_loop(next: Next) -> EvalResult {
    match next {
        Next::Loop(c, e, k) => eval_loop(super::state::step(c, e, k)),
        Next::Break(result) => result,
    }
}

/// Execute an expression with a given scope
pub fn execute(exp: Node, scope: Scope) -> EvalResult {
    eval_loop(super::state::step(
        Control::Expr(exp),
        new_env(scope),
        Box::new(Stack::Empty(HashMap::new())),
    ))
}

/// Call a function with arguments
pub fn call(f: Rc<Value>, args: Vec<(Rc<Value>, ())>) -> EvalResult {
    let env = new_env(vec![]);
    let h = HashMap::new();

    // Build the stack with CallWith frames for each argument
    let mut k = Stack::Empty(h);
    for (value, meta) in args.into_iter().rev() {
        k = Stack::Frame(
            super::state::Kontinue::CallWith(value, env.clone()),
            meta,
            Box::new(k),
        );
    }

    eval_loop(super::state::step(Control::Val(f), env, Box::new(k)))
}

/// Resume evaluation with a value
pub fn resume(value: Rc<Value>, env: Env, k: Stack) -> EvalResult {
    eval_loop(super::state::step(Control::Val(value), env, Box::new(k)))
}

/// Create a new environment with the given scope
pub fn new_env(scope: Scope) -> Env {
    Env {
        scope,
        references: HashMap::new(),
        builtins: builtins(),
    }
}

/// Build the builtins map
fn builtins() -> HashMap<String, super::state::Builtin> {
    // For now, return an empty map
    // We'll populate this in Milestone 5
    HashMap::new()
}
