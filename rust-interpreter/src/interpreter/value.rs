// Runtime value types
// Mirrors packages/gleam_interpreter/src/eyg/interpreter/value.gleam

use crate::ir::ast::Node;
use std::collections::HashMap;
use std::rc::Rc;

/// Scope is a list of variable bindings (name -> value).
/// Most-recently-bound wins (linear scan from head).
pub type Scope = Vec<(String, Rc<Value>)>;

/// Context represents a captured delimited continuation for effect handlers.
/// It's a tuple of (popped stack frames, environment).
pub type Context = (Vec<(super::state::Kontinue, ())>, super::state::Env);

/// Runtime values in the interpreter.
/// Mirrors the Value(m, context) type from value.gleam.
#[derive(Debug, Clone)]
pub enum Value {
    Binary(Vec<u8>),
    Integer(i64),
    Str(String),
    LinkedList(Vec<Rc<Value>>),
    Record(HashMap<String, Rc<Value>>),
    Tagged {
        label: String,
        value: Rc<Value>,
    },
    Closure {
        param: String,
        body: Box<Node>,
        env: Scope,
    },
    Partial(Switch, Vec<Rc<Value>>),
}

/// Switch represents partially-applied operations.
/// Mirrors the Switch(context) type from value.gleam.
#[derive(Debug, Clone)]
pub enum Switch {
    Cons,
    Extend(String),
    Overwrite(String),
    Select(String),
    Tag(String),
    Match(String),
    NoCases,
    Perform(String),
    Handle(String),
    Resume(Context),
    Builtin(String),
}

// Helper functions for common values

/// Unit value (empty record)
pub fn unit() -> Value {
    Value::Record(HashMap::new())
}

/// True value
pub fn true_value() -> Value {
    Value::Tagged {
        label: "True".to_string(),
        value: Rc::new(unit()),
    }
}

/// False value
pub fn false_value() -> Value {
    Value::Tagged {
        label: "False".to_string(),
        value: Rc::new(unit()),
    }
}

/// Boolean value
pub fn bool_value(b: bool) -> Value {
    if b {
        true_value()
    } else {
        false_value()
    }
}

/// Ok value
pub fn ok(value: Value) -> Value {
    Value::Tagged {
        label: "Ok".to_string(),
        value: Rc::new(value),
    }
}

/// Error value
pub fn error(reason: Value) -> Value {
    Value::Tagged {
        label: "Error".to_string(),
        value: Rc::new(reason),
    }
}

/// Some value
pub fn some(value: Value) -> Value {
    Value::Tagged {
        label: "Some".to_string(),
        value: Rc::new(value),
    }
}

/// None value
pub fn none() -> Value {
    Value::Tagged {
        label: "None".to_string(),
        value: Rc::new(unit()),
    }
}

/// Structural equality for values
/// Mirrors Gleam's == operator behavior
impl Value {
    pub fn equals(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Binary(a), Value::Binary(b)) => a == b,
            (Value::Integer(a), Value::Integer(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::LinkedList(a), Value::LinkedList(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.equals(y))
            }
            (Value::Record(a), Value::Record(b)) => {
                a.len() == b.len() && a.iter().all(|(k, v)| {
                    b.get(k).is_some_and(|v2| v.equals(v2))
                })
            }
            (Value::Tagged { label: l1, value: v1 }, Value::Tagged { label: l2, value: v2 }) => {
                l1 == l2 && v1.equals(v2)
            }
            (Value::Closure { param: p1, body: b1, env: e1 },
             Value::Closure { param: p2, body: b2, env: e2 }) => {
                // Closures are equal if they have the same structure
                // Note: This is a simplified comparison
                p1 == p2 && b1 == b2 && e1.len() == e2.len()
            }
            (Value::Partial(s1, args1), Value::Partial(s2, args2)) => {
                switch_equals(s1, s2) && args1.len() == args2.len()
                    && args1.iter().zip(args2.iter()).all(|(x, y)| x.equals(y))
            }
            _ => false,
        }
    }
}

fn switch_equals(s1: &Switch, s2: &Switch) -> bool {
    match (s1, s2) {
        (Switch::Cons, Switch::Cons) => true,
        (Switch::Extend(a), Switch::Extend(b)) => a == b,
        (Switch::Overwrite(a), Switch::Overwrite(b)) => a == b,
        (Switch::Select(a), Switch::Select(b)) => a == b,
        (Switch::Tag(a), Switch::Tag(b)) => a == b,
        (Switch::Match(a), Switch::Match(b)) => a == b,
        (Switch::NoCases, Switch::NoCases) => true,
        (Switch::Perform(a), Switch::Perform(b)) => a == b,
        (Switch::Handle(a), Switch::Handle(b)) => a == b,
        (Switch::Resume(_), Switch::Resume(_)) => false, // Contexts are not comparable
        (Switch::Builtin(a), Switch::Builtin(b)) => a == b,
        _ => false,
    }
}
