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
