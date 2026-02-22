// Error / break reasons
// Mirrors packages/gleam_interpreter/src/eyg/interpreter/break.gleam

use super::value::Value;

/// Reasons why evaluation might break/fail.
/// Mirrors the Reason(m, c) type from break.gleam.
/// Values are boxed to reduce the size of the enum.
#[derive(Debug, Clone)]
pub enum BreakReason {
    NotAFunction(Box<Value>),
    UndefinedVariable(String),
    UndefinedBuiltin(String),
    UndefinedReference(String),
    UndefinedRelease {
        package: String,
        release: i64,
        cid: String,
    },
    Vacant,
    NoMatch(Box<Value>),
    UnhandledEffect(String, Box<Value>),
    IncorrectTerm {
        expected: String,
        got: Box<Value>,
    },
    MissingField(String),
}
