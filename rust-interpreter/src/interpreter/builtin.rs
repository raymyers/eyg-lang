// All built-in functions
// Mirrors packages/gleam_interpreter/src/eyg/interpreter/builtin.gleam

use super::break_reason::BreakReason;
use super::state::{Env, Stack, StepReturn};
use super::value::Value;
use std::rc::Rc;

// ============================================================================
// Equality / control flow
// ============================================================================

/// equal: Arity2 - structural equality
pub fn equal(_left: Rc<Value>, _right: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("equal".to_string()))
}

/// fix: Arity1 - fixed-point combinator
pub fn fix(_builder: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("fix".to_string()))
}

/// fixed: Arity2 - one step of fixed-point unrolling
pub fn fixed(_builder: Rc<Value>, _arg: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("fixed".to_string()))
}

/// never: Arity1 - always returns IncorrectTerm
pub fn never(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("never".to_string()))
}

// ============================================================================
// Integer operations
// ============================================================================

/// int_compare: Arity2 - compare two integers
pub fn int_compare(_left: Rc<Value>, _right: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("int_compare".to_string()))
}

/// int_add: Arity2 - add two integers
pub fn int_add(_left: Rc<Value>, _right: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("int_add".to_string()))
}

/// int_subtract: Arity2 - subtract two integers
pub fn int_subtract(_left: Rc<Value>, _right: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("int_subtract".to_string()))
}

/// int_multiply: Arity2 - multiply two integers
pub fn int_multiply(_left: Rc<Value>, _right: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("int_multiply".to_string()))
}

/// int_divide: Arity2 - divide two integers (returns Result)
pub fn int_divide(_left: Rc<Value>, _right: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("int_divide".to_string()))
}

/// int_absolute: Arity1 - absolute value of an integer
pub fn int_absolute(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("int_absolute".to_string()))
}

/// int_parse: Arity1 - parse a string to an integer
pub fn int_parse(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("int_parse".to_string()))
}

/// int_to_string: Arity1 - convert an integer to a string
pub fn int_to_string(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("int_to_string".to_string()))
}

// ============================================================================
// String operations
// ============================================================================

/// string_append: Arity2 - concatenate two strings
pub fn string_append(_left: Rc<Value>, _right: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_append".to_string()))
}

/// string_split: Arity2 - split a string by a delimiter
pub fn string_split(_value: Rc<Value>, _delimiter: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_split".to_string()))
}

/// string_split_once: Arity2 - split a string once by a delimiter
pub fn string_split_once(_value: Rc<Value>, _delimiter: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_split_once".to_string()))
}

/// string_replace: Arity3 - replace occurrences in a string
pub fn string_replace(_value: Rc<Value>, _pattern: Rc<Value>, _replacement: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_replace".to_string()))
}

/// string_uppercase: Arity1 - convert a string to uppercase
pub fn string_uppercase(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_uppercase".to_string()))
}

/// string_lowercase: Arity1 - convert a string to lowercase
pub fn string_lowercase(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_lowercase".to_string()))
}

/// string_starts_with: Arity2 - check if a string starts with a prefix
pub fn string_starts_with(_value: Rc<Value>, _prefix: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_starts_with".to_string()))
}

/// string_ends_with: Arity2 - check if a string ends with a suffix
pub fn string_ends_with(_value: Rc<Value>, _suffix: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_ends_with".to_string()))
}


/// string_length: Arity1 - get the length of a string
pub fn string_length(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_length".to_string()))
}

/// string_to_binary: Arity1 - convert a string to binary
pub fn string_to_binary(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_to_binary".to_string()))
}

/// string_from_binary: Arity1 - convert binary to a string
pub fn string_from_binary(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("string_from_binary".to_string()))
}

// ============================================================================
// Binary operations
// ============================================================================

/// binary_from_integers: Arity1 - create binary from a list of integers
pub fn binary_from_integers(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("binary_from_integers".to_string()))
}

/// binary_fold: Arity3 - fold over bytes in a binary
pub fn binary_fold(_binary: Rc<Value>, _acc: Rc<Value>, _func: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("binary_fold".to_string()))
}

// ============================================================================
// List operations
// ============================================================================

/// list_pop: Arity1 - pop the head of a list
pub fn list_pop(_value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("list_pop".to_string()))
}

/// list_fold: Arity3 - fold over a list
pub fn list_fold(_list: Rc<Value>, _acc: Rc<Value>, _func: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    // TODO: Implement in Milestone 5
    Err(BreakReason::UndefinedBuiltin("list_fold".to_string()))
}
