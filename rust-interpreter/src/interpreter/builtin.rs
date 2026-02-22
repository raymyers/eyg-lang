// All built-in functions
// Mirrors packages/gleam_interpreter/src/eyg/interpreter/builtin.gleam

use super::break_reason::BreakReason;
use super::state::{Control, Env, Stack, StepReturn};
use super::value::{Switch, Value};
use std::rc::Rc;

// ============================================================================
// Equality / control flow
// ============================================================================

/// equal: Arity2 - structural equality
pub fn equal(left: Rc<Value>, right: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    let value = if left.equals(&right) {
        super::value::true_value()
    } else {
        super::value::false_value()
    };
    Ok((Control::Val(Rc::new(value)), env, k))
}

/// fix: Arity1 - fixed-point combinator
pub fn fix(builder: Rc<Value>, meta: (), env: Env, k: Stack) -> StepReturn {
    let partial = Rc::new(Value::Partial(
        Switch::Builtin("fixed".to_string()),
        vec![builder.clone()],
    ));
    super::state::call(builder, partial, meta, env, k)
}

/// fixed: Arity2 - one step of fixed-point unrolling
pub fn fixed(builder: Rc<Value>, arg: Rc<Value>, meta: (), env: Env, k: Stack) -> StepReturn {
    let partial = Rc::new(Value::Partial(
        Switch::Builtin("fixed".to_string()),
        vec![builder.clone()],
    ));
    let new_k = Stack::Frame(
        super::state::Kontinue::CallWith(arg, env.clone()),
        meta,
        Box::new(k),
    );
    super::state::call(builder, partial, meta, env, new_k)
}

/// never: Arity1 - always returns IncorrectTerm
pub fn never(value: Rc<Value>, _meta: (), _env: Env, _k: Stack) -> StepReturn {
    Err(BreakReason::IncorrectTerm {
        expected: "Never".to_string(),
        got: Box::new((*value).clone()),
    })
}

// ============================================================================
// Integer operations
// ============================================================================

/// int_compare: Arity2 - compare two integers
pub fn int_compare(left: Rc<Value>, right: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let left = cast::as_integer(&left)?;
    let right = cast::as_integer(&right)?;
    let result = match left.cmp(&right) {
        std::cmp::Ordering::Less => Value::Tagged {
            label: "Lt".to_string(),
            value: Rc::new(super::value::unit()),
        },
        std::cmp::Ordering::Equal => Value::Tagged {
            label: "Eq".to_string(),
            value: Rc::new(super::value::unit()),
        },
        std::cmp::Ordering::Greater => Value::Tagged {
            label: "Gt".to_string(),
            value: Rc::new(super::value::unit()),
        },
    };
    Ok((Control::Val(Rc::new(result)), env, k))
}

/// int_add: Arity2 - add two integers
pub fn int_add(left: Rc<Value>, right: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let left = cast::as_integer(&left)?;
    let right = cast::as_integer(&right)?;
    Ok((Control::Val(Rc::new(Value::Integer(left + right))), env, k))
}

/// int_subtract: Arity2 - subtract two integers
pub fn int_subtract(left: Rc<Value>, right: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let left = cast::as_integer(&left)?;
    let right = cast::as_integer(&right)?;
    Ok((Control::Val(Rc::new(Value::Integer(left - right))), env, k))
}

/// int_multiply: Arity2 - multiply two integers
pub fn int_multiply(left: Rc<Value>, right: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let left = cast::as_integer(&left)?;
    let right = cast::as_integer(&right)?;
    Ok((Control::Val(Rc::new(Value::Integer(left * right))), env, k))
}

/// int_divide: Arity2 - divide two integers (returns Result)
pub fn int_divide(left: Rc<Value>, right: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let left = cast::as_integer(&left)?;
    let right = cast::as_integer(&right)?;
    let value = if right == 0 {
        super::value::error(super::value::unit())
    } else {
        super::value::ok(Value::Integer(left / right))
    };
    Ok((Control::Val(Rc::new(value)), env, k))
}

/// int_absolute: Arity1 - absolute value of an integer
pub fn int_absolute(value: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let x = cast::as_integer(&value)?;
    Ok((Control::Val(Rc::new(Value::Integer(x.abs()))), env, k))
}

/// int_parse: Arity1 - parse a string to an integer
pub fn int_parse(value: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let raw = cast::as_string(&value)?;
    let result = match raw.parse::<i64>() {
        Ok(i) => super::value::ok(Value::Integer(i)),
        Err(_) => super::value::error(super::value::unit()),
    };
    Ok((Control::Val(Rc::new(result)), env, k))
}

/// int_to_string: Arity1 - convert an integer to a string
pub fn int_to_string(value: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let x = cast::as_integer(&value)?;
    Ok((Control::Val(Rc::new(Value::Str(x.to_string()))), env, k))
}

// ============================================================================
// String operations
// ============================================================================

/// string_append: Arity2 - concatenate two strings
pub fn string_append(left: Rc<Value>, right: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let left = cast::as_string(&left)?;
    let right = cast::as_string(&right)?;
    Ok((Control::Val(Rc::new(Value::Str(format!("{}{}", left, right)))), env, k))
}

/// string_split: Arity2 - split a string by a delimiter
pub fn string_split(value: Rc<Value>, delimiter: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    use std::collections::HashMap;
    let s = cast::as_string(&value)?;
    let pattern = cast::as_string(&delimiter)?;
    let parts: Vec<String> = s.split(&pattern).map(|s| s.to_string()).collect();

    // Gleam's string.split always returns at least one element
    let (first, rest) = if parts.is_empty() {
        (String::new(), vec![])
    } else {
        (parts[0].clone(), parts[1..].to_vec())
    };

    let tail = Value::LinkedList(
        rest.iter().map(|s| Rc::new(Value::Str(s.clone()))).collect()
    );

    let mut fields = HashMap::new();
    fields.insert("head".to_string(), Rc::new(Value::Str(first)));
    fields.insert("tail".to_string(), Rc::new(tail));

    Ok((Control::Val(Rc::new(Value::Record(fields))), env, k))
}

/// string_split_once: Arity2 - split a string once by a delimiter
pub fn string_split_once(value: Rc<Value>, delimiter: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    use std::collections::HashMap;
    let s = cast::as_string(&value)?;
    let pattern = cast::as_string(&delimiter)?;

    let result = if let Some(pos) = s.find(&pattern) {
        let (pre, post_with_pattern) = s.split_at(pos);
        let post = &post_with_pattern[pattern.len()..];

        let mut fields = HashMap::new();
        fields.insert("pre".to_string(), Rc::new(Value::Str(pre.to_string())));
        fields.insert("post".to_string(), Rc::new(Value::Str(post.to_string())));

        super::value::ok(Value::Record(fields))
    } else {
        super::value::error(super::value::unit())
    };

    Ok((Control::Val(Rc::new(result)), env, k))
}

/// string_replace: Arity3 - replace occurrences in a string
pub fn string_replace(value: Rc<Value>, pattern: Rc<Value>, replacement: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let s = cast::as_string(&value)?;
    let from = cast::as_string(&pattern)?;
    let to = cast::as_string(&replacement)?;

    Ok((Control::Val(Rc::new(Value::Str(s.replace(&from, &to)))), env, k))
}

/// string_uppercase: Arity1 - convert a string to uppercase
pub fn string_uppercase(value: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let s = cast::as_string(&value)?;
    Ok((Control::Val(Rc::new(Value::Str(s.to_uppercase()))), env, k))
}

/// string_lowercase: Arity1 - convert a string to lowercase
pub fn string_lowercase(value: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let s = cast::as_string(&value)?;
    Ok((Control::Val(Rc::new(Value::Str(s.to_lowercase()))), env, k))
}

/// string_starts_with: Arity2 - check if a string starts with a prefix
pub fn string_starts_with(value: Rc<Value>, prefix: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let s = cast::as_string(&value)?;
    let t = cast::as_string(&prefix)?;
    let result = super::value::bool_value(s.starts_with(&t));
    Ok((Control::Val(Rc::new(result)), env, k))
}

/// string_ends_with: Arity2 - check if a string ends with a suffix
pub fn string_ends_with(value: Rc<Value>, suffix: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let s = cast::as_string(&value)?;
    let t = cast::as_string(&suffix)?;
    let result = super::value::bool_value(s.ends_with(&t));
    Ok((Control::Val(Rc::new(result)), env, k))
}

/// string_length: Arity1 - get the length of a string
pub fn string_length(value: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let s = cast::as_string(&value)?;
    Ok((Control::Val(Rc::new(Value::Integer(s.len() as i64))), env, k))
}

/// string_to_binary: Arity1 - convert a string to binary
pub fn string_to_binary(value: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let s = cast::as_string(&value)?;
    Ok((Control::Val(Rc::new(Value::Binary(s.into_bytes()))), env, k))
}

/// string_from_binary: Arity1 - convert binary to a string
pub fn string_from_binary(value: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let bytes = cast::as_binary(&value)?;
    let result = match String::from_utf8(bytes) {
        Ok(s) => super::value::ok(Value::Str(s)),
        Err(_) => super::value::error(super::value::unit()),
    };
    Ok((Control::Val(Rc::new(result)), env, k))
}

// ============================================================================
// Binary operations
// ============================================================================

/// binary_from_integers: Arity1 - create binary from a list of integers
pub fn binary_from_integers(value: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let parts = cast::as_list(&value)?;

    // Build the binary by converting each integer to a byte
    // Process in reverse order to match Gleam's fold behavior
    let mut bytes = Vec::new();
    for part in parts.iter().rev() {
        let i = cast::as_integer(part)?;
        bytes.push(i as u8);
    }
    bytes.reverse();

    Ok((Control::Val(Rc::new(Value::Binary(bytes))), env, k))
}

/// binary_fold: Arity3 - fold over bytes in a binary
pub fn binary_fold(binary: Rc<Value>, state: Rc<Value>, func: Rc<Value>, meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let bytes = cast::as_binary(&binary)?;

    if bytes.is_empty() {
        Ok((Control::Val(state), env, k))
    } else {
        let byte = bytes[0];
        let rest = bytes[1..].to_vec();

        // Build the continuation stack for CPS fold
        let new_k = Stack::Frame(
            super::state::Kontinue::CallWith(state, env.clone()),
            meta,
            Box::new(Stack::Frame(
                super::state::Kontinue::Apply(
                    Rc::new(Value::Partial(
                        Switch::Builtin("binary_fold".to_string()),
                        vec![Rc::new(Value::Binary(rest))],
                    )),
                    env.clone(),
                ),
                meta,
                Box::new(Stack::Frame(
                    super::state::Kontinue::CallWith(func.clone(), env.clone()),
                    meta,
                    Box::new(k),
                )),
            )),
        );

        super::state::call(func, Rc::new(Value::Integer(byte as i64)), meta, env, new_k)
    }
}

// ============================================================================
// List operations
// ============================================================================

/// list_pop: Arity1 - pop the head of a list
pub fn list_pop(value: Rc<Value>, _meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    use std::collections::HashMap;
    let elements = cast::as_list(&value)?;

    let result = if elements.is_empty() {
        super::value::error(super::value::unit())
    } else {
        let head = elements[0].clone();
        let tail = Value::LinkedList(elements[1..].to_vec());

        let mut fields = HashMap::new();
        fields.insert("head".to_string(), head);
        fields.insert("tail".to_string(), Rc::new(tail));

        super::value::ok(Value::Record(fields))
    };

    Ok((Control::Val(Rc::new(result)), env, k))
}

/// list_fold: Arity3 - fold over a list
pub fn list_fold(list: Rc<Value>, state: Rc<Value>, func: Rc<Value>, meta: (), env: Env, k: Stack) -> StepReturn {
    use super::cast;
    let elements = cast::as_list(&list)?;

    if elements.is_empty() {
        Ok((Control::Val(state), env, k))
    } else {
        let element = elements[0].clone();
        let rest = elements[1..].to_vec();

        // Build the continuation stack for CPS fold
        let new_k = Stack::Frame(
            super::state::Kontinue::CallWith(state, env.clone()),
            meta,
            Box::new(Stack::Frame(
                super::state::Kontinue::Apply(
                    Rc::new(Value::Partial(
                        Switch::Builtin("list_fold".to_string()),
                        vec![Rc::new(Value::LinkedList(rest))],
                    )),
                    env.clone(),
                ),
                meta,
                Box::new(Stack::Frame(
                    super::state::Kontinue::CallWith(func.clone(), env.clone()),
                    meta,
                    Box::new(k),
                )),
            )),
        );

        super::state::call(func, element, meta, env, new_k)
    }
}
