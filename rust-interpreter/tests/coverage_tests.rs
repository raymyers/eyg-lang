// Comprehensive tests targeting coverage gaps across the interpreter
use rust_interpreter::interpreter::break_reason::BreakReason;
use rust_interpreter::interpreter::builtin;
use rust_interpreter::interpreter::cast;
use rust_interpreter::interpreter::expression;
use rust_interpreter::interpreter::state::{Builtin, Control, Env, Stack};
use rust_interpreter::interpreter::value::{self, Switch, Value};
use rust_interpreter::interpreter::value_json;
use rust_interpreter::ir::ast::{self, Expr, Node};

use im;
use std::rc::Rc;

fn empty_env() -> Env {
    Env {
        scope: im::Vector::new(),
        references: im::HashMap::new(),
        builtins: im::HashMap::new(),
    }
}

fn empty_stack() -> Stack {
    Stack::Empty(im::HashMap::new())
}

/// Extract the value from a successful StepReturn
fn extract_val(
    result: Result<(Control, Env, Stack), Box<(BreakReason, (), Env, Stack)>>,
) -> Rc<Value> {
    let (control, _, _) = result.expect("expected Ok");
    match control {
        Control::Val(v) => v,
        _ => panic!("expected Val control"),
    }
}

// ============================================================================
// break_reason::Display tests (0% -> ~100%)
// ============================================================================
mod break_reason_display {
    use super::*;

    #[test]
    fn not_a_function() {
        let br = BreakReason::NotAFunction(Box::new(Value::Integer(42)));
        assert_eq!(format!("{br}"), "Not a function: 42");
    }

    #[test]
    fn undefined_variable() {
        let br = BreakReason::UndefinedVariable("x".into());
        assert_eq!(format!("{br}"), "Undefined variable: x");
    }

    #[test]
    fn undefined_builtin() {
        let br = BreakReason::UndefinedBuiltin("foo".into());
        assert_eq!(format!("{br}"), "Undefined builtin: foo");
    }

    #[test]
    fn undefined_reference() {
        let br = BreakReason::UndefinedReference("abc123".into());
        assert_eq!(format!("{br}"), "Undefined reference: abc123");
    }

    #[test]
    fn undefined_release() {
        let br = BreakReason::UndefinedRelease {
            package: "mypkg".into(),
            release: 3,
            cid: "cidxyz".into(),
        };
        assert_eq!(format!("{br}"), "Undefined release: mypkg/3 (cidxyz)");
    }

    #[test]
    fn vacant() {
        assert_eq!(format!("{}", BreakReason::Vacant), "Vacant");
    }

    #[test]
    fn no_match() {
        let br = BreakReason::NoMatch(Box::new(Value::Str("hi".into())));
        assert_eq!(format!("{br}"), "No match for: \"hi\"");
    }

    #[test]
    fn unhandled_effect() {
        let br = BreakReason::UnhandledEffect("Log".into(), Box::new(Value::Integer(1)));
        assert_eq!(format!("{br}"), "Unhandled effect 'Log' with value: 1");
    }

    #[test]
    fn incorrect_term() {
        let br = BreakReason::IncorrectTerm {
            expected: "Integer".into(),
            got: Box::new(Value::Str("nope".into())),
        };
        assert_eq!(format!("{br}"), "Incorrect term: expected Integer, got \"nope\"");
    }

    #[test]
    fn missing_field() {
        let br = BreakReason::MissingField("name".into());
        assert_eq!(format!("{br}"), "Missing field: name");
    }
}

// ============================================================================
// value::Display tests (covers all Value variants + display_partial)
// ============================================================================
mod value_display {
    use super::*;

    #[test]
    fn display_integer() {
        assert_eq!(format!("{}", Value::Integer(42)), "42");
        assert_eq!(format!("{}", Value::Integer(-7)), "-7");
    }

    #[test]
    fn display_string() {
        assert_eq!(format!("{}", Value::Str("hello".into())), "\"hello\"");
    }

    #[test]
    fn display_binary_empty() {
        assert_eq!(format!("{}", Value::Binary(vec![])), "<<>>");
    }

    #[test]
    fn display_binary_single() {
        assert_eq!(format!("{}", Value::Binary(vec![65])), "<<65>>");
    }

    #[test]
    fn display_binary_multiple() {
        assert_eq!(format!("{}", Value::Binary(vec![1, 2, 3])), "<<1, 2, 3>>");
    }

    #[test]
    fn display_binary_negative_cast() {
        // 200u8 as i8 is -56
        assert_eq!(format!("{}", Value::Binary(vec![200])), "<<-56>>");
    }

    #[test]
    fn display_linked_list_empty() {
        assert_eq!(format!("{}", Value::LinkedList(vec![])), "[]");
    }

    #[test]
    fn display_linked_list_items() {
        let items = vec![
            Rc::new(Value::Integer(1)),
            Rc::new(Value::Integer(2)),
            Rc::new(Value::Integer(3)),
        ];
        assert_eq!(format!("{}", Value::LinkedList(items)), "[1, 2, 3]");
    }

    #[test]
    fn display_record_empty() {
        assert_eq!(format!("{}", Value::Record(im::HashMap::new())), "{}");
    }

    #[test]
    fn display_record_fields() {
        let mut fields = im::HashMap::new();
        fields.insert("x".to_string(), Rc::new(Value::Integer(10)));
        let display = format!("{}", Value::Record(fields));
        assert!(display.starts_with('{'));
        assert!(display.ends_with('}'));
        assert!(display.contains("x: 10"));
    }

    #[test]
    fn display_record_multiple_fields() {
        let mut fields = im::HashMap::new();
        fields.insert("a".to_string(), Rc::new(Value::Integer(1)));
        fields.insert("b".to_string(), Rc::new(Value::Integer(2)));
        let display = format!("{}", Value::Record(fields));
        assert!(display.contains("a: 1"));
        assert!(display.contains("b: 2"));
        assert!(display.contains(", "));
    }

    #[test]
    fn display_tagged() {
        let v = Value::Tagged {
            label: "Ok".into(),
            value: Rc::new(Value::Integer(5)),
        };
        assert_eq!(format!("{v}"), "Ok(5)");
    }

    #[test]
    fn display_closure() {
        let v = Value::Closure {
            param: "x".into(),
            body: Box::new(Node(Expr::Variable { label: "x".into() }, ())),
            env: im::Vector::new(),
        };
        assert_eq!(format!("{v}"), "(x) -> { ... }");
    }

    // display_partial coverage
    #[test]
    fn display_partial_cons_no_args() {
        let v = Value::Partial(Switch::Cons, vec![]);
        assert_eq!(format!("{v}"), "cons");
    }

    #[test]
    fn display_partial_cons_with_args() {
        let v = Value::Partial(Switch::Cons, vec![Rc::new(Value::Integer(1))]);
        assert_eq!(format!("{v}"), "cons(1)");
    }

    #[test]
    fn display_partial_extend_no_args() {
        let v = Value::Partial(Switch::Extend("name".into()), vec![]);
        assert_eq!(format!("{v}"), "+name");
    }

    #[test]
    fn display_partial_extend_with_args() {
        let v = Value::Partial(
            Switch::Extend("name".into()),
            vec![Rc::new(Value::Str("alice".into()))],
        );
        assert_eq!(format!("{v}"), "+name(\"alice\")");
    }

    #[test]
    fn display_partial_select() {
        let v = Value::Partial(Switch::Select("age".into()), vec![]);
        assert_eq!(format!("{v}"), ".age");
    }

    #[test]
    fn display_partial_overwrite() {
        let v = Value::Partial(Switch::Overwrite("age".into()), vec![]);
        assert_eq!(format!("{v}"), ":=age");
    }

    #[test]
    fn display_partial_tag_no_args() {
        let v = Value::Partial(Switch::Tag("Ok".into()), vec![]);
        assert_eq!(format!("{v}"), "Ok");
    }

    #[test]
    fn display_partial_tag_with_args() {
        let v = Value::Partial(Switch::Tag("Ok".into()), vec![Rc::new(Value::Integer(1))]);
        assert_eq!(format!("{v}"), "Ok(1)");
    }

    #[test]
    fn display_partial_match() {
        let v = Value::Partial(Switch::Match("Some".into()), vec![]);
        assert_eq!(format!("{v}"), "case Some");
    }

    #[test]
    fn display_partial_no_cases() {
        let v = Value::Partial(Switch::NoCases, vec![]);
        assert_eq!(format!("{v}"), "nocases");
    }

    #[test]
    fn display_partial_perform() {
        let v = Value::Partial(Switch::Perform("Log".into()), vec![]);
        assert_eq!(format!("{v}"), "^Log");
    }

    #[test]
    fn display_partial_handle_no_args() {
        let v = Value::Partial(Switch::Handle("Log".into()), vec![]);
        assert_eq!(format!("{v}"), "deep Log");
    }

    #[test]
    fn display_partial_handle_with_args() {
        let v = Value::Partial(
            Switch::Handle("Log".into()),
            vec![Rc::new(Value::Integer(0))],
        );
        assert_eq!(format!("{v}"), "deep Log(0)");
    }

    #[test]
    fn display_partial_resume() {
        let ctx = (vec![], Env {
            scope: im::Vector::new(),
            references: im::HashMap::new(),
            builtins: im::HashMap::new(),
        });
        let v = Value::Partial(Switch::Resume(ctx), vec![]);
        assert_eq!(format!("{v}"), "resume");
    }

    #[test]
    fn display_partial_builtin() {
        let v = Value::Partial(
            Switch::Builtin("int_add".into()),
            vec![Rc::new(Value::Integer(3))],
        );
        assert_eq!(format!("{v}"), "Defunc int_add (3)");
    }

    #[test]
    fn display_partial_builtin_multi_args() {
        let v = Value::Partial(
            Switch::Builtin("string_replace".into()),
            vec![
                Rc::new(Value::Str("a".into())),
                Rc::new(Value::Str("b".into())),
            ],
        );
        assert_eq!(format!("{v}"), "Defunc string_replace (\"a\", \"b\")");
    }
}

// ============================================================================
// value::equals tests
// ============================================================================
mod value_equals {
    use super::*;

    #[test]
    fn binary_equal() {
        let a = Value::Binary(vec![1, 2, 3]);
        let b = Value::Binary(vec![1, 2, 3]);
        assert!(a.equals(&b));
    }

    #[test]
    fn binary_not_equal() {
        let a = Value::Binary(vec![1, 2]);
        let b = Value::Binary(vec![1, 3]);
        assert!(!a.equals(&b));
    }

    #[test]
    fn list_equal() {
        let a = Value::LinkedList(vec![Rc::new(Value::Integer(1)), Rc::new(Value::Integer(2))]);
        let b = Value::LinkedList(vec![Rc::new(Value::Integer(1)), Rc::new(Value::Integer(2))]);
        assert!(a.equals(&b));
    }

    #[test]
    fn list_not_equal_length() {
        let a = Value::LinkedList(vec![Rc::new(Value::Integer(1))]);
        let b = Value::LinkedList(vec![Rc::new(Value::Integer(1)), Rc::new(Value::Integer(2))]);
        assert!(!a.equals(&b));
    }

    #[test]
    fn list_not_equal_values() {
        let a = Value::LinkedList(vec![Rc::new(Value::Integer(1))]);
        let b = Value::LinkedList(vec![Rc::new(Value::Integer(2))]);
        assert!(!a.equals(&b));
    }

    #[test]
    fn record_equal() {
        let mut fa = im::HashMap::new();
        fa.insert("x".to_string(), Rc::new(Value::Integer(1)));
        let mut fb = im::HashMap::new();
        fb.insert("x".to_string(), Rc::new(Value::Integer(1)));
        assert!(Value::Record(fa).equals(&Value::Record(fb)));
    }

    #[test]
    fn record_not_equal_different_key() {
        let mut fa = im::HashMap::new();
        fa.insert("x".to_string(), Rc::new(Value::Integer(1)));
        let mut fb = im::HashMap::new();
        fb.insert("y".to_string(), Rc::new(Value::Integer(1)));
        assert!(!Value::Record(fa).equals(&Value::Record(fb)));
    }

    #[test]
    fn record_not_equal_different_value() {
        let mut fa = im::HashMap::new();
        fa.insert("x".to_string(), Rc::new(Value::Integer(1)));
        let mut fb = im::HashMap::new();
        fb.insert("x".to_string(), Rc::new(Value::Integer(2)));
        assert!(!Value::Record(fa).equals(&Value::Record(fb)));
    }

    #[test]
    fn record_not_equal_different_size() {
        let mut fa = im::HashMap::new();
        fa.insert("x".to_string(), Rc::new(Value::Integer(1)));
        let fb = im::HashMap::new();
        assert!(!Value::Record(fa).equals(&Value::Record(fb)));
    }

    #[test]
    fn tagged_equal() {
        let a = Value::Tagged {
            label: "Ok".into(),
            value: Rc::new(Value::Integer(1)),
        };
        let b = Value::Tagged {
            label: "Ok".into(),
            value: Rc::new(Value::Integer(1)),
        };
        assert!(a.equals(&b));
    }

    #[test]
    fn tagged_not_equal_label() {
        let a = Value::Tagged {
            label: "Ok".into(),
            value: Rc::new(Value::Integer(1)),
        };
        let b = Value::Tagged {
            label: "Err".into(),
            value: Rc::new(Value::Integer(1)),
        };
        assert!(!a.equals(&b));
    }

    #[test]
    fn tagged_not_equal_value() {
        let a = Value::Tagged {
            label: "Ok".into(),
            value: Rc::new(Value::Integer(1)),
        };
        let b = Value::Tagged {
            label: "Ok".into(),
            value: Rc::new(Value::Integer(2)),
        };
        assert!(!a.equals(&b));
    }

    #[test]
    fn closure_equal_same_structure() {
        let body = Box::new(Node(Expr::Variable { label: "x".into() }, ()));
        let a = Value::Closure {
            param: "x".into(),
            body: body.clone(),
            env: im::Vector::new(),
        };
        let b = Value::Closure {
            param: "x".into(),
            body: body,
            env: im::Vector::new(),
        };
        assert!(a.equals(&b));
    }

    #[test]
    fn closure_not_equal_different_param() {
        let body = Box::new(Node(Expr::Variable { label: "x".into() }, ()));
        let a = Value::Closure {
            param: "x".into(),
            body: body.clone(),
            env: im::Vector::new(),
        };
        let b = Value::Closure {
            param: "y".into(),
            body: body,
            env: im::Vector::new(),
        };
        assert!(!a.equals(&b));
    }

    #[test]
    fn partial_equal() {
        let a = Value::Partial(Switch::Cons, vec![Rc::new(Value::Integer(1))]);
        let b = Value::Partial(Switch::Cons, vec![Rc::new(Value::Integer(1))]);
        assert!(a.equals(&b));
    }

    #[test]
    fn partial_not_equal_switch() {
        let a = Value::Partial(Switch::Cons, vec![]);
        let b = Value::Partial(Switch::NoCases, vec![]);
        assert!(!a.equals(&b));
    }

    #[test]
    fn partial_not_equal_args() {
        let a = Value::Partial(Switch::Cons, vec![Rc::new(Value::Integer(1))]);
        let b = Value::Partial(Switch::Cons, vec![Rc::new(Value::Integer(2))]);
        assert!(!a.equals(&b));
    }

    #[test]
    fn mixed_types_not_equal() {
        assert!(!Value::Integer(1).equals(&Value::Str("1".into())));
        assert!(!Value::Binary(vec![]).equals(&Value::LinkedList(vec![])));
    }

    // switch_equals coverage
    #[test]
    fn switch_equals_all_variants() {
        // Test via Value::Partial equals
        let cases: Vec<(Switch, Switch, bool)> = vec![
            (Switch::Cons, Switch::Cons, true),
            (Switch::Extend("a".into()), Switch::Extend("a".into()), true),
            (Switch::Extend("a".into()), Switch::Extend("b".into()), false),
            (Switch::Overwrite("a".into()), Switch::Overwrite("a".into()), true),
            (Switch::Overwrite("a".into()), Switch::Overwrite("b".into()), false),
            (Switch::Select("a".into()), Switch::Select("a".into()), true),
            (Switch::Select("a".into()), Switch::Select("b".into()), false),
            (Switch::Tag("a".into()), Switch::Tag("a".into()), true),
            (Switch::Tag("a".into()), Switch::Tag("b".into()), false),
            (Switch::Match("a".into()), Switch::Match("a".into()), true),
            (Switch::Match("a".into()), Switch::Match("b".into()), false),
            (Switch::NoCases, Switch::NoCases, true),
            (Switch::Perform("a".into()), Switch::Perform("a".into()), true),
            (Switch::Perform("a".into()), Switch::Perform("b".into()), false),
            (Switch::Handle("a".into()), Switch::Handle("a".into()), true),
            (Switch::Handle("a".into()), Switch::Handle("b".into()), false),
            (Switch::Builtin("a".into()), Switch::Builtin("a".into()), true),
            (Switch::Builtin("a".into()), Switch::Builtin("b".into()), false),
            // Resume is always false
            (
                Switch::Resume((vec![], empty_env())),
                Switch::Resume((vec![], empty_env())),
                false,
            ),
            // Mixed types
            (Switch::Cons, Switch::NoCases, false),
        ];
        for (s1, s2, expected) in cases {
            let a = Value::Partial(s1, vec![]);
            let b = Value::Partial(s2, vec![]);
            assert_eq!(a.equals(&b), expected);
        }
    }
}

// ============================================================================
// value helper functions
// ============================================================================
mod value_helpers {
    use super::*;

    #[test]
    fn unit_is_empty_record() {
        match value::unit() {
            Value::Record(fields) => assert!(fields.is_empty()),
            _ => panic!("unit should be empty record"),
        }
    }

    #[test]
    fn true_value() {
        match value::true_value() {
            Value::Tagged { label, .. } => assert_eq!(label, "True"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn false_value() {
        match value::false_value() {
            Value::Tagged { label, .. } => assert_eq!(label, "False"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn bool_value_true() {
        match value::bool_value(true) {
            Value::Tagged { label, .. } => assert_eq!(label, "True"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn bool_value_false() {
        match value::bool_value(false) {
            Value::Tagged { label, .. } => assert_eq!(label, "False"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn ok_value() {
        match value::ok(Value::Integer(5)) {
            Value::Tagged { label, value } => {
                assert_eq!(label, "Ok");
                assert!(matches!(value.as_ref(), Value::Integer(5)));
            }
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn error_value() {
        match value::error(Value::Str("oops".into())) {
            Value::Tagged { label, value } => {
                assert_eq!(label, "Error");
                assert!(matches!(value.as_ref(), Value::Str(s) if s == "oops"));
            }
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn some_value() {
        match value::some(Value::Integer(10)) {
            Value::Tagged { label, value } => {
                assert_eq!(label, "Some");
                assert!(matches!(value.as_ref(), Value::Integer(10)));
            }
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn none_value() {
        match value::none() {
            Value::Tagged { label, .. } => assert_eq!(label, "None"),
            _ => panic!("expected Tagged"),
        }
    }
}

// ============================================================================
// cast tests (error paths)
// ============================================================================
mod cast_tests {
    use super::*;

    #[test]
    fn as_integer_ok() {
        assert_eq!(cast::as_integer(&Value::Integer(42)).unwrap(), 42);
    }

    #[test]
    fn as_integer_err() {
        let result = cast::as_integer(&Value::Str("nope".into()));
        assert!(result.is_err());
        match result.unwrap_err() {
            BreakReason::IncorrectTerm { expected, .. } => assert_eq!(expected, "Integer"),
            _ => panic!("wrong error"),
        }
    }

    #[test]
    fn as_string_ok() {
        assert_eq!(cast::as_string(&Value::Str("hi".into())).unwrap(), "hi");
    }

    #[test]
    fn as_string_err() {
        let result = cast::as_string(&Value::Integer(5));
        assert!(result.is_err());
        match result.unwrap_err() {
            BreakReason::IncorrectTerm { expected, .. } => assert_eq!(expected, "String"),
            _ => panic!("wrong error"),
        }
    }

    #[test]
    fn as_binary_ok() {
        assert_eq!(cast::as_binary(&Value::Binary(vec![1, 2])).unwrap(), &[1, 2]);
    }

    #[test]
    fn as_binary_err() {
        let result = cast::as_binary(&Value::Integer(5));
        assert!(result.is_err());
        match result.unwrap_err() {
            BreakReason::IncorrectTerm { expected, .. } => assert_eq!(expected, "Binary"),
            _ => panic!("wrong error"),
        }
    }

    #[test]
    fn as_list_ok() {
        let v = Value::LinkedList(vec![Rc::new(Value::Integer(1))]);
        let result = cast::as_list(&v).unwrap();
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn as_list_err() {
        let result = cast::as_list(&Value::Integer(5));
        assert!(result.is_err());
        match result.unwrap_err() {
            BreakReason::IncorrectTerm { expected, .. } => assert_eq!(expected, "List"),
            _ => panic!("wrong error"),
        }
    }

    #[test]
    fn as_record_ok() {
        let v = Value::Record(im::HashMap::new());
        assert!(cast::as_record(&v).is_ok());
    }

    #[test]
    fn as_record_err() {
        let result = cast::as_record(&Value::Integer(5));
        assert!(result.is_err());
        match result.unwrap_err() {
            BreakReason::IncorrectTerm { expected, .. } => assert_eq!(expected, "Record"),
            _ => panic!("wrong error"),
        }
    }

    #[test]
    fn as_tagged_ok() {
        let v = Value::Tagged {
            label: "Ok".into(),
            value: Rc::new(Value::Integer(1)),
        };
        let (label, _) = cast::as_tagged(&v).unwrap();
        assert_eq!(label, "Ok");
    }

    #[test]
    fn as_tagged_err() {
        let result = cast::as_tagged(&Value::Integer(5));
        assert!(result.is_err());
        match result.unwrap_err() {
            BreakReason::IncorrectTerm { expected, .. } => assert_eq!(expected, "Tagged"),
            _ => panic!("wrong error"),
        }
    }
}

// ============================================================================
// builtin tests (untested functions)
// ============================================================================
mod builtin_tests {
    use super::*;

    #[test]
    fn never_returns_error() {
        let v = Rc::new(Value::Integer(42));
        let result = builtin::never(&v, (), empty_env(), empty_stack());
        assert!(result.is_err());
        let debug = result.unwrap_err();
        match &debug.0 {
            BreakReason::IncorrectTerm { expected, .. } => assert_eq!(expected, "Never"),
            _ => panic!("expected IncorrectTerm"),
        }
    }

    #[test]
    fn int_compare_less() {
        let v = extract_val(builtin::int_compare(
            &Rc::new(Value::Integer(1)),
            &Rc::new(Value::Integer(5)),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "Lt"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn int_compare_equal() {
        let v = extract_val(builtin::int_compare(
            &Rc::new(Value::Integer(3)),
            &Rc::new(Value::Integer(3)),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "Eq"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn int_compare_greater() {
        let v = extract_val(builtin::int_compare(
            &Rc::new(Value::Integer(10)),
            &Rc::new(Value::Integer(3)),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "Gt"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn int_compare_type_error() {
        let result = builtin::int_compare(
            &Rc::new(Value::Str("nope".into())),
            &Rc::new(Value::Integer(3)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn int_absolute() {
        let v = extract_val(builtin::int_absolute(
            &Rc::new(Value::Integer(-7)),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Integer(7)));
    }

    #[test]
    fn int_absolute_positive() {
        let v = extract_val(builtin::int_absolute(
            &Rc::new(Value::Integer(5)),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Integer(5)));
    }

    #[test]
    fn int_absolute_type_error() {
        let result = builtin::int_absolute(
            &Rc::new(Value::Str("x".into())),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn int_parse_ok() {
        let v = extract_val(builtin::int_parse(
            &Rc::new(Value::Str("42".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, value } => {
                assert_eq!(label, "Ok");
                assert!(matches!(value.as_ref(), Value::Integer(42)));
            }
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn int_parse_error() {
        let v = extract_val(builtin::int_parse(
            &Rc::new(Value::Str("abc".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "Error"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn int_parse_type_error() {
        let result = builtin::int_parse(
            &Rc::new(Value::Integer(42)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn int_to_string() {
        let v = extract_val(builtin::int_to_string(
            &Rc::new(Value::Integer(42)),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Str(s) if s == "42"));
    }

    #[test]
    fn int_to_string_type_error() {
        let result = builtin::int_to_string(
            &Rc::new(Value::Str("x".into())),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_split_basic() {
        let v = extract_val(builtin::string_split(
            &Rc::new(Value::Str("a,b,c".into())),
            &Rc::new(Value::Str(",".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Record(fields) => {
                let head = fields.get("head").unwrap();
                assert!(matches!(head.as_ref(), Value::Str(s) if s == "a"));
                let tail = fields.get("tail").unwrap();
                match tail.as_ref() {
                    Value::LinkedList(items) => assert_eq!(items.len(), 2),
                    _ => panic!("expected list tail"),
                }
            }
            _ => panic!("expected Record"),
        }
    }

    #[test]
    fn string_split_empty_delimiter() {
        let v = extract_val(builtin::string_split(
            &Rc::new(Value::Str("abc".into())),
            &Rc::new(Value::Str("".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Record(fields) => {
                let head = fields.get("head").unwrap();
                assert!(matches!(head.as_ref(), Value::Str(s) if s == "a"));
            }
            _ => panic!("expected Record"),
        }
    }

    #[test]
    fn string_split_type_error() {
        let result = builtin::string_split(
            &Rc::new(Value::Integer(5)),
            &Rc::new(Value::Str(",".into())),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_split_once_found() {
        let v = extract_val(builtin::string_split_once(
            &Rc::new(Value::Str("hello-world-test".into())),
            &Rc::new(Value::Str("-".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, value } => {
                assert_eq!(label, "Ok");
                match value.as_ref() {
                    Value::Record(fields) => {
                        let pre = fields.get("pre").unwrap();
                        assert!(matches!(pre.as_ref(), Value::Str(s) if s == "hello"));
                        let post = fields.get("post").unwrap();
                        assert!(matches!(post.as_ref(), Value::Str(s) if s == "world-test"));
                    }
                    _ => panic!("expected Record"),
                }
            }
            _ => panic!("expected Tagged Ok"),
        }
    }

    #[test]
    fn string_split_once_not_found() {
        let v = extract_val(builtin::string_split_once(
            &Rc::new(Value::Str("hello".into())),
            &Rc::new(Value::Str("-".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "Error"),
            _ => panic!("expected Tagged Error"),
        }
    }

    #[test]
    fn string_split_once_type_error() {
        let result = builtin::string_split_once(
            &Rc::new(Value::Integer(5)),
            &Rc::new(Value::Str(",".into())),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_replace() {
        let v = extract_val(builtin::string_replace(
            &Rc::new(Value::Str("hello world".into())),
            &Rc::new(Value::Str("world".into())),
            &Rc::new(Value::Str("rust".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Str(s) if s == "hello rust"));
    }

    #[test]
    fn string_replace_type_error() {
        let result = builtin::string_replace(
            &Rc::new(Value::Integer(5)),
            &Rc::new(Value::Str("a".into())),
            &Rc::new(Value::Str("b".into())),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_uppercase() {
        let v = extract_val(builtin::string_uppercase(
            &Rc::new(Value::Str("hello".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Str(s) if s == "HELLO"));
    }

    #[test]
    fn string_uppercase_type_error() {
        let result = builtin::string_uppercase(
            &Rc::new(Value::Integer(5)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_lowercase() {
        let v = extract_val(builtin::string_lowercase(
            &Rc::new(Value::Str("HELLO".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Str(s) if s == "hello"));
    }

    #[test]
    fn string_lowercase_type_error() {
        let result = builtin::string_lowercase(
            &Rc::new(Value::Integer(5)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_starts_with_true() {
        let v = extract_val(builtin::string_starts_with(
            &Rc::new(Value::Str("hello world".into())),
            &Rc::new(Value::Str("hello".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "True"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn string_starts_with_false() {
        let v = extract_val(builtin::string_starts_with(
            &Rc::new(Value::Str("hello".into())),
            &Rc::new(Value::Str("world".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "False"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn string_starts_with_type_error() {
        let result = builtin::string_starts_with(
            &Rc::new(Value::Integer(5)),
            &Rc::new(Value::Str("a".into())),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_ends_with_true() {
        let v = extract_val(builtin::string_ends_with(
            &Rc::new(Value::Str("hello world".into())),
            &Rc::new(Value::Str("world".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "True"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn string_ends_with_false() {
        let v = extract_val(builtin::string_ends_with(
            &Rc::new(Value::Str("hello".into())),
            &Rc::new(Value::Str("world".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "False"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn string_ends_with_type_error() {
        let result = builtin::string_ends_with(
            &Rc::new(Value::Integer(5)),
            &Rc::new(Value::Str("a".into())),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_length_ascii() {
        let v = extract_val(builtin::string_length(
            &Rc::new(Value::Str("hello".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Integer(5)));
    }

    #[test]
    fn string_length_unicode() {
        // "é" is one grapheme cluster
        let v = extract_val(builtin::string_length(
            &Rc::new(Value::Str("café".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Integer(4)));
    }

    #[test]
    fn string_length_type_error() {
        let result = builtin::string_length(
            &Rc::new(Value::Integer(5)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_to_binary() {
        let v = extract_val(builtin::string_to_binary(
            &Rc::new(Value::Str("AB".into())),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Binary(b) if b == &vec![65, 66]));
    }

    #[test]
    fn string_to_binary_type_error() {
        let result = builtin::string_to_binary(
            &Rc::new(Value::Integer(5)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_from_binary_ok() {
        let v = extract_val(builtin::string_from_binary(
            &Rc::new(Value::Binary(vec![72, 105])),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, value } => {
                assert_eq!(label, "Ok");
                assert!(matches!(value.as_ref(), Value::Str(s) if s == "Hi"));
            }
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn string_from_binary_invalid_utf8() {
        let v = extract_val(builtin::string_from_binary(
            &Rc::new(Value::Binary(vec![0xFF, 0xFE])),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "Error"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn string_from_binary_type_error() {
        let result = builtin::string_from_binary(
            &Rc::new(Value::Integer(5)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn binary_from_integers_basic() {
        let items = vec![
            Rc::new(Value::Integer(65)),
            Rc::new(Value::Integer(66)),
            Rc::new(Value::Integer(67)),
        ];
        let v = extract_val(builtin::binary_from_integers(
            &Rc::new(Value::LinkedList(items)),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Binary(b) if b == &vec![65, 66, 67]));
    }

    #[test]
    fn binary_from_integers_empty() {
        let v = extract_val(builtin::binary_from_integers(
            &Rc::new(Value::LinkedList(vec![])),
            (),
            empty_env(),
            empty_stack(),
        ));
        assert!(matches!(v.as_ref(), Value::Binary(b) if b.is_empty()));
    }

    #[test]
    fn binary_from_integers_type_error() {
        let result = builtin::binary_from_integers(
            &Rc::new(Value::Integer(5)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn list_pop_nonempty() {
        let items = vec![
            Rc::new(Value::Integer(1)),
            Rc::new(Value::Integer(2)),
            Rc::new(Value::Integer(3)),
        ];
        let v = extract_val(builtin::list_pop(
            &Rc::new(Value::LinkedList(items)),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, value } => {
                assert_eq!(label, "Ok");
                match value.as_ref() {
                    Value::Record(fields) => {
                        let head = fields.get("head").unwrap();
                        assert!(matches!(head.as_ref(), Value::Integer(1)));
                        let tail = fields.get("tail").unwrap();
                        match tail.as_ref() {
                            Value::LinkedList(rest) => assert_eq!(rest.len(), 2),
                            _ => panic!("expected list tail"),
                        }
                    }
                    _ => panic!("expected Record"),
                }
            }
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn list_pop_empty() {
        let v = extract_val(builtin::list_pop(
            &Rc::new(Value::LinkedList(vec![])),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "Error"),
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn list_pop_type_error() {
        let result = builtin::list_pop(
            &Rc::new(Value::Integer(5)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn equal_false() {
        let v = extract_val(builtin::equal(
            &Rc::new(Value::Integer(1)),
            &Rc::new(Value::Integer(2)),
            (),
            empty_env(),
            empty_stack(),
        ));
        match v.as_ref() {
            Value::Tagged { label, .. } => assert_eq!(label, "False"),
            _ => panic!("expected Tagged"),
        }
    }

    // Type error on second arg for int_add/subtract/multiply/divide
    #[test]
    fn int_add_type_error_first() {
        let result = builtin::int_add(
            &Rc::new(Value::Str("x".into())),
            &Rc::new(Value::Integer(1)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn int_add_type_error_second() {
        let result = builtin::int_add(
            &Rc::new(Value::Integer(1)),
            &Rc::new(Value::Str("x".into())),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn int_subtract_type_error() {
        let result = builtin::int_subtract(
            &Rc::new(Value::Str("x".into())),
            &Rc::new(Value::Integer(1)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn int_multiply_type_error() {
        let result = builtin::int_multiply(
            &Rc::new(Value::Str("x".into())),
            &Rc::new(Value::Integer(1)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn int_divide_type_error() {
        let result = builtin::int_divide(
            &Rc::new(Value::Str("x".into())),
            &Rc::new(Value::Integer(1)),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn string_append_type_error() {
        let result = builtin::string_append(
            &Rc::new(Value::Integer(5)),
            &Rc::new(Value::Str("x".into())),
            (),
            empty_env(),
            empty_stack(),
        );
        assert!(result.is_err());
    }
}

// ============================================================================
// AST tests
// ============================================================================
mod ast_tests {
    use super::*;

    #[test]
    fn node_helper() {
        let n = ast::node(Expr::Integer { value: 42 });
        assert_eq!(n, Node(Expr::Integer { value: 42 }, ()));
    }

    #[test]
    fn node_serialize_roundtrip_integer() {
        let n = Node(Expr::Integer { value: 42 }, ());
        let json = serde_json::to_string(&n).unwrap();
        let deserialized: Node = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, n);
    }

    #[test]
    fn node_serialize_variable() {
        let n = Node(Expr::Variable { label: "x".into() }, ());
        let json = serde_json::to_string(&n).unwrap();
        assert!(json.contains("\"0\":\"v\""));
        assert!(json.contains("\"l\":\"x\""));
    }

    #[test]
    fn node_serialize_string() {
        let n = Node(Expr::String { value: "hello".into() }, ());
        let json = serde_json::to_string(&n).unwrap();
        let deserialized: Node = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, n);
    }

    #[test]
    fn node_serialize_lambda() {
        let body = Box::new(Node(Expr::Variable { label: "x".into() }, ()));
        let n = Node(
            Expr::Lambda {
                label: "x".into(),
                body,
            },
            (),
        );
        let json = serde_json::to_string(&n).unwrap();
        let deserialized: Node = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, n);
    }

    #[test]
    fn node_serialize_tail() {
        let n = Node(Expr::Tail, ());
        let json = serde_json::to_string(&n).unwrap();
        let deserialized: Node = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, n);
    }

    #[test]
    fn node_serialize_binary() {
        let n = Node(Expr::Binary { value: vec![1, 2, 3] }, ());
        let json = serde_json::to_string(&n).unwrap();
        let deserialized: Node = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, n);
    }

    #[test]
    fn node_serialize_reference() {
        let n = Node(
            Expr::Reference {
                identifier: "bafytest".into(),
            },
            (),
        );
        let json = serde_json::to_string(&n).unwrap();
        assert!(json.contains("bafytest"));
        let deserialized: Node = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, n);
    }

    #[test]
    fn node_serialize_release() {
        let n = Node(
            Expr::Release {
                package: "mypkg".into(),
                release: 1,
                identifier: "bafyrelease".into(),
            },
            (),
        );
        let json = serde_json::to_string(&n).unwrap();
        let deserialized: Node = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, n);
    }
}

// ============================================================================
// dag_json serialization tests
// ============================================================================
mod dag_json_tests {
    use super::*;

    #[test]
    fn serialize_deserialize_binary() {
        let n = Node(Expr::Binary { value: vec![0, 127, 255] }, ());
        let json = serde_json::to_value(&n).unwrap();
        let deserialized: Node = serde_json::from_value(json).unwrap();
        match &deserialized.0 {
            Expr::Binary { value } => assert_eq!(value, &vec![0, 127, 255]),
            _ => panic!("expected Binary"),
        }
    }

    #[test]
    fn serialize_deserialize_cid() {
        let n = Node(
            Expr::Reference {
                identifier: "bafyreib4e2q".into(),
            },
            (),
        );
        let json = serde_json::to_value(&n).unwrap();
        let deserialized: Node = serde_json::from_value(json).unwrap();
        match &deserialized.0 {
            Expr::Reference { identifier } => assert_eq!(identifier, "bafyreib4e2q"),
            _ => panic!("expected Reference"),
        }
    }

    #[test]
    fn serialize_deserialize_empty_binary() {
        let n = Node(Expr::Binary { value: vec![] }, ());
        let json = serde_json::to_value(&n).unwrap();
        let deserialized: Node = serde_json::from_value(json).unwrap();
        match &deserialized.0 {
            Expr::Binary { value } => assert!(value.is_empty()),
            _ => panic!("expected Binary"),
        }
    }
}

// ============================================================================
// expression::call tests
// ============================================================================
mod expression_tests {
    use super::*;

    #[test]
    fn call_tag_function() {
        let f = Rc::new(Value::Partial(Switch::Tag("Ok".into()), vec![]));
        let args = vec![(Rc::new(Value::Integer(42)), ())];
        let result = expression::call(f, args);
        assert!(result.is_ok());
        let val = result.unwrap();
        match val.as_ref() {
            Value::Tagged { label, value } => {
                assert_eq!(label, "Ok");
                assert!(matches!(value.as_ref(), Value::Integer(42)));
            }
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    fn call_select_function() {
        let f = Rc::new(Value::Partial(Switch::Select("x".into()), vec![]));
        let mut fields = im::HashMap::new();
        fields.insert("x".to_string(), Rc::new(Value::Integer(10)));
        let args = vec![(Rc::new(Value::Record(fields)), ())];
        let result = expression::call(f, args);
        assert!(result.is_ok());
        let val = result.unwrap();
        assert!(matches!(val.as_ref(), Value::Integer(10)));
    }

    #[test]
    fn call_not_a_function() {
        let f = Rc::new(Value::Integer(42));
        let args = vec![(Rc::new(Value::Integer(1)), ())];
        let result = expression::call(f, args);
        assert!(result.is_err());
    }
}

// ============================================================================
// state tests (Env, Builtin Debug, edge cases)
// ============================================================================
mod state_tests {
    use super::*;

    #[test]
    fn env_empty() {
        let env = Env::empty();
        assert!(env.scope.is_empty());
        assert!(env.references.is_empty());
        assert!(env.builtins.is_empty());
    }

    #[test]
    fn env_extend_and_lookup() {
        let env = Env::empty();
        let env2 = env.extend("x".to_string(), Rc::new(Value::Integer(42)));
        assert!(matches!(
            env2.lookup("x").unwrap().as_ref(),
            Value::Integer(42)
        ));
        assert!(env2.lookup("y").is_none());
    }

    #[test]
    fn env_extend_shadows() {
        let env = Env::empty();
        let env2 = env.extend("x".to_string(), Rc::new(Value::Integer(1)));
        let env3 = env2.extend("x".to_string(), Rc::new(Value::Integer(2)));
        assert!(matches!(
            env3.lookup("x").unwrap().as_ref(),
            Value::Integer(2)
        ));
    }

    #[test]
    fn builtin_debug_display() {
        fn dummy1(_: &Rc<Value>, _: (), _: Env, _: Stack) -> rust_interpreter::interpreter::state::StepReturn {
            unimplemented!()
        }
        fn dummy2(_: &Rc<Value>, _: &Rc<Value>, _: (), _: Env, _: Stack) -> rust_interpreter::interpreter::state::StepReturn {
            unimplemented!()
        }
        fn dummy3(_: &Rc<Value>, _: &Rc<Value>, _: &Rc<Value>, _: (), _: Env, _: Stack) -> rust_interpreter::interpreter::state::StepReturn {
            unimplemented!()
        }
        fn dummy4(_: &Rc<Value>, _: &Rc<Value>, _: &Rc<Value>, _: &Rc<Value>, _: (), _: Env, _: Stack) -> rust_interpreter::interpreter::state::StepReturn {
            unimplemented!()
        }

        assert_eq!(format!("{:?}", Builtin::Arity1(dummy1)), "Builtin::Arity1(...)");
        assert_eq!(format!("{:?}", Builtin::Arity2(dummy2)), "Builtin::Arity2(...)");
        assert_eq!(format!("{:?}", Builtin::Arity3(dummy3)), "Builtin::Arity3(...)");
        assert_eq!(format!("{:?}", Builtin::Arity4(dummy4)), "Builtin::Arity4(...)");
    }
}

// ============================================================================
// Interpreter integration tests (eval paths through state.rs)
// ============================================================================
mod eval_integration {
    use super::*;

    fn run_expr(expr: Expr) -> Result<Rc<Value>, Box<(BreakReason, (), Env, Stack)>> {
        expression::execute(Node(expr, ()), im::Vector::new())
    }

    #[test]
    fn eval_integer() {
        let v = run_expr(Expr::Integer { value: 42 }).unwrap();
        assert!(matches!(v.as_ref(), Value::Integer(42)));
    }

    #[test]
    fn eval_string() {
        let v = run_expr(Expr::String { value: "hi".into() }).unwrap();
        assert!(matches!(v.as_ref(), Value::Str(s) if s == "hi"));
    }

    #[test]
    fn eval_binary() {
        let v = run_expr(Expr::Binary { value: vec![1, 2] }).unwrap();
        assert!(matches!(v.as_ref(), Value::Binary(b) if b == &vec![1, 2]));
    }

    #[test]
    fn eval_tail() {
        let v = run_expr(Expr::Tail).unwrap();
        assert!(matches!(v.as_ref(), Value::LinkedList(items) if items.is_empty()));
    }

    #[test]
    fn eval_empty() {
        let v = run_expr(Expr::Empty).unwrap();
        assert!(matches!(v.as_ref(), Value::Record(fields) if fields.is_empty()));
    }

    #[test]
    fn eval_cons() {
        let v = run_expr(Expr::Cons).unwrap();
        assert!(matches!(v.as_ref(), Value::Partial(Switch::Cons, args) if args.is_empty()));
    }

    #[test]
    fn eval_vacant() {
        let result = run_expr(Expr::Vacant);
        assert!(result.is_err());
        let debug = result.unwrap_err();
        assert!(matches!(debug.0, BreakReason::Vacant));
    }

    #[test]
    fn eval_undefined_variable() {
        let result = run_expr(Expr::Variable { label: "x".into() });
        assert!(result.is_err());
        let debug = result.unwrap_err();
        assert!(matches!(&debug.0, BreakReason::UndefinedVariable(v) if v == "x"));
    }

    #[test]
    fn eval_undefined_builtin() {
        let result = run_expr(Expr::Builtin { identifier: "nonexistent".into() });
        assert!(result.is_err());
        let debug = result.unwrap_err();
        assert!(matches!(&debug.0, BreakReason::UndefinedBuiltin(v) if v == "nonexistent"));
    }

    #[test]
    fn eval_undefined_reference() {
        let result = run_expr(Expr::Reference { identifier: "bafyxxx".into() });
        assert!(result.is_err());
        let debug = result.unwrap_err();
        assert!(matches!(&debug.0, BreakReason::UndefinedReference(v) if v == "bafyxxx"));
    }

    #[test]
    fn eval_undefined_release() {
        let result = run_expr(Expr::Release {
            package: "pkg".into(),
            release: 1,
            identifier: "cid".into(),
        });
        assert!(result.is_err());
        let debug = result.unwrap_err();
        assert!(matches!(
            &debug.0,
            BreakReason::UndefinedRelease { package, release, cid }
            if package == "pkg" && *release == 1 && cid == "cid"
        ));
    }

    #[test]
    fn eval_select() {
        let v = run_expr(Expr::Select { label: "x".into() }).unwrap();
        assert!(matches!(v.as_ref(), Value::Partial(Switch::Select(_), _)));
    }

    #[test]
    fn eval_tag() {
        let v = run_expr(Expr::Tag { label: "Ok".into() }).unwrap();
        assert!(matches!(v.as_ref(), Value::Partial(Switch::Tag(_), _)));
    }

    #[test]
    fn eval_perform() {
        let v = run_expr(Expr::Perform { label: "Log".into() }).unwrap();
        assert!(matches!(v.as_ref(), Value::Partial(Switch::Perform(_), _)));
    }

    #[test]
    fn eval_extend() {
        let v = run_expr(Expr::Extend { label: "x".into() }).unwrap();
        assert!(matches!(v.as_ref(), Value::Partial(Switch::Extend(_), _)));
    }

    #[test]
    fn eval_overwrite() {
        let v = run_expr(Expr::Overwrite { label: "x".into() }).unwrap();
        assert!(matches!(v.as_ref(), Value::Partial(Switch::Overwrite(_), _)));
    }

    #[test]
    fn eval_case() {
        let v = run_expr(Expr::Case { label: "Ok".into() }).unwrap();
        assert!(matches!(v.as_ref(), Value::Partial(Switch::Match(_), _)));
    }

    #[test]
    fn eval_no_cases() {
        let v = run_expr(Expr::NoCases).unwrap();
        assert!(matches!(v.as_ref(), Value::Partial(Switch::NoCases, _)));
    }

    #[test]
    fn eval_handle() {
        let v = run_expr(Expr::Handle { label: "Log".into() }).unwrap();
        assert!(matches!(v.as_ref(), Value::Partial(Switch::Handle(_), _)));
    }

    #[test]
    fn eval_lambda_and_apply() {
        // (\x -> x) 42
        let id_fn = Expr::Lambda {
            label: "x".into(),
            body: Box::new(Node(Expr::Variable { label: "x".into() }, ())),
        };
        let apply = Expr::Apply {
            func: Box::new(Node(id_fn, ())),
            argument: Box::new(Node(Expr::Integer { value: 42 }, ())),
        };
        let v = run_expr(apply).unwrap();
        assert!(matches!(v.as_ref(), Value::Integer(42)));
    }

    #[test]
    fn eval_let_binding() {
        // let x = 10 in x
        let letexpr = Expr::Let {
            label: "x".into(),
            definition: Box::new(Node(Expr::Integer { value: 10 }, ())),
            body: Box::new(Node(Expr::Variable { label: "x".into() }, ())),
        };
        let v = run_expr(letexpr).unwrap();
        assert!(matches!(v.as_ref(), Value::Integer(10)));
    }

    #[test]
    fn eval_apply_not_a_function() {
        // 42 applied to 1
        let apply = Expr::Apply {
            func: Box::new(Node(Expr::Integer { value: 42 }, ())),
            argument: Box::new(Node(Expr::Integer { value: 1 }, ())),
        };
        let result = run_expr(apply);
        assert!(result.is_err());
        let debug = result.unwrap_err();
        assert!(matches!(debug.0, BreakReason::NotAFunction(_)));
    }

    #[test]
    fn eval_no_cases_applied() {
        // NoCases applied to a tagged value -> NoMatch
        let apply = Expr::Apply {
            func: Box::new(Node(Expr::NoCases, ())),
            argument: Box::new(Node(
                Expr::Apply {
                    func: Box::new(Node(Expr::Tag { label: "X".into() }, ())),
                    argument: Box::new(Node(Expr::Integer { value: 1 }, ())),
                },
                (),
            )),
        };
        let result = run_expr(apply);
        assert!(result.is_err());
        let debug = result.unwrap_err();
        assert!(matches!(debug.0, BreakReason::NoMatch(_)));
    }

    #[test]
    fn eval_select_missing_field() {
        // .missing applied to {}
        let apply = Expr::Apply {
            func: Box::new(Node(Expr::Select { label: "missing".into() }, ())),
            argument: Box::new(Node(Expr::Empty, ())),
        };
        let result = run_expr(apply);
        assert!(result.is_err());
        let debug = result.unwrap_err();
        assert!(matches!(&debug.0, BreakReason::MissingField(f) if f == "missing"));
    }

    #[test]
    fn eval_overwrite_missing_field() {
        // (:=missing) applied to a value then to {}
        // overwrite takes value then record
        let ow = Expr::Overwrite { label: "missing".into() };
        // (:=missing "val") {}
        let partial_apply = Expr::Apply {
            func: Box::new(Node(ow, ())),
            argument: Box::new(Node(Expr::String { value: "val".into() }, ())),
        };
        let apply = Expr::Apply {
            func: Box::new(Node(partial_apply, ())),
            argument: Box::new(Node(Expr::Empty, ())),
        };
        let result = run_expr(apply);
        assert!(result.is_err());
        let debug = result.unwrap_err();
        assert!(matches!(&debug.0, BreakReason::MissingField(f) if f == "missing"));
    }

    #[test]
    fn eval_perform_unhandled() {
        // (perform "Log") "hello"
        let apply = Expr::Apply {
            func: Box::new(Node(Expr::Perform { label: "Log".into() }, ())),
            argument: Box::new(Node(Expr::String { value: "hello".into() }, ())),
        };
        let result = run_expr(apply);
        assert!(result.is_err());
        let debug = result.unwrap_err();
        assert!(matches!(&debug.0, BreakReason::UnhandledEffect(l, _) if l == "Log"));
    }

    #[test]
    fn eval_cons_builds_list() {
        // cons 1 []
        let cons_1 = Expr::Apply {
            func: Box::new(Node(Expr::Cons, ())),
            argument: Box::new(Node(Expr::Integer { value: 1 }, ())),
        };
        let apply = Expr::Apply {
            func: Box::new(Node(cons_1, ())),
            argument: Box::new(Node(Expr::Tail, ())),
        };
        let v = run_expr(apply).unwrap();
        match v.as_ref() {
            Value::LinkedList(items) => {
                assert_eq!(items.len(), 1);
                assert!(matches!(items[0].as_ref(), Value::Integer(1)));
            }
            _ => panic!("expected LinkedList"),
        }
    }

    #[test]
    fn eval_extend_builds_record() {
        // (+x) 42 {}
        let ext = Expr::Extend { label: "x".into() };
        let partial = Expr::Apply {
            func: Box::new(Node(ext, ())),
            argument: Box::new(Node(Expr::Integer { value: 42 }, ())),
        };
        let apply = Expr::Apply {
            func: Box::new(Node(partial, ())),
            argument: Box::new(Node(Expr::Empty, ())),
        };
        let v = run_expr(apply).unwrap();
        match v.as_ref() {
            Value::Record(fields) => {
                let x = fields.get("x").unwrap();
                assert!(matches!(x.as_ref(), Value::Integer(42)));
            }
            _ => panic!("expected Record"),
        }
    }

    #[test]
    fn eval_overwrite_existing_field() {
        // Build {x: 1}, then overwrite x with 2
        let build_record = Expr::Apply {
            func: Box::new(Node(
                Expr::Apply {
                    func: Box::new(Node(Expr::Extend { label: "x".into() }, ())),
                    argument: Box::new(Node(Expr::Integer { value: 1 }, ())),
                },
                (),
            )),
            argument: Box::new(Node(Expr::Empty, ())),
        };
        let ow_partial = Expr::Apply {
            func: Box::new(Node(Expr::Overwrite { label: "x".into() }, ())),
            argument: Box::new(Node(Expr::Integer { value: 2 }, ())),
        };
        let apply = Expr::Apply {
            func: Box::new(Node(ow_partial, ())),
            argument: Box::new(Node(build_record, ())),
        };
        let v = run_expr(apply).unwrap();
        match v.as_ref() {
            Value::Record(fields) => {
                let x = fields.get("x").unwrap();
                assert!(matches!(x.as_ref(), Value::Integer(2)));
            }
            _ => panic!("expected Record"),
        }
    }

    #[test]
    fn eval_match_correct_branch() {
        // case "Ok" (\v -> v) (\_ -> 0) applied to Ok(42)
        let id_fn = Expr::Lambda {
            label: "v".into(),
            body: Box::new(Node(Expr::Variable { label: "v".into() }, ())),
        };
        let otherwise = Expr::Lambda {
            label: "_".into(),
            body: Box::new(Node(Expr::Integer { value: 0 }, ())),
        };
        let case_partial1 = Expr::Apply {
            func: Box::new(Node(Expr::Case { label: "Ok".into() }, ())),
            argument: Box::new(Node(id_fn, ())),
        };
        let case_partial2 = Expr::Apply {
            func: Box::new(Node(case_partial1, ())),
            argument: Box::new(Node(otherwise, ())),
        };
        let tagged = Expr::Apply {
            func: Box::new(Node(Expr::Tag { label: "Ok".into() }, ())),
            argument: Box::new(Node(Expr::Integer { value: 42 }, ())),
        };
        let apply = Expr::Apply {
            func: Box::new(Node(case_partial2, ())),
            argument: Box::new(Node(tagged, ())),
        };
        let v = run_expr(apply).unwrap();
        assert!(matches!(v.as_ref(), Value::Integer(42)));
    }

    #[test]
    fn eval_match_otherwise_branch() {
        // case "Ok" (\v -> v) (\_ -> 0) applied to Err(99)
        let id_fn = Expr::Lambda {
            label: "v".into(),
            body: Box::new(Node(Expr::Variable { label: "v".into() }, ())),
        };
        let otherwise = Expr::Lambda {
            label: "_".into(),
            body: Box::new(Node(Expr::Integer { value: 0 }, ())),
        };
        let case_partial1 = Expr::Apply {
            func: Box::new(Node(Expr::Case { label: "Ok".into() }, ())),
            argument: Box::new(Node(id_fn, ())),
        };
        let case_partial2 = Expr::Apply {
            func: Box::new(Node(case_partial1, ())),
            argument: Box::new(Node(otherwise, ())),
        };
        let tagged = Expr::Apply {
            func: Box::new(Node(Expr::Tag { label: "Err".into() }, ())),
            argument: Box::new(Node(Expr::Integer { value: 99 }, ())),
        };
        let apply = Expr::Apply {
            func: Box::new(Node(case_partial2, ())),
            argument: Box::new(Node(tagged, ())),
        };
        let v = run_expr(apply).unwrap();
        assert!(matches!(v.as_ref(), Value::Integer(0)));
    }

    #[test]
    fn eval_builtin_via_expression() {
        // int_add 3 4
        let add_3 = Expr::Apply {
            func: Box::new(Node(Expr::Builtin { identifier: "int_add".into() }, ())),
            argument: Box::new(Node(Expr::Integer { value: 3 }, ())),
        };
        let apply = Expr::Apply {
            func: Box::new(Node(add_3, ())),
            argument: Box::new(Node(Expr::Integer { value: 4 }, ())),
        };
        let v = run_expr(apply).unwrap();
        assert!(matches!(v.as_ref(), Value::Integer(7)));
    }

    #[test]
    fn eval_select_field() {
        // .x applied to {x: 10}
        let build_record = Expr::Apply {
            func: Box::new(Node(
                Expr::Apply {
                    func: Box::new(Node(Expr::Extend { label: "x".into() }, ())),
                    argument: Box::new(Node(Expr::Integer { value: 10 }, ())),
                },
                (),
            )),
            argument: Box::new(Node(Expr::Empty, ())),
        };
        let apply = Expr::Apply {
            func: Box::new(Node(Expr::Select { label: "x".into() }, ())),
            argument: Box::new(Node(build_record, ())),
        };
        let v = run_expr(apply).unwrap();
        assert!(matches!(v.as_ref(), Value::Integer(10)));
    }
}

// ============================================================================
// value_json tests (edge cases)
// ============================================================================
mod value_json_tests {
    use super::*;

    #[test]
    fn deserialize_binary_value() {
        use base64::Engine;
        let encoded = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(&[1, 2, 3]);
        let json: serde_json::Value = serde_json::json!({
            "binary": {"/": {"bytes": encoded}}
        });
        let v = value_json::deserialize_value(&json);
        assert!(matches!(v, Value::Binary(b) if b == vec![1, 2, 3]));
    }

    #[test]
    fn deserialize_list_value() {
        let json: serde_json::Value = serde_json::json!({
            "list": [{"integer": 1}, {"integer": 2}]
        });
        let v = value_json::deserialize_value(&json);
        match v {
            Value::LinkedList(items) => assert_eq!(items.len(), 2),
            _ => panic!("expected LinkedList"),
        }
    }

    #[test]
    fn deserialize_record_value() {
        let json: serde_json::Value = serde_json::json!({
            "record": {"x": {"integer": 1}, "y": {"string": "hi"}}
        });
        let v = value_json::deserialize_value(&json);
        match v {
            Value::Record(fields) => {
                assert_eq!(fields.len(), 2);
                assert!(matches!(fields.get("x").unwrap().as_ref(), Value::Integer(1)));
                assert!(matches!(fields.get("y").unwrap().as_ref(), Value::Str(s) if s == "hi"));
            }
            _ => panic!("expected Record"),
        }
    }

    #[test]
    fn deserialize_tagged_value() {
        let json: serde_json::Value = serde_json::json!({
            "tagged": {"label": "Ok", "value": {"integer": 42}}
        });
        let v = value_json::deserialize_value(&json);
        match v {
            Value::Tagged { label, value } => {
                assert_eq!(label, "Ok");
                assert!(matches!(value.as_ref(), Value::Integer(42)));
            }
            _ => panic!("expected Tagged"),
        }
    }

    #[test]
    #[should_panic(expected = "Unknown value type")]
    fn deserialize_unknown_value() {
        let json: serde_json::Value = serde_json::json!({"unknown": true});
        value_json::deserialize_value(&json);
    }
}
