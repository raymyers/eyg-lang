use crate::infer::{q};
use crate::types::{Poly, Type};

fn pure1(arg: Poly, ret: Poly) -> Poly {
    Type::Fun(Box::new(arg), Box::new(Type::Empty), Box::new(ret))
}

fn pure2(arg1: Poly, arg2: Poly, ret: Poly) -> Poly {
    Type::Fun(
        Box::new(arg1),
        Box::new(Type::Empty),
        Box::new(pure1(arg2, ret)),
    )
}

fn pure3(arg1: Poly, arg2: Poly, arg3: Poly, ret: Poly) -> Poly {
    Type::Fun(
        Box::new(arg1),
        Box::new(Type::Empty),
        Box::new(pure2(arg2, arg3, ret)),
    )
}

pub fn lookup(name: &str) -> Option<Poly> {
    let result = match name {
        "equal" => pure2(q(0), q(0), Type::boolean()),
        "fix" => Type::Fun(
            Box::new(Type::Fun(Box::new(q(0)), Box::new(q(1)), Box::new(q(0)))),
            Box::new(q(1)),
            Box::new(q(0)),
        ),
        "never" => pure1(Type::Never, q(1)),

        // Integer ops
        "int_compare" => {
            let ret = Type::union(vec![
                ("Lt".into(), Type::unit()),
                ("Eq".into(), Type::unit()),
                ("Gt".into(), Type::unit()),
            ]);
            pure2(Type::Integer, Type::Integer, ret)
        }
        "int_add" => pure2(Type::Integer, Type::Integer, Type::Integer),
        "int_subtract" => pure2(Type::Integer, Type::Integer, Type::Integer),
        "int_multiply" => pure2(Type::Integer, Type::Integer, Type::Integer),
        "int_divide" => pure2(Type::Integer, Type::Integer, Type::result(Type::Integer, Type::unit())),
        "int_absolute" => pure1(Type::Integer, Type::Integer),
        "int_parse" => pure1(Type::String, Type::result(Type::Integer, Type::unit())),
        "int_to_string" => pure1(Type::Integer, Type::String),

        // String ops
        "string_append" => pure2(Type::String, Type::String, Type::String),
        "string_split" => {
            let ret = Type::record(vec![
                ("head".into(), Type::String),
                ("tail".into(), Type::List(Box::new(Type::String))),
            ]);
            pure2(Type::String, Type::String, ret)
        }
        "string_split_once" => {
            let ret = Type::record(vec![
                ("head".into(), Type::String),
                ("tail".into(), Type::String),
            ]);
            pure2(Type::String, Type::String, Type::result(ret, Type::unit()))
        }
        "string_replace" => pure3(Type::String, Type::String, Type::String, Type::String),
        "string_uppercase" => pure1(Type::String, Type::String),
        "string_lowercase" => pure1(Type::String, Type::String),
        "string_starts_with" => pure2(Type::String, Type::String, Type::boolean()),
        "string_ends_with" => pure2(Type::String, Type::String, Type::boolean()),
        "string_length" => pure1(Type::String, Type::Integer),
        "string_to_binary" => pure1(Type::String, Type::Binary),
        "string_from_binary" => pure1(Type::Binary, Type::result(Type::String, Type::unit())),

        // Binary ops
        "binary_from_integers" => pure1(Type::List(Box::new(Type::Integer)), Type::Binary),
        "binary_fold" => {
            let acc = q(1);
            let eff = q(2);
            let reducer = Type::Fun(
                Box::new(Type::Integer),
                Box::new(eff.clone()),
                Box::new(Type::Fun(Box::new(acc.clone()), Box::new(eff.clone()), Box::new(acc.clone()))),
            );
            pure2(Type::Binary, acc, Type::Fun(Box::new(reducer), Box::new(eff), Box::new(q(1))))
        }

        // List ops
        "list_pop" => {
            let ret = Type::record(vec![
                ("head".into(), q(0)),
                ("tail".into(), Type::List(Box::new(q(0)))),
            ]);
            pure1(Type::List(Box::new(q(0))), Type::result(ret, Type::unit()))
        }
        "list_fold" => {
            let el = q(0);
            let acc = q(1);
            let eff = q(2);
            let reducer = Type::Fun(
                Box::new(el),
                Box::new(eff.clone()),
                Box::new(Type::Fun(Box::new(acc.clone()), Box::new(eff.clone()), Box::new(acc.clone()))),
            );
            pure2(
                Type::List(Box::new(q(0))),
                acc,
                Type::Fun(Box::new(reducer), Box::new(eff), Box::new(q(1))),
            )
        }

        _ => return None,
    };
    Some(result)
}
