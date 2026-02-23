use crate::binding::{self, Binding, Bindings};
use crate::error::Reason;
use crate::types::{Mono, Type};

pub fn unify(t1: &Mono, t2: &Mono, level: usize, bindings: &mut Bindings) -> Result<(), Reason> {
    match do_unify(vec![(t1.clone(), t2.clone())], level, bindings) {
        Err(Reason::TypeMismatch(Type::Var(_), Type::Var(_))) => Err(Reason::TypeMismatch(
            binding::resolve(t1, bindings),
            binding::resolve(t2, bindings),
        )),
        result => result,
    }
}

fn find(type_: &Mono, bindings: &Bindings) -> Option<Binding> {
    match type_ {
        Type::Var(i) => Some(bindings.get(*i).clone()),
        _ => None,
    }
}

fn do_unify(
    mut worklist: Vec<(Mono, Mono)>,
    level: usize,
    bindings: &mut Bindings,
) -> Result<(), Reason> {
    while let Some((t1, t2)) = worklist.pop() {
        match (&t1, find(&t1, bindings), &t2, find(&t2, bindings)) {
            (Type::Var(i), _, Type::Var(j), _) if i == j => continue,
            (_, Some(Binding::Bound(resolved)), _, _) => {
                worklist.push((resolved, t2));
            }
            (_, _, _, Some(Binding::Bound(resolved))) => {
                worklist.push((t1, resolved));
            }
            (Type::Var(i), Some(Binding::Unbound(var_level)), other, _)
            | (other, _, Type::Var(i), Some(Binding::Unbound(var_level))) => {
                let i = *i;
                let other = other.clone();
                occurs_and_levels(i, var_level, &[&other], bindings)?;
                bindings.bind(i, other);
            }
            (Type::Fun(arg1, eff1, ret1), _, Type::Fun(arg2, eff2, ret2), _) => {
                worklist.push((*ret1.clone(), *ret2.clone()));
                worklist.push((*eff1.clone(), *eff2.clone()));
                worklist.push((*arg1.clone(), *arg2.clone()));
            }
            (Type::Integer, _, Type::Integer, _) => continue,
            (Type::Binary, _, Type::Binary, _) => continue,
            (Type::String, _, Type::String, _) => continue,
            (Type::Empty, _, Type::Empty, _) => continue,
            (Type::List(el1), _, Type::List(el2), _) => {
                worklist.push((*el1.clone(), *el2.clone()));
            }
            (Type::Record(rows1), _, Type::Record(rows2), _) => {
                worklist.push((*rows1.clone(), *rows2.clone()));
            }
            (Type::Union(rows1), _, Type::Union(rows2), _) => {
                worklist.push((*rows1.clone(), *rows2.clone()));
            }
            (Type::RowExtend(l1, field1, rest1), _, other, _)
            | (other, _, Type::RowExtend(l1, field1, rest1), _) => {
                let l1 = l1.clone();
                let field1 = *field1.clone();
                let rest1 = *rest1.clone();
                let other = other.clone();
                let (field2, rest2) = rewrite_row(&l1, &other, level, bindings, &rest1)?;
                worklist.push((rest1, rest2));
                worklist.push((field1, field2));
            }
            (Type::EffectExtend(l1, (lift1, reply1), r1), _, other, _)
            | (other, _, Type::EffectExtend(l1, (lift1, reply1), r1), _) => {
                let l1 = l1.clone();
                let lift1 = *lift1.clone();
                let reply1 = *reply1.clone();
                let r1 = *r1.clone();
                let other = other.clone();
                let ((lift2, reply2), r2) =
                    rewrite_effect(&l1, &other, level, bindings, &r1)?;
                worklist.push((r1, r2));
                worklist.push((reply1, reply2));
                worklist.push((lift1, lift2));
            }
            (Type::Never, _, Type::Never, _) => continue,
            (Type::Promise(t1), _, Type::Promise(t2), _) => {
                worklist.push((*t1.clone(), *t2.clone()));
            }
            _ => return Err(Reason::TypeMismatch(t1, t2)),
        }
    }
    Ok(())
}

fn occurs_and_levels(
    i: usize,
    level: usize,
    types: &[&Mono],
    bindings: &mut Bindings,
) -> Result<(), Reason> {
    let mut stack: Vec<Mono> = types.iter().map(|t| (*t).clone()).collect();
    while let Some(type_) = stack.pop() {
        match &type_ {
            Type::Var(j) if *j == i => return Err(Reason::Recursive),
            Type::Var(j) => {
                let j = *j;
                match bindings.get(j).clone() {
                    Binding::Unbound(l) => {
                        let new_l = l.min(level);
                        bindings.set_unbound(j, new_l);
                    }
                    Binding::Bound(t) => stack.push(t),
                }
            }
            Type::Fun(arg, eff, ret) => {
                stack.push(*arg.clone());
                stack.push(*eff.clone());
                stack.push(*ret.clone());
            }
            Type::Integer | Type::Binary | Type::String | Type::Empty | Type::Never => {}
            Type::List(el) => stack.push(*el.clone()),
            Type::Record(row) => stack.push(*row.clone()),
            Type::Union(row) => stack.push(*row.clone()),
            Type::RowExtend(_, field, rest) => {
                stack.push(*field.clone());
                stack.push(*rest.clone());
            }
            Type::EffectExtend(_, (lift, reply), rest) => {
                stack.push(*lift.clone());
                stack.push(*reply.clone());
                stack.push(*rest.clone());
            }
            Type::Promise(inner) => stack.push(*inner.clone()),
        }
    }
    Ok(())
}

fn rewrite_row(
    required: &str,
    type_: &Mono,
    level: usize,
    bindings: &mut Bindings,
    check: &Mono,
) -> Result<(Mono, Mono), Reason> {
    match type_ {
        Type::Empty => Err(Reason::MissingRow(required.to_string())),
        Type::RowExtend(l, field, rest) if l == required => Ok((*field.clone(), *rest.clone())),
        Type::RowExtend(l, other_field, rest) => {
            let (field, new_tail) = rewrite_row(required, rest, level, bindings, check)?;
            let rest = Type::RowExtend(l.clone(), other_field.clone(), Box::new(new_tail));
            Ok((field, rest))
        }
        Type::Var(i) => {
            let i = *i;
            match bindings.get(i).clone() {
                Binding::Bound(resolved) => {
                    rewrite_row(required, &resolved, level, bindings, check)
                }
                _ => {
                    // Check for infinite loop (same tails)
                    if let Type::Var(j) = check
                        && i == *j
                    {
                        return Err(Reason::SameTail(Type::Var(i), Type::Var(*j)));
                    }
                    let field = bindings.fresh_mono(level);
                    let rest = bindings.fresh_mono(level);
                    let bound = Type::RowExtend(
                        required.to_string(),
                        Box::new(field.clone()),
                        Box::new(rest.clone()),
                    );
                    bindings.bind(i, bound);
                    Ok((field, rest))
                }
            }
        }
        _ => panic!("bad row"),
    }
}

fn rewrite_effect(
    required: &str,
    type_: &Mono,
    level: usize,
    bindings: &mut Bindings,
    check: &Mono,
) -> Result<((Mono, Mono), Mono), Reason> {
    match type_ {
        Type::Empty => Err(Reason::MissingRow(required.to_string())),
        Type::EffectExtend(l, (lift, reply), rest) if l == required => {
            Ok(((*lift.clone(), *reply.clone()), *rest.clone()))
        }
        Type::EffectExtend(l, other_eff, rest) => {
            let ((lift, reply), new_tail) =
                rewrite_effect(required, rest, level, bindings, check)?;
            let rest = Type::EffectExtend(l.clone(), other_eff.clone(), Box::new(new_tail));
            Ok(((lift, reply), rest))
        }
        Type::Var(i) => {
            let i = *i;
            match bindings.get(i).clone() {
                Binding::Bound(resolved) => {
                    rewrite_effect(required, &resolved, level, bindings, check)
                }
                _ => {
                    // Check for infinite loop (same tails)
                    if let Type::Var(j) = check
                        && i == *j
                    {
                        return Err(Reason::TypeMismatch(Type::Var(i), Type::Var(*j)));
                    }
                    let lift = bindings.fresh_mono(level);
                    let reply = bindings.fresh_mono(level);

                    // Re-check binding after fresh_mono calls (might get bound during tail rewrite)
                    match bindings.get(i).clone() {
                        Binding::Unbound(var_level) => {
                            let rest = bindings.fresh_mono(var_level);
                            let bound = Type::EffectExtend(
                                required.to_string(),
                                (Box::new(lift.clone()), Box::new(reply.clone())),
                                Box::new(rest.clone()),
                            );
                            bindings.bind(i, bound);
                            Ok(((lift, reply), rest))
                        }
                        Binding::Bound(resolved) => {
                            rewrite_effect(required, &resolved, level, bindings, check)
                        }
                    }
                }
            }
        }
        _ => panic!("bad effect"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_same_type() {
        let mut b = Bindings::new();
        assert!(unify(&Type::Integer, &Type::Integer, 1, &mut b).is_ok());
        assert!(unify(&Type::String, &Type::String, 1, &mut b).is_ok());
        assert!(unify(&Type::Binary, &Type::Binary, 1, &mut b).is_ok());
        assert!(unify(&Type::Empty, &Type::Empty, 1, &mut b).is_ok());
        assert!(unify(&Type::Never, &Type::Never, 1, &mut b).is_ok());
    }

    #[test]
    fn test_unify_mismatch() {
        let mut b = Bindings::new();
        let result = unify(&Type::Integer, &Type::String, 1, &mut b);
        assert!(matches!(result, Err(Reason::TypeMismatch(_, _))));
    }

    #[test]
    fn test_unify_var_with_type() {
        let mut b = Bindings::new();
        let v = b.fresh_mono(1);
        assert!(unify(&v, &Type::Integer, 1, &mut b).is_ok());
        assert_eq!(binding::resolve(&v, &b), Type::Integer);
    }

    #[test]
    fn test_unify_type_with_var() {
        let mut b = Bindings::new();
        let v = b.fresh_mono(1);
        assert!(unify(&Type::String, &v, 1, &mut b).is_ok());
        assert_eq!(binding::resolve(&v, &b), Type::String);
    }

    #[test]
    fn test_unify_same_var() {
        let mut b = Bindings::new();
        let v = b.fresh_mono(1);
        assert!(unify(&v, &v, 1, &mut b).is_ok());
    }

    #[test]
    fn test_unify_fun() {
        let mut b = Bindings::new();
        let f1 = Type::Fun(
            Box::new(Type::Integer),
            Box::new(Type::Empty),
            Box::new(Type::String),
        );
        let f2 = Type::Fun(
            Box::new(Type::Integer),
            Box::new(Type::Empty),
            Box::new(Type::String),
        );
        assert!(unify(&f1, &f2, 1, &mut b).is_ok());
    }

    #[test]
    fn test_unify_fun_mismatch() {
        let mut b = Bindings::new();
        let f1 = Type::Fun(
            Box::new(Type::Integer),
            Box::new(Type::Empty),
            Box::new(Type::String),
        );
        let f2 = Type::Fun(
            Box::new(Type::String),
            Box::new(Type::Empty),
            Box::new(Type::String),
        );
        assert!(unify(&f1, &f2, 1, &mut b).is_err());
    }

    #[test]
    fn test_unify_list() {
        let mut b = Bindings::new();
        let l1 = Type::List(Box::new(Type::Integer));
        let l2 = Type::List(Box::new(Type::Integer));
        assert!(unify(&l1, &l2, 1, &mut b).is_ok());
    }

    #[test]
    fn test_unify_record_rows() {
        let mut b = Bindings::new();
        let r1 = Type::Record(Box::new(Type::RowExtend(
            "x".into(),
            Box::new(Type::Integer),
            Box::new(Type::Empty),
        )));
        let r2 = Type::Record(Box::new(Type::RowExtend(
            "x".into(),
            Box::new(Type::Integer),
            Box::new(Type::Empty),
        )));
        assert!(unify(&r1, &r2, 1, &mut b).is_ok());
    }

    #[test]
    fn test_unify_row_rewrite() {
        let mut b = Bindings::new();
        // {x: Int, y: String} vs {y: String, x: Int} — should unify via row rewriting
        let r1 = Type::Record(Box::new(Type::RowExtend(
            "x".into(),
            Box::new(Type::Integer),
            Box::new(Type::RowExtend(
                "y".into(),
                Box::new(Type::String),
                Box::new(Type::Empty),
            )),
        )));
        let r2 = Type::Record(Box::new(Type::RowExtend(
            "y".into(),
            Box::new(Type::String),
            Box::new(Type::RowExtend(
                "x".into(),
                Box::new(Type::Integer),
                Box::new(Type::Empty),
            )),
        )));
        assert!(unify(&r1, &r2, 1, &mut b).is_ok());
    }

    #[test]
    fn test_unify_missing_row() {
        let mut b = Bindings::new();
        let r1 = Type::RowExtend("x".into(), Box::new(Type::Integer), Box::new(Type::Empty));
        let r2 = Type::RowExtend("y".into(), Box::new(Type::Integer), Box::new(Type::Empty));
        let result = unify(&r1, &r2, 1, &mut b);
        assert!(matches!(result, Err(Reason::MissingRow(_))));
    }

    #[test]
    fn test_occurs_check() {
        let mut b = Bindings::new();
        let v = b.fresh_mono(1); // Var(0)
        let recursive = Type::List(Box::new(v.clone()));
        let result = unify(&v, &recursive, 1, &mut b);
        assert!(matches!(result, Err(Reason::Recursive)));
    }

    // Port of Gleam test: binding_types_in_tail_position_get_resolved_test
    #[test]
    fn test_binding_types_in_tail_position_resolved() {
        let mut b = Bindings::new();
        // Set up bindings manually: 0=Bound(Int), 1=Bound(Empty),
        // 2=Bound(Record(RowExtend("foo", Var(0), Var(1)))), 3=Unbound(1), 4=Unbound(1)
        b.fresh_mono(0); // id 0
        b.fresh_mono(0); // id 1
        b.fresh_mono(0); // id 2
        b.fresh_mono(1); // id 3
        b.fresh_mono(1); // id 4
        b.bind(0, Type::Integer);
        b.bind(1, Type::Empty);
        b.bind(
            2,
            Type::Record(Box::new(Type::RowExtend(
                "foo".into(),
                Box::new(Type::Var(0)),
                Box::new(Type::Var(1)),
            ))),
        );

        let have = Type::Var(2);
        let want = Type::Record(Box::new(Type::RowExtend(
            "init".into(),
            Box::new(Type::Var(4)),
            Box::new(Type::Var(3)),
        )));
        let result = unify(&want, &have, 1, &mut b);
        assert_eq!(result, Err(Reason::MissingRow("init".into())));
    }

    // Port of Gleam test: rows_with_the_same_common_tail_dont_unify_test
    #[test]
    fn test_rows_same_tail_dont_unify() {
        let mut b = Bindings::new();
        let root = b.fresh_mono(1); // Var(0)
        let r1 = Type::RowExtend("A".into(), Box::new(Type::Integer), Box::new(root.clone()));
        let r2 = Type::RowExtend("B".into(), Box::new(Type::String), Box::new(root));
        assert!(unify(&r1, &r2, 1, &mut b).is_err());
    }

    // Port of Gleam test: effects_with_the_same_common_tail_dont_unify_test
    #[test]
    fn test_effects_same_tail_dont_unify() {
        let mut b = Bindings::new();
        let root = b.fresh_mono(1); // Var(0)
        let e1 = Type::EffectExtend(
            "A".into(),
            (Box::new(Type::Integer), Box::new(Type::unit())),
            Box::new(root.clone()),
        );
        let e2 = Type::EffectExtend(
            "B".into(),
            (Box::new(Type::String), Box::new(Type::unit())),
            Box::new(root),
        );
        assert!(unify(&e1, &e2, 1, &mut b).is_err());
    }

    #[test]
    fn test_unify_open_record_with_var_tail() {
        let mut b = Bindings::new();
        let tail = b.fresh_mono(1); // Var(0)
        let r1 = Type::Record(Box::new(Type::RowExtend(
            "x".into(),
            Box::new(Type::Integer),
            Box::new(tail),
        )));
        let r2 = Type::Record(Box::new(Type::RowExtend(
            "x".into(),
            Box::new(Type::Integer),
            Box::new(Type::RowExtend(
                "y".into(),
                Box::new(Type::String),
                Box::new(Type::Empty),
            )),
        )));
        assert!(unify(&r1, &r2, 1, &mut b).is_ok());
    }

    #[test]
    fn test_unify_promise() {
        let mut b = Bindings::new();
        let p1 = Type::Promise(Box::new(Type::Integer));
        let p2 = Type::Promise(Box::new(Type::Integer));
        assert!(unify(&p1, &p2, 1, &mut b).is_ok());

        let p3 = Type::Promise(Box::new(Type::String));
        assert!(unify(&p1, &p3, 1, &mut b).is_err());
    }
}
