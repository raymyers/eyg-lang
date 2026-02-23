use std::collections::HashMap;

use crate::types::{Mono, Poly, Type};

#[derive(Debug, Clone, PartialEq)]
pub enum Binding {
    Bound(Mono),
    Unbound(usize), // level
}

#[derive(Debug, Clone)]
pub struct Bindings(Vec<Binding>);

impl Bindings {
    pub fn new() -> Self {
        Bindings(Vec::new())
    }

    pub fn fresh_mono(&mut self, level: usize) -> Mono {
        let id = self.0.len();
        self.0.push(Binding::Unbound(level));
        Type::Var(id)
    }

    pub fn fresh_poly(&mut self, level: usize) -> Poly {
        let id = self.0.len();
        self.0.push(Binding::Unbound(level));
        Type::Var((false, id))
    }

    pub fn bind(&mut self, id: usize, mono: Mono) {
        self.0[id] = Binding::Bound(mono);
    }

    pub fn get(&self, id: usize) -> &Binding {
        &self.0[id]
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn set_unbound(&mut self, id: usize, level: usize) {
        self.0[id] = Binding::Unbound(level);
    }
}

impl Default for Bindings {
    fn default() -> Self {
        Self::new()
    }
}

pub fn resolve(type_: &Mono, bindings: &Bindings) -> Mono {
    match type_ {
        Type::Var(i) => match bindings.get(*i) {
            Binding::Bound(t) => resolve(t, bindings),
            Binding::Unbound(_) => type_.clone(),
        },
        Type::Fun(arg, eff, ret) => Type::Fun(
            Box::new(resolve(arg, bindings)),
            Box::new(resolve(eff, bindings)),
            Box::new(resolve(ret, bindings)),
        ),
        Type::Integer => Type::Integer,
        Type::Binary => Type::Binary,
        Type::String => Type::String,
        Type::Empty => Type::Empty,
        Type::List(el) => Type::List(Box::new(resolve(el, bindings))),
        Type::Record(rows) => Type::Record(Box::new(resolve(rows, bindings))),
        Type::Union(rows) => Type::Union(Box::new(resolve(rows, bindings))),
        Type::RowExtend(label, field, rest) => Type::RowExtend(
            label.clone(),
            Box::new(resolve(field, bindings)),
            Box::new(resolve(rest, bindings)),
        ),
        Type::EffectExtend(label, (lift, reply), rest) => Type::EffectExtend(
            label.clone(),
            (
                Box::new(resolve(lift, bindings)),
                Box::new(resolve(reply, bindings)),
            ),
            Box::new(resolve(rest, bindings)),
        ),
        Type::Never => Type::Never,
        Type::Promise(inner) => Type::Promise(Box::new(resolve(inner, bindings))),
    }
}

pub fn generalize(type_: &Mono, level: usize, bindings: &Bindings) -> Poly {
    match type_ {
        Type::Var(i) => match bindings.get(*i) {
            Binding::Unbound(l) => {
                if *l > level {
                    Type::Var((true, *i))
                } else {
                    Type::Var((false, *i))
                }
            }
            Binding::Bound(t) =>generalize(t, level, bindings),
        },
        Type::Fun(arg, eff, ret) => Type::Fun(
            Box::new(generalize(arg, level, bindings)),
            Box::new(generalize(eff, level, bindings)),
            Box::new(generalize(ret, level, bindings)),
        ),
        Type::Integer => Type::Integer,
        Type::Binary => Type::Binary,
        Type::String => Type::String,
        Type::Empty => Type::Empty,
        Type::List(el) => Type::List(Box::new(generalize(el, level, bindings))),
        Type::Record(rows) => Type::Record(Box::new(generalize(rows, level, bindings))),
        Type::Union(rows) => Type::Union(Box::new(generalize(rows, level, bindings))),
        Type::RowExtend(label, field, rest) => Type::RowExtend(
            label.clone(),
            Box::new(generalize(field, level, bindings)),
            Box::new(generalize(rest, level, bindings)),
        ),
        Type::EffectExtend(label, (lift, reply), rest) => Type::EffectExtend(
            label.clone(),
            (
                Box::new(generalize(lift, level, bindings)),
                Box::new(generalize(reply, level, bindings)),
            ),
            Box::new(generalize(rest, level, bindings)),
        ),
        Type::Never => Type::Never,
        Type::Promise(inner) => Type::Promise(Box::new(generalize(inner, level, bindings))),
    }
}

pub fn instantiate(poly: &Poly, level: usize, bindings: &mut Bindings) -> Mono {
    let mut subs: HashMap<usize, Mono> = HashMap::new();
    do_inst(poly, level, bindings, &mut subs)
}

fn do_inst(
    poly: &Poly,
    level: usize,
    bindings: &mut Bindings,
    subs: &mut HashMap<usize, Mono>,
) -> Mono {
    match poly {
        Type::Var((true, i)) => {
            if let Some(tv) = subs.get(i) {
                tv.clone()
            } else {
                let tv = bindings.fresh_mono(level);
                subs.insert(*i, tv.clone());
                tv
            }
        }
        Type::Var((false, i)) => Type::Var(*i),
        Type::Fun(arg, eff, ret) => Type::Fun(
            Box::new(do_inst(arg, level, bindings, subs)),
            Box::new(do_inst(eff, level, bindings, subs)),
            Box::new(do_inst(ret, level, bindings, subs)),
        ),
        Type::Integer => Type::Integer,
        Type::Binary => Type::Binary,
        Type::String => Type::String,
        Type::Empty => Type::Empty,
        Type::List(el) => Type::List(Box::new(do_inst(el, level, bindings, subs))),
        Type::Record(rows) => Type::Record(Box::new(do_inst(rows, level, bindings, subs))),
        Type::Union(rows) => Type::Union(Box::new(do_inst(rows, level, bindings, subs))),
        Type::RowExtend(label, field, rest) => Type::RowExtend(
            label.clone(),
            Box::new(do_inst(field, level, bindings, subs)),
            Box::new(do_inst(rest, level, bindings, subs)),
        ),
        Type::EffectExtend(label, (lift, reply), rest) => Type::EffectExtend(
            label.clone(),
            (
                Box::new(do_inst(lift, level, bindings, subs)),
                Box::new(do_inst(reply, level, bindings, subs)),
            ),
            Box::new(do_inst(rest, level, bindings, subs)),
        ),
        Type::Never => Type::Never,
        Type::Promise(inner) => Type::Promise(Box::new(do_inst(inner, level, bindings, subs))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fresh_mono_sequential_ids() {
        let mut b = Bindings::new();
        let v0 = b.fresh_mono(0);
        let v1 = b.fresh_mono(0);
        let v2 = b.fresh_mono(1);
        assert_eq!(v0, Type::Var(0));
        assert_eq!(v1, Type::Var(1));
        assert_eq!(v2, Type::Var(2));
        assert_eq!(b.len(), 3);
    }

    #[test]
    fn test_fresh_poly() {
        let mut b = Bindings::new();
        let p = b.fresh_poly(0);
        assert_eq!(p, Type::Var((false, 0)));
    }

    #[test]
    fn test_bind_and_get() {
        let mut b = Bindings::new();
        b.fresh_mono(0); // id 0
        assert!(matches!(b.get(0), Binding::Unbound(0)));
        b.bind(0, Type::Integer);
        assert_eq!(b.get(0), &Binding::Bound(Type::Integer));
    }

    #[test]
    fn test_resolve_unbound() {
        let mut b = Bindings::new();
        let v = b.fresh_mono(0);
        assert_eq!(resolve(&v, &b), Type::Var(0));
    }

    #[test]
    fn test_resolve_one_step() {
        let mut b = Bindings::new();
        b.fresh_mono(0); // id 0
        b.bind(0, Type::Integer);
        assert_eq!(resolve(&Type::Var(0), &b), Type::Integer);
    }

    #[test]
    fn test_resolve_multi_step() {
        let mut b = Bindings::new();
        b.fresh_mono(0); // id 0
        b.fresh_mono(0); // id 1
        b.bind(0, Type::Var(1));
        b.bind(1, Type::String);
        assert_eq!(resolve(&Type::Var(0), &b), Type::String);
    }

    #[test]
    fn test_resolve_compound() {
        let mut b = Bindings::new();
        b.fresh_mono(0); // id 0
        b.bind(0, Type::Integer);
        let list = Type::List(Box::new(Type::Var(0)));
        assert_eq!(resolve(&list, &b), Type::List(Box::new(Type::Integer)));
    }

    #[test]
    fn test_gen_above_level() {
        let mut b = Bindings::new();
        b.fresh_mono(2); // id 0 at level 2
        let poly =generalize(&Type::Var(0), 1, &b);
        assert_eq!(poly, Type::Var((true, 0))); // quantified: level 2 > 1
    }

    #[test]
    fn test_gen_at_level() {
        let mut b = Bindings::new();
        b.fresh_mono(1); // id 0 at level 1
        let poly =generalize(&Type::Var(0), 1, &b);
        assert_eq!(poly, Type::Var((false, 0))); // free: level 1 not > 1
    }

    #[test]
    fn test_gen_below_level() {
        let mut b = Bindings::new();
        b.fresh_mono(0); // id 0 at level 0
        let poly =generalize(&Type::Var(0), 1, &b);
        assert_eq!(poly, Type::Var((false, 0))); // free: level 0 not > 1
    }

    #[test]
    fn test_gen_bound_chases() {
        let mut b = Bindings::new();
        b.fresh_mono(0); // id 0
        b.bind(0, Type::Integer);
        let poly =generalize(&Type::Var(0), 0, &b);
        assert_eq!(poly, Type::Integer);
    }

    #[test]
    fn test_instantiate_quantified() {
        let mut b = Bindings::new();
        // Poly: forall a. a -> a (quantified var id 0)
        let poly: Poly = Type::Fun(
            Box::new(Type::Var((true, 0))),
            Box::new(Type::Empty),
            Box::new(Type::Var((true, 0))),
        );
        // Need var 0 to exist in bindings for gen to have produced this
        b.fresh_mono(2); // id 0, will be replaced

        let mono = instantiate(&poly, 1, &mut b);
        // Should get Fun(Var(1), Empty, Var(1)) — same fresh var for both occurrences
        match mono {
            Type::Fun(arg, _, ret) => {
                assert_eq!(arg, ret); // same fresh var
                assert!(matches!(*arg, Type::Var(1))); // new var id 1
            }
            _ => panic!("expected Fun"),
        }
    }

    #[test]
    fn test_instantiate_free_preserved() {
        let mut b = Bindings::new();
        b.fresh_mono(0); // id 0
        let poly: Poly = Type::Var((false, 0));
        let mono = instantiate(&poly, 1, &mut b);
        assert_eq!(mono, Type::Var(0)); // preserved as-is
    }

    #[test]
    fn test_instantiate_concrete_types() {
        let mut b = Bindings::new();
        let poly: Poly = Type::Integer;
        let mono = instantiate(&poly, 1, &mut b);
        assert_eq!(mono, Type::Integer);
    }
}
