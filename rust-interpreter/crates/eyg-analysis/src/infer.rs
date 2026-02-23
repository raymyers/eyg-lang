use std::collections::HashMap;

use eyg_ir::{Expr, Node};

use crate::binding::{self, Binding, Bindings};
use crate::error::Reason;
use crate::types::{Mono, Poly, Type};
use crate::unify;

// --- Public types ---

pub type Env = Vec<(String, Poly)>;

pub struct Context {
    pub env: Env,
    pub eff: Mono,
    pub refs: HashMap<String, Poly>,
    pub level: usize,
    pub bindings: Bindings,
}

impl Context {
    pub fn pure() -> Self {
        Context {
            env: Vec::new(),
            eff: Type::Empty,
            refs: HashMap::new(),
            level: 1,
            bindings: Bindings::new(),
        }
    }

    pub fn unpure() -> Self {
        let mut bindings = Bindings::new();
        let eff = bindings.fresh_mono(1);
        Context {
            env: Vec::new(),
            eff,
            refs: HashMap::new(),
            level: 1,
            bindings,
        }
    }

    pub fn with_refs(mut self, refs: HashMap<String, Poly>) -> Self {
        self.refs = refs;
        self
    }

    pub fn with_effect(mut self, label: &str, lift: Mono, lower: Mono) -> Self {
        self.eff = Type::EffectExtend(
            label.to_string(),
            (Box::new(lift), Box::new(lower)),
            Box::new(self.eff),
        );
        self
    }
}

#[derive(Debug, Clone)]
pub struct NodeInfo {
    pub result: Result<(), Reason>,
    pub typ: Mono,
    pub eff: Mono,
    pub scope: Env,
}

pub struct Analysis {
    pub bindings: Bindings,
    pub annotations: Vec<NodeInfo>,
}

impl Analysis {
    pub fn type_of(&self) -> Mono {
        let last = &self.annotations.first().expect("non-empty annotations");
        binding::resolve(&last.typ, &self.bindings)
    }
}

pub fn check(context: Context, source: &Node) -> Analysis {
    let Context {
        env,
        eff,
        refs,
        level,
        mut bindings,
    } = context;
    let mut annotations = Vec::new();
    do_infer(
        source,
        &env,
        &eff,
        &refs,
        level,
        &mut bindings,
        &mut annotations,
    );
    Analysis {
        bindings,
        annotations,
    }
}

// --- Helpers ---

/// Quantified poly variable shorthand (like `q(i)` in Gleam).
pub fn q(i: usize) -> Poly {
    Type::Var((true, i))
}

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

/// Free type variables of a mono type.
fn ftv(type_: &Mono) -> std::collections::HashSet<usize> {
    use std::collections::HashSet;
    match type_ {
        Type::Var(x) => {
            let mut s = HashSet::new();
            s.insert(*x);
            s
        }
        Type::Fun(arg, eff, ret) => {
            let mut s = ftv(arg);
            s.extend(ftv(eff));
            s.extend(ftv(ret));
            s
        }
        Type::Integer | Type::Binary | Type::String | Type::Empty | Type::Never => {
            HashSet::new()
        }
        Type::List(el) => ftv(el),
        Type::Record(rows) => ftv(rows),
        Type::Union(inner) => ftv(inner),
        Type::RowExtend(_, field, tail) => {
            let mut s = ftv(field);
            s.extend(ftv(tail));
            s
        }
        Type::EffectExtend(_, (lift, reply), tail) => {
            let mut s = ftv(lift);
            s.extend(ftv(reply));
            s.extend(ftv(tail));
            s
        }
        Type::Promise(inner) => ftv(inner),
    }
}

/// Replace closed effect tails (Empty) with fresh vars.
fn open_effect(eff: &Mono, level: usize, bindings: &mut Bindings) -> Mono {
    match eff {
        Type::Empty => bindings.fresh_mono(level),
        Type::EffectExtend(label, (lift, reply), tail) => {
            let tail = open_effect(tail, level, bindings);
            Type::EffectExtend(
                label.clone(),
                (lift.clone(), reply.clone()),
                Box::new(tail),
            )
        }
        other => other.clone(),
    }
}

/// Open effect tails in function types (recursing into return type).
fn open(type_: &Mono, level: usize, bindings: &mut Bindings) -> Mono {
    match type_ {
        Type::Fun(arg, eff, ret) => {
            let eff = open_effect(eff, level, bindings);
            let ret = open(ret, level, bindings);
            Type::Fun(arg.clone(), Box::new(eff), Box::new(ret))
        }
        other => other.clone(),
    }
}

/// Extract the tail variable and the rebuilt effect chain without it.
fn eff_tail(eff: &Mono) -> (Option<usize>, Mono) {
    match eff {
        Type::Var(x) => (Some(*x), Type::Empty),
        Type::EffectExtend(l, f, tail) => {
            let (result, new_tail) = eff_tail(tail);
            (
                result,
                Type::EffectExtend(l.clone(), f.clone(), Box::new(new_tail)),
            )
        }
        _ => (None, eff.clone()),
    }
}

/// Close effect tails that would generalize and are not free in arg/ret.
fn close(type_: &Mono, level: usize, bindings: &Bindings) -> Mono {
    match &binding::resolve(type_, bindings) {
        Type::Fun(arg, eff, ret) => {
            let closed_eff = close_eff(arg, eff, ret, level, bindings);
            let closed_ret = close(ret, level, bindings);
            Type::Fun(arg.clone(), Box::new(closed_eff), Box::new(closed_ret))
        }
        _ => type_.clone(),
    }
}

fn close_eff(arg: &Mono, eff: &Mono, ret: &Mono, level: usize, bindings: &Bindings) -> Mono {
    let (last, mapped) = eff_tail(eff);
    match last {
        Some(i) => {
            match bindings.get(i) {
                Binding::Unbound(l) => {
                    let arg_ret_ftvs = ftv(arg).union(&ftv(ret)).copied().collect::<std::collections::HashSet<_>>();
                    if !arg_ret_ftvs.contains(&i) && *l > level {
                        mapped
                    } else {
                        eff.clone()
                    }
                }
                _ => eff.clone(),
            }
        }
        None => eff.clone(),
    }
}

/// Instantiate a poly scheme, open effects, record annotation.
fn prim(
    scheme: &Poly,
    env: &Env,
    eff: &Mono,
    level: usize,
    bindings: &mut Bindings,
    annotations: &mut Vec<NodeInfo>,
) -> (Mono, Mono) {
    let type_ = binding::instantiate(scheme, level, bindings);
    let opened = open(&type_, level, bindings);
    annotations.push(NodeInfo {
        result: Ok(()),
        typ: type_,
        eff: Type::Empty,
        scope: env.clone(),
    });
    (opened, eff.clone())
}

// --- Core inference ---

/// Main inference function. Pushes NodeInfo in pre-order DFS.
/// Returns (inferred_type, resulting_effect).
fn do_infer(
    source: &Node,
    env: &Env,
    eff: &Mono,
    refs: &HashMap<String, Poly>,
    level: usize,
    bindings: &mut Bindings,
    annotations: &mut Vec<NodeInfo>,
) -> (Mono, Mono) {
    match &source.0 {
        Expr::Variable { label } => {
            if let Some(scheme) = env.iter().find_map(|(k, v)| {
                if k == label { Some(v) } else { None }
            }) {
                let type_ = binding::instantiate(scheme, level, bindings);
                let opened = open(&type_, level, bindings);
                annotations.push(NodeInfo {
                    result: Ok(()),
                    typ: type_,
                    eff: Type::Empty,
                    scope: env.clone(),
                });
                (opened, eff.clone())
            } else {
                let type_ = bindings.fresh_mono(level);
                annotations.push(NodeInfo {
                    result: Err(Reason::MissingVariable(label.clone())),
                    typ: type_.clone(),
                    eff: Type::Empty,
                    scope: env.clone(),
                });
                (type_, eff.clone())
            }
        }

        Expr::Lambda { label, body } => {
            let type_x = bindings.fresh_mono(level);
            let i = match &type_x {
                Type::Var(i) => *i,
                _ => unreachable!(),
            };
            let scheme_x: Poly = Type::Var((false, i));

            let inner_level = level + 1;
            let type_eff = bindings.fresh_mono(inner_level);

            let mut inner_env = vec![(label.clone(), scheme_x)];
            inner_env.extend(env.iter().cloned());

            let ann_idx = annotations.len();
            annotations.push(NodeInfo {
                result: Ok(()),
                typ: Type::Empty, // placeholder
                eff: Type::Empty,
                scope: env.clone(),
            });

            let (type_r, _type_eff_out) =
                do_infer(body, &inner_env, &type_eff, refs, inner_level, bindings, annotations);

            let type_eff_resolved = binding::resolve(&type_eff, bindings);
            let type_ = Type::Fun(
                Box::new(type_x),
                Box::new(type_eff_resolved),
                Box::new(type_r.clone()),
            );
            let record = close(&type_, level, bindings);
            annotations[ann_idx].typ = record;

            (type_, eff.clone())
        }

        Expr::Apply { func, argument } => {
            let inner_level = level + 1;

            let ann_idx = annotations.len();
            annotations.push(NodeInfo {
                result: Ok(()),
                typ: Type::Empty, // placeholder
                eff: Type::Empty,
                scope: env.clone(),
            });

            let (ty_fun, eff_after_fun) =
                do_infer(func, env, eff, refs, inner_level, bindings, annotations);
            let (ty_arg, eff_after_arg) =
                do_infer(argument, env, &eff_after_fun, refs, inner_level, bindings, annotations);

            let ty_ret = bindings.fresh_mono(inner_level);
            let test_eff = bindings.fresh_mono(inner_level);

            let expected = Type::Fun(
                Box::new(ty_arg),
                Box::new(test_eff.clone()),
                Box::new(ty_ret.clone()),
            );

            let mut result = match unify::unify(&expected, &ty_fun, inner_level, bindings) {
                Ok(()) => Ok(()),
                Err(reason) => Err(reason),
            };

            // Effect raising: check if test_eff tail would generalize
            // Gleam uses `l > (level - 1)` with signed ints; equivalent to `l >= level` for usize
            let resolved_test_eff = binding::resolve(&test_eff, bindings);
            let (last, mapped) = eff_tail(&resolved_test_eff);
            let raised = match last {
                None => test_eff.clone(),
                Some(i) => {
                    match bindings.get(i) {
                        Binding::Unbound(l) if *l >= level => mapped,
                        _ => test_eff.clone(),
                    }
                }
            };

            // Unify test_eff with ambient eff
            match unify::unify(&test_eff, &eff_after_arg, level, bindings) {
                Ok(()) => {}
                Err(reason) => {
                    if result.is_ok() {
                        result = Err(reason);
                    }
                }
            }

            let record = close(&ty_ret, level, bindings);
            annotations[ann_idx].typ = record;
            annotations[ann_idx].eff = raised.clone();
            annotations[ann_idx].result = result;

            (ty_ret, eff_after_arg)
        }

        Expr::Let {
            label,
            definition,
            body,
        } => {
            let ann_idx = annotations.len();
            annotations.push(NodeInfo {
                result: Ok(()),
                typ: Type::Empty, // placeholder
                eff: Type::Empty,
                scope: env.clone(),
            });

            let inner_level = level + 1;
            let (ty_value, eff_after_value) =
                do_infer(definition, env, eff, refs, inner_level, bindings, annotations);

            let closed_value = close(&ty_value, level, bindings);
            let sch_value = binding::generalize(&closed_value, level, &*bindings);

            let mut body_env = vec![(label.clone(), sch_value)];
            body_env.extend(env.iter().cloned());

            let (ty_then, eff_after_then) =
                do_infer(body, &body_env, &eff_after_value, refs, level, bindings, annotations);

            annotations[ann_idx].typ = ty_then.clone();

            (ty_then, eff_after_then)
        }

        Expr::Vacant => {
            let type_ = bindings.fresh_mono(level);
            annotations.push(NodeInfo {
                result: Err(Reason::Todo),
                typ: type_.clone(),
                eff: Type::Empty,
                scope: env.clone(),
            });
            (type_, eff.clone())
        }

        Expr::Integer { .. } => prim(&Type::Integer, env, eff, level, bindings, annotations),
        Expr::Binary { .. } => prim(&Type::Binary, env, eff, level, bindings, annotations),
        Expr::String { .. } => prim(&Type::String, env, eff, level, bindings, annotations),

        // --- Data structures (Milestone 7) ---
        Expr::Tail => prim(&Type::List(Box::new(q(0))), env, eff, level, bindings, annotations),
        Expr::Cons => {
            let scheme = pure2(q(0), Type::List(Box::new(q(0))), Type::List(Box::new(q(0))));
            prim(&scheme, env, eff, level, bindings, annotations)
        }
        Expr::Empty => prim(&Type::Record(Box::new(Type::Empty)), env, eff, level, bindings, annotations),
        Expr::Extend { label: l } => {
            let scheme = pure2(
                q(0),
                Type::Record(Box::new(q(1))),
                Type::Record(Box::new(Type::RowExtend(l.clone(), Box::new(q(0)), Box::new(q(1))))),
            );
            prim(&scheme, env, eff, level, bindings, annotations)
        }
        Expr::Overwrite { label: l } => {
            let scheme = pure2(
                q(0),
                Type::Record(Box::new(Type::RowExtend(l.clone(), Box::new(q(1)), Box::new(q(2))))),
                Type::Record(Box::new(Type::RowExtend(l.clone(), Box::new(q(0)), Box::new(q(2))))),
            );
            prim(&scheme, env, eff, level, bindings, annotations)
        }
        Expr::Select { label: l } => {
            let scheme = pure1(
                Type::Record(Box::new(Type::RowExtend(l.clone(), Box::new(q(0)), Box::new(q(1))))),
                q(0),
            );
            prim(&scheme, env, eff, level, bindings, annotations)
        }
        Expr::Tag { label: l } => {
            let scheme = pure1(
                q(0),
                Type::Union(Box::new(Type::RowExtend(l.clone(), Box::new(q(0)), Box::new(q(1))))),
            );
            prim(&scheme, env, eff, level, bindings, annotations)
        }
        Expr::Case { label: l } => {
            let inner = q(0);
            let eff_q = q(1);
            let return_ = q(2);
            let tail = q(3);
            let input = Type::Union(Box::new(Type::RowExtend(
                l.clone(),
                Box::new(inner.clone()),
                Box::new(tail.clone()),
            )));
            let branch = Type::Fun(Box::new(inner), Box::new(eff_q.clone()), Box::new(return_.clone()));
            let otherwise = Type::Fun(
                Box::new(Type::Union(Box::new(tail))),
                Box::new(eff_q.clone()),
                Box::new(return_.clone()),
            );
            let exec = Type::Fun(Box::new(input), Box::new(eff_q), Box::new(return_));
            let scheme = pure2(branch, otherwise, exec);
            prim(&scheme, env, eff, level, bindings, annotations)
        }
        Expr::NoCases => {
            let scheme = pure1(Type::Union(Box::new(Type::Empty)), q(0));
            prim(&scheme, env, eff, level, bindings, annotations)
        }

        // --- Effects & Builtins (Milestone 8) ---
        Expr::Perform { label: l } => {
            let scheme = Type::Fun(
                Box::new(q(0)),
                Box::new(Type::EffectExtend(
                    l.clone(),
                    (Box::new(q(0)), Box::new(q(1))),
                    Box::new(Type::Empty),
                )),
                Box::new(q(1)),
            );
            prim(&scheme, env, eff, level, bindings, annotations)
        }
        Expr::Handle { label: l } => {
            let lift = q(0);
            let reply = q(1);
            let tail = q(2);
            let return_ = q(3);
            let kont = Type::Fun(Box::new(reply.clone()), Box::new(tail.clone()), Box::new(return_.clone()));
            let handler = Type::Fun(
                Box::new(lift.clone()),
                Box::new(Type::Empty),
                Box::new(Type::Fun(Box::new(kont), Box::new(tail.clone()), Box::new(return_.clone()))),
            );
            let exec = Type::Fun(
                Box::new(Type::Record(Box::new(Type::Empty))),
                Box::new(Type::EffectExtend(
                    l.clone(),
                    (Box::new(lift), Box::new(reply)),
                    Box::new(tail.clone()),
                )),
                Box::new(return_.clone()),
            );
            let scheme = Type::Fun(
                Box::new(handler),
                Box::new(Type::Empty),
                Box::new(Type::Fun(Box::new(exec), Box::new(tail), Box::new(return_))),
            );
            prim(&scheme, env, eff, level, bindings, annotations)
        }
        Expr::Builtin { identifier } => {
            match crate::builtins::lookup(identifier) {
                Some(poly) => prim(&poly, env, eff, level, bindings, annotations),
                None => {
                    let type_ = bindings.fresh_mono(level);
                    annotations.push(NodeInfo {
                        result: Err(Reason::MissingBuiltin(identifier.clone())),
                        typ: type_.clone(),
                        eff: Type::Empty,
                        scope: env.clone(),
                    });
                    (type_, eff.clone())
                }
            }
        }
        Expr::Reference { identifier } => {
            lookup_ref(refs, &Reason::MissingReference(identifier.clone()), identifier, env, eff, level, bindings, annotations)
        }
        Expr::Release {
            package,
            release,
            identifier,
        } => {
            let reason = Reason::UndefinedRelease {
                package: package.clone(),
                release: *release,
                identifier: identifier.clone(),
            };
            lookup_ref(refs, &reason, identifier, env, eff, level, bindings, annotations)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn lookup_ref(
    refs: &HashMap<String, Poly>,
    reason: &Reason,
    id: &str,
    env: &Env,
    eff: &Mono,
    level: usize,
    bindings: &mut Bindings,
    annotations: &mut Vec<NodeInfo>,
) -> (Mono, Mono) {
    if let Some(poly) = refs.get(id) {
        prim(poly, env, eff, level, bindings, annotations)
    } else {
        let type_ = bindings.fresh_mono(level);
        annotations.push(NodeInfo {
            result: Err(reason.clone()),
            typ: type_.clone(),
            eff: Type::Empty,
            scope: env.clone(),
        });
        (type_, eff.clone())
    }
}

// --- Convenience for tests ---

/// Lower-level infer function matching Gleam's `infer` (used in tests).
pub fn infer(
    source: &Node,
    eff: &Mono,
    refs: &HashMap<String, Poly>,
    level: usize,
    bindings: &mut Bindings,
) -> Vec<NodeInfo> {
    let env: Env = Vec::new();
    let mut annotations = Vec::new();
    do_infer(source, &env, eff, refs, level, bindings, &mut annotations);
    annotations
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::debug;

    fn parse(src: &str) -> Node {
        eyg_parser::from_string(src).expect("parse should succeed")
    }

    /// Resolve all annotations and render as (result, type_string, effect_string).
    fn calc(source: &str, eff: &Mono) -> Vec<(Result<(), Reason>, String, String)> {
        let mut bindings = Bindings::new();
        let refs = HashMap::new();
        let anns = infer(&parse(source), eff, &refs, 0, &mut bindings);
        anns.iter()
            .map(|info| {
                let typ = binding::resolve(&info.typ, &bindings);
                let eff = binding::resolve(&info.eff, &bindings);
                (info.result.clone(), debug::render_mono(&typ), debug::render_effects(&eff))
            })
            .collect()
    }

    fn do_calc(source: &str, eff: &Mono, bindings: &mut Bindings) -> Vec<(Result<(), Reason>, String, String)> {
        let refs = HashMap::new();
        let anns = infer(&parse(source), eff, &refs, 0, bindings);
        anns.iter()
            .map(|info| {
                let typ = binding::resolve(&info.typ, &bindings);
                let eff = binding::resolve(&info.eff, &bindings);
                (info.result.clone(), debug::render_mono(&typ), debug::render_effects(&eff))
            })
            .collect()
    }

    fn ok(typ: &str, eff: &str) -> (Result<(), Reason>, String, String) {
        (Ok(()), typ.to_string(), eff.to_string())
    }

    #[test]
    fn variable() {
        assert_eq!(
            calc("x", &Type::Empty),
            vec![(Err(Reason::MissingVariable("x".into())), "0".into(), "".into())]
        );
    }

    #[test]
    fn literal() {
        assert_eq!(calc("5", &Type::Empty), vec![ok("Integer", "")]);
        assert_eq!(calc("\"hello\"", &Type::Empty), vec![ok("String", "")]);
    }

    #[test]
    fn simple_function() {
        assert_eq!(
            calc("(_) -> { 5 }", &Type::Empty),
            vec![ok("(0) -> Integer", ""), ok("Integer", "")]
        );

        assert_eq!(
            calc("(x) -> { x }(5)", &Type::Empty),
            vec![
                ok("Integer", ""),
                ok("(Integer) -> Integer", ""),
                ok("Integer", ""),
                ok("Integer", ""),
            ]
        );

        assert_eq!(
            calc("(x, _) -> {\n    x\n  }(1, \"\")", &Type::Empty),
            vec![
                ok("Integer", ""),
                ok("(String) -> Integer", ""),
                ok("(Integer, String) -> Integer", ""),
                ok("(String) -> Integer", ""),
                ok("Integer", ""),
                ok("Integer", ""),
                ok("String", ""),
            ]
        );

        assert_eq!(
            calc("(_, z) -> {\n    z\n  }(1, \"\")", &Type::Empty),
            vec![
                ok("String", ""),
                ok("(String) -> String", ""),
                ok("(Integer, String) -> String", ""),
                ok("(String) -> String", ""),
                ok("String", ""),
                ok("Integer", ""),
                ok("String", ""),
            ]
        );
    }

    #[test]
    fn let_binding() {
        assert_eq!(
            calc("let x = 5\n  let y = \"\"\n  x", &Type::Empty),
            vec![
                ok("Integer", ""),
                ok("Integer", ""),
                ok("Integer", ""),
                ok("String", ""),
                ok("Integer", ""),
            ]
        );

        // shadowing
        assert_eq!(
            calc("let x = 5\n  let x = \"\"\n  x", &Type::Empty),
            vec![
                ok("String", ""),
                ok("Integer", ""),
                ok("String", ""),
                ok("String", ""),
                ok("String", ""),
            ]
        );
    }

    #[test]
    fn let_polymorphism() {
        assert_eq!(
            calc("let f = (x) -> { x }\n  let y = f(3)\n  f(\"hey\")", &Type::Empty),
            vec![
                ok("String", ""),
                ok("(0) -> 0", ""),
                ok("0", ""),
                ok("String", ""),
                ok("Integer", ""),
                ok("(Integer) -> Integer", ""),
                ok("Integer", ""),
                ok("String", ""),
                ok("(String) -> String", ""),
                ok("String", ""),
            ]
        );
    }

    #[test]
    fn list() {
        assert_eq!(calc("[]", &Type::Empty), vec![ok("List(0)", "")]);

        assert_eq!(
            calc("[3]", &Type::Empty),
            vec![
                ok("List(Integer)", ""),
                ok("(List(Integer)) -> List(Integer)", ""),
                ok("(Integer, List(Integer)) -> List(Integer)", ""),
                ok("Integer", ""),
                ok("List(Integer)", ""),
            ]
        );
    }

    #[test]
    fn record() {
        assert_eq!(calc("{}", &Type::Empty), vec![ok("{}", "")]);

        assert_eq!(
            calc("{a: 3}", &Type::Empty),
            vec![
                ok("{a: Integer}", ""),
                ok("({}) -> {a: Integer}", ""),
                ok("(Integer, {}) -> {a: Integer}", ""),
                ok("Integer", ""),
                ok("{}", ""),
            ]
        );
    }

    #[test]
    fn select() {
        // {name: 5}.name — parser doesn't support dot after record literal,
        // so we use let binding
        assert_eq!(
            calc("let r = {name: 5}\n  r.name", &Type::Empty),
            vec![
                ok("Integer", ""),
                ok("{name: Integer}", ""),
                ok("({}) -> {name: Integer}", ""),
                ok("(Integer, {}) -> {name: Integer}", ""),
                ok("Integer", ""),
                ok("{}", ""),
                ok("Integer", ""),
                ok("({name: Integer}) -> Integer", ""),
                ok("{name: Integer}", ""),
            ]
        );

        assert_eq!(
            calc("x.name", &Type::Empty),
            vec![
                ok("0", ""),
                ok("({name: 0, ..1}) -> 0", ""),
                (Err(Reason::MissingVariable("x".into())), "{name: 0, ..1}".into(), "".into()),
            ]
        );

        // {}.name → MissingRow; use let binding
        let result = calc("let r = {}\n  r.name", &Type::Empty);
        // let, {}, select(r.name), select prim, variable r
        assert_eq!(result.len(), 5);
        // Overall let type: a fresh var (from error recovery)
        // The Apply (select applied to r) has the error
        assert!(result.iter().any(|(r, _, _)| matches!(r, Err(Reason::MissingRow(l)) if l == "name")));
    }

    #[test]
    fn tag() {
        assert_eq!(
            calc("Ok", &Type::Empty),
            vec![ok("(0) -> Ok: 0 | ..1", "")]
        );

        assert_eq!(
            calc("Ok(8)", &Type::Empty),
            vec![
                ok("Ok: Integer | ..1", ""),
                ok("(Integer) -> Ok: Integer | ..1", ""),
                ok("Integer", ""),
            ]
        );
    }

    #[test]
    fn builtin() {
        assert_eq!(
            calc("!int_add", &Type::Empty),
            vec![ok("(Integer, Integer) -> Integer", "")]
        );

        assert_eq!(
            calc("!int_add(1, 2)", &Type::Empty),
            vec![
                ok("Integer", ""),
                ok("(Integer) -> Integer", ""),
                ok("(Integer, Integer) -> Integer", ""),
                ok("Integer", ""),
                ok("Integer", ""),
            ]
        );

        let mut bindings = Bindings::new();
        let var = bindings.fresh_mono(0);
        assert_eq!(
            do_calc("!int_add(1, 2)", &var, &mut bindings),
            vec![
                (Ok(()), "Integer".into(), "".into()),
                (Ok(()), "(Integer) -> Integer".into(), "".into()),
                (Ok(()), "(Integer, Integer) -> Integer".into(), "".into()),
                (Ok(()), "Integer".into(), "".into()),
                (Ok(()), "Integer".into(), "".into()),
            ]
        );

        assert_eq!(
            calc("!not_a_thing", &Type::Empty),
            vec![(Err(Reason::MissingBuiltin("not_a_thing".into())), "0".into(), "".into())]
        );
    }

    #[test]
    fn perform() {
        let mut bindings = Bindings::new();
        let var = bindings.fresh_mono(0);
        assert_eq!(
            do_calc("perform Log(\"thing\")", &var, &mut bindings),
            vec![
                (Ok(()), "2".into(), "Log(↑String ↓2)".into()),
                (Ok(()), "(String <Log(↑String ↓2)>) -> 2".into(), "".into()),
                (Ok(()), "String".into(), "".into()),
            ]
        );
    }

    #[test]
    fn perform_unifies_with_env() {
        let eff = Type::EffectExtend(
            "Log".into(),
            (
                Box::new(Type::String),
                Box::new(Type::Record(Box::new(Type::Empty))),
            ),
            Box::new(Type::Empty),
        );
        let result = calc("perform Log(5)", &eff);
        assert_eq!(result.len(), 3);
        assert!(matches!(&result[0].0, Err(Reason::TypeMismatch(..))));
        assert_eq!(result[0].1, "1");
        assert_eq!(result[0].2, "Log(↑Integer ↓1)");
    }

    #[test]
    fn only_unknown_effect() {
        assert_eq!(
            calc("(f) -> {\n    f(5)\n  }", &Type::Empty),
            vec![
                ok("((Integer <..1>) -> 2 <..1>) -> 2", ""),
                ok("2", "..1"),
                ok("(Integer <..1>) -> 2", ""),
                ok("Integer", ""),
            ]
        );
    }
}
