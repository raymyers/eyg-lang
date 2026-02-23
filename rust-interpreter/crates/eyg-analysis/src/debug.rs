use crate::error::Reason;
use crate::types::Mono;
use crate::types::Type;

/// Render a monomorphic type as a human-readable string.
pub fn render_mono(typ: &Mono) -> String {
    match typ {
        Type::Var(i) => i.to_string(),
        Type::Integer => "Integer".into(),
        Type::Binary => "Binary".into(),
        Type::String => "String".into(),
        Type::Never => "Never".into(),
        Type::List(el) => format!("List({})", render_mono(el)),
        Type::Fun(from, eff, to) => render_function(to, vec![(from, eff)]),
        Type::Union(row) => render_row(row).join(" | "),
        Type::Record(row) => format!("{{{}}}", render_row(row).join(", ")),
        Type::EffectExtend(..) => format!("<{}>", render_effects(typ)),
        Type::Promise(inner) => format!("Promise({})", render_mono(inner)),
        // Bare row (RowExtend or Empty at top level)
        Type::Empty => "{}".into(),
        Type::RowExtend(..) => format!("{{{}}}", render_row(typ).join("")),
    }
}

fn render_function<'a>(to: &'a Mono, mut acc: Vec<(&'a Mono, &'a Mono)>) -> String {
    match to {
        Type::Fun(from, eff, ret) => {
            acc.push((from, eff));
            render_function(ret, acc)
        }
        _ => {
            let rendered: Vec<String> = acc
                .iter()
                .map(|(arg, eff)| {
                    let arg_str = render_mono(arg);
                    match **eff {
                        Type::Empty => arg_str,
                        _ => format!("{} <{}>", arg_str, render_effects(eff)),
                    }
                })
                .collect();
            format!("({}) -> {}", rendered.join(", "), render_mono(to))
        }
    }
}

fn render_row(r: &Mono) -> Vec<String> {
    match r {
        Type::Empty => vec![],
        Type::Var(i) => vec![format!("..{}", i)],
        Type::RowExtend(label, value, tail) => {
            let mut result = vec![format!("{}: {}", label, render_mono(value))];
            result.extend(render_row(tail));
            result
        }
        _ => vec!["not a valid row".into()],
    }
}

/// Render an effect type as a human-readable string.
pub fn render_effects(effects: &Mono) -> String {
    match effects {
        Type::Var(i) => format!("..{}", i),
        Type::Empty => String::new(),
        Type::EffectExtend(label, (lift, resume), tail) => {
            let mut acc = vec![render_effect(label, lift, resume)];
            collect_effects(tail, &mut acc);
            acc.join(", ")
        }
        _ => "not a valid effect".into(),
    }
}

fn render_effect(label: &str, lift: &Mono, resume: &Mono) -> String {
    format!("{}(↑{} ↓{})", label, render_mono(lift), render_mono(resume))
}

fn collect_effects(eff: &Mono, acc: &mut Vec<String>) {
    match eff {
        Type::EffectExtend(label, (lift, resume), tail) => {
            acc.push(render_effect(label, lift, resume));
            collect_effects(tail, acc);
        }
        Type::Var(i) => acc.push(format!("..{}", i)),
        Type::Empty => {}
        _ => acc.push("unexpected effect".into()),
    }
}

/// Render a type error reason as a human-readable string.
pub fn render_reason(reason: &Reason) -> String {
    match reason {
        Reason::Todo => "code incomplete".into(),
        Reason::MissingVariable(label) => format!("missing variable '{}'", label),
        Reason::MissingBuiltin(label) => format!("missing variable '!{}'", label),
        Reason::MissingReference(label) => format!("missing reference #{}", label),
        Reason::UndefinedRelease {
            package, release, ..
        } => format!("release undefined: @{}:{}", package, release),
        Reason::MissingRow(label) => format!("missing row '{}'", label),
        Reason::TypeMismatch(expected, given) => format!(
            "type missmatch given: {} expected: {}",
            render_mono(given),
            render_mono(expected)
        ),
        Reason::Recursive => "Recursive".into(),
        Reason::SameTail(expected, given) => format!(
            "same tail given: {} expected: {}",
            render_mono(given),
            render_mono(expected)
        ),
    }
}

impl std::fmt::Display for Reason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", render_reason(self))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pure_function() {
        let t = Type::Fun(
            Box::new(Type::Integer),
            Box::new(Type::Empty),
            Box::new(Type::String),
        );
        assert_eq!(render_mono(&t), "(Integer) -> String");
    }

    #[test]
    fn multiple_argument_function() {
        let t = Type::Fun(
            Box::new(Type::Integer),
            Box::new(Type::Empty),
            Box::new(Type::Fun(
                Box::new(Type::Integer),
                Box::new(Type::Empty),
                Box::new(Type::String),
            )),
        );
        assert_eq!(render_mono(&t), "(Integer, Integer) -> String");
    }

    #[test]
    fn open_function() {
        let t = Type::Fun(
            Box::new(Type::Integer),
            Box::new(Type::Var(1)),
            Box::new(Type::String),
        );
        assert_eq!(render_mono(&t), "(Integer <..1>) -> String");
    }

    #[test]
    fn closed_effectful_function() {
        let t = Type::Fun(
            Box::new(Type::Integer),
            Box::new(Type::EffectExtend(
                "Abort".into(),
                (Box::new(Type::String), Box::new(Type::unit())),
                Box::new(Type::EffectExtend(
                    "Count".into(),
                    (Box::new(Type::unit()), Box::new(Type::Integer)),
                    Box::new(Type::Empty),
                )),
            )),
            Box::new(Type::String),
        );
        assert_eq!(
            render_mono(&t),
            "(Integer <Abort(↑String ↓{}), Count(↑{} ↓Integer)>) -> String"
        );
    }

    #[test]
    fn open_effectful_function() {
        let t = Type::Fun(
            Box::new(Type::Integer),
            Box::new(Type::EffectExtend(
                "Abort".into(),
                (Box::new(Type::String), Box::new(Type::unit())),
                Box::new(Type::Var(2)),
            )),
            Box::new(Type::String),
        );
        assert_eq!(
            render_mono(&t),
            "(Integer <Abort(↑String ↓{}), ..2>) -> String"
        );
    }

    #[test]
    fn polymorphic_effect() {
        let f = Type::Fun(
            Box::new(Type::String),
            Box::new(Type::Var(0)),
            Box::new(Type::String),
        );
        let t = Type::Fun(
            Box::new(f),
            Box::new(Type::Empty),
            Box::new(Type::Fun(
                Box::new(Type::Integer),
                Box::new(Type::Var(0)),
                Box::new(Type::String),
            )),
        );
        assert_eq!(
            render_mono(&t),
            "((String <..0>) -> String, Integer <..0>) -> String"
        );
    }

    #[test]
    fn render_basic_types() {
        assert_eq!(render_mono(&Type::Integer), "Integer");
        assert_eq!(render_mono(&Type::Binary), "Binary");
        assert_eq!(render_mono(&Type::String), "String");
        assert_eq!(render_mono(&Type::Never), "Never");
        assert_eq!(render_mono(&Type::Var(42)), "42");
    }

    #[test]
    fn render_list() {
        assert_eq!(
            render_mono(&Type::List(Box::new(Type::Integer))),
            "List(Integer)"
        );
    }

    #[test]
    fn render_record() {
        let rec = Type::record(vec![
            ("name".into(), Type::String),
            ("age".into(), Type::Integer),
        ]);
        assert_eq!(render_mono(&rec), "{name: String, age: Integer}");
    }

    #[test]
    fn render_empty_record() {
        assert_eq!(render_mono(&Type::unit()), "{}");
    }

    #[test]
    fn render_union() {
        let u = Type::union(vec![
            ("Ok".into(), Type::Integer),
            ("Error".into(), Type::String),
        ]);
        assert_eq!(render_mono(&u), "Ok: Integer | Error: String");
    }

    #[test]
    fn render_promise() {
        assert_eq!(
            render_mono(&Type::Promise(Box::new(Type::Integer))),
            "Promise(Integer)"
        );
    }

    #[test]
    fn render_effects_empty() {
        assert_eq!(render_effects(&Type::Empty), "");
    }

    #[test]
    fn render_effects_open() {
        assert_eq!(render_effects(&Type::Var(3)), "..3");
    }

    #[test]
    fn render_reason_variants() {
        assert_eq!(render_reason(&Reason::Todo), "code incomplete");
        assert_eq!(
            render_reason(&Reason::MissingVariable("x".into())),
            "missing variable 'x'"
        );
        assert_eq!(
            render_reason(&Reason::MissingBuiltin("int_add".into())),
            "missing variable '!int_add'"
        );
        assert_eq!(
            render_reason(&Reason::MissingReference("abc".into())),
            "missing reference #abc"
        );
        assert_eq!(
            render_reason(&Reason::UndefinedRelease {
                package: "pkg".into(),
                release: 1,
                identifier: "mod".into(),
            }),
            "release undefined: @pkg:1"
        );
        assert_eq!(
            render_reason(&Reason::MissingRow("name".into())),
            "missing row 'name'"
        );
        assert_eq!(
            render_reason(&Reason::TypeMismatch(Type::Integer, Type::String)),
            "type missmatch given: String expected: Integer"
        );
        assert_eq!(render_reason(&Reason::Recursive), "Recursive");
        assert_eq!(
            render_reason(&Reason::SameTail(Type::Var(0), Type::Var(1))),
            "same tail given: 1 expected: 0"
        );
    }

    #[test]
    fn display_trait_for_reason() {
        let r = Reason::Todo;
        assert_eq!(format!("{}", r), "code incomplete");
    }
}
