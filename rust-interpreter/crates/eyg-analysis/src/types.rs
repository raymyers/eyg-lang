/// Core type representation, generic over the variable type.
/// `Mono = Type<usize>` uses plain indices, `Poly = Type<(bool, usize)>` marks quantified vars.
#[derive(Debug, Clone, PartialEq)]
pub enum Type<V> {
    Var(V),
    Fun(Box<Type<V>>, Box<Type<V>>, Box<Type<V>>), // arg, effect, return
    Binary,
    Integer,
    String,
    List(Box<Type<V>>),
    Record(Box<Type<V>>),
    Union(Box<Type<V>>),
    Empty,
    RowExtend(std::string::String, Box<Type<V>>, Box<Type<V>>),
    EffectExtend(std::string::String, (Box<Type<V>>, Box<Type<V>>), Box<Type<V>>),
    Never,
    Promise(Box<Type<V>>),
}

pub type Mono = Type<usize>;
pub type Poly = Type<(bool, usize)>;

impl<V> Type<V> {
    pub fn unit() -> Self {
        Type::Record(Box::new(Type::Empty))
    }

    pub fn boolean() -> Self {
        Type::Union(Box::new(Type::RowExtend(
            "True".into(),
            Box::new(Self::unit()),
            Box::new(Type::RowExtend(
                "False".into(),
                Box::new(Self::unit()),
                Box::new(Type::Empty),
            )),
        )))
    }

    pub fn result(value: Type<V>, reason: Type<V>) -> Self {
        Type::Union(Box::new(Type::RowExtend(
            "Ok".into(),
            Box::new(value),
            Box::new(Type::RowExtend(
                "Error".into(),
                Box::new(reason),
                Box::new(Type::Empty),
            )),
        )))
    }

    pub fn rows(pairs: Vec<(std::string::String, Type<V>)>) -> Type<V> {
        pairs
            .into_iter()
            .rev()
            .fold(Type::Empty, |tail, (label, value)| {
                Type::RowExtend(label, Box::new(value), Box::new(tail))
            })
    }

    pub fn record(pairs: Vec<(std::string::String, Type<V>)>) -> Self {
        Type::Record(Box::new(Self::rows(pairs)))
    }

    pub fn union(pairs: Vec<(std::string::String, Type<V>)>) -> Self {
        Type::Union(Box::new(Self::rows(pairs)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mono_variants() {
        let v: Mono = Type::Var(0);
        assert_eq!(v, Type::Var(0));

        let i: Mono = Type::Integer;
        assert_eq!(i, Type::Integer);

        let s: Mono = Type::String;
        assert_eq!(s, Type::String);

        let b: Mono = Type::Binary;
        assert_eq!(b, Type::Binary);

        let e: Mono = Type::Empty;
        assert_eq!(e, Type::Empty);

        let n: Mono = Type::Never;
        assert_eq!(n, Type::Never);
    }

    #[test]
    fn test_compound_types() {
        let list: Mono = Type::List(Box::new(Type::Integer));
        assert_eq!(list, Type::List(Box::new(Type::Integer)));

        let fun: Mono = Type::Fun(
            Box::new(Type::Integer),
            Box::new(Type::Empty),
            Box::new(Type::String),
        );
        assert!(matches!(fun, Type::Fun(..)));

        let promise: Mono = Type::Promise(Box::new(Type::Integer));
        assert_eq!(promise, Type::Promise(Box::new(Type::Integer)));
    }

    #[test]
    fn test_row_types() {
        let row: Mono = Type::RowExtend(
            "x".into(),
            Box::new(Type::Integer),
            Box::new(Type::Empty),
        );
        assert!(matches!(row, Type::RowExtend(..)));

        let eff: Mono = Type::EffectExtend(
            "Log".into(),
            (Box::new(Type::String), Box::new(Type::unit())),
            Box::new(Type::Empty),
        );
        assert!(matches!(eff, Type::EffectExtend(..)));
    }

    #[test]
    fn test_poly_variant() {
        let p: Poly = Type::Var((true, 0));
        assert_eq!(p, Type::Var((true, 0)));

        let free: Poly = Type::Var((false, 1));
        assert_ne!(p, free);
    }

    #[test]
    fn test_unit() {
        let u: Mono = Type::unit();
        assert_eq!(u, Type::Record(Box::new(Type::Empty)));
    }

    #[test]
    fn test_boolean() {
        let b: Mono = Type::boolean();
        match b {
            Type::Union(inner) => match *inner {
                Type::RowExtend(ref label, _, _) => assert_eq!(label, "True"),
                _ => panic!("expected RowExtend"),
            },
            _ => panic!("expected Union"),
        }
    }

    #[test]
    fn test_result() {
        let r: Mono = Type::result(Type::Integer, Type::String);
        match r {
            Type::Union(inner) => match *inner {
                Type::RowExtend(ref label, _, _) => assert_eq!(label, "Ok"),
                _ => panic!("expected RowExtend"),
            },
            _ => panic!("expected Union"),
        }
    }

    #[test]
    fn test_rows_and_record() {
        let rec: Mono = Type::record(vec![
            ("name".into(), Type::String),
            ("age".into(), Type::Integer),
        ]);
        match rec {
            Type::Record(inner) => match *inner {
                Type::RowExtend(ref label, _, _) => assert_eq!(label, "name"),
                _ => panic!("expected RowExtend"),
            },
            _ => panic!("expected Record"),
        }
    }

    #[test]
    fn test_union_constructor() {
        let u: Mono = Type::union(vec![
            ("Ok".into(), Type::Integer),
            ("Error".into(), Type::String),
        ]);
        match u {
            Type::Union(inner) => match *inner {
                Type::RowExtend(ref label, _, _) => assert_eq!(label, "Ok"),
                _ => panic!("expected RowExtend"),
            },
            _ => panic!("expected Union"),
        }
    }

    #[test]
    fn test_inequality() {
        let a: Mono = Type::Integer;
        let b: Mono = Type::String;
        assert_ne!(a, b);
    }
}
