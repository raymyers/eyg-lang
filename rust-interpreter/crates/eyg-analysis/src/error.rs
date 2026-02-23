use crate::types::Mono;

#[derive(Debug, Clone, PartialEq)]
pub enum Reason {
    Todo,
    MissingVariable(String),
    MissingBuiltin(String),
    MissingReference(String),
    UndefinedRelease {
        package: String,
        release: i64,
        identifier: String,
    },
    TypeMismatch(Mono, Mono),
    MissingRow(String),
    Recursive,
    SameTail(Mono, Mono),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Type;

    #[test]
    fn test_all_reason_variants() {
        let reasons: Vec<Reason> = vec![
            Reason::Todo,
            Reason::MissingVariable("x".into()),
            Reason::MissingBuiltin("int_add".into()),
            Reason::MissingReference("abc123".into()),
            Reason::UndefinedRelease {
                package: "pkg".into(),
                release: 1,
                identifier: "mod".into(),
            },
            Reason::TypeMismatch(Type::Integer, Type::String),
            Reason::MissingRow("name".into()),
            Reason::Recursive,
            Reason::SameTail(Type::Var(0), Type::Var(1)),
        ];
        assert_eq!(reasons.len(), 9);
    }

    #[test]
    fn test_reason_equality() {
        assert_eq!(Reason::Todo, Reason::Todo);
        assert_eq!(
            Reason::MissingVariable("x".into()),
            Reason::MissingVariable("x".into())
        );
        assert_ne!(Reason::Todo, Reason::Recursive);
        assert_ne!(
            Reason::MissingVariable("x".into()),
            Reason::MissingVariable("y".into())
        );
    }

    #[test]
    fn test_reason_clone() {
        let r = Reason::TypeMismatch(Type::Integer, Type::String);
        let r2 = r.clone();
        assert_eq!(r, r2);
    }
}
