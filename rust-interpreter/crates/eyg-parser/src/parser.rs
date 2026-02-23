use crate::token::Token;
use eyg_ir::ast::{node, Expr, Node};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    UnexpectedEnd,
    UnexpectedToken(Token, usize),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::UnexpectedEnd => write!(f, "unexpected end of input"),
            ParseError::UnexpectedToken(tok, pos) => {
                write!(f, "unexpected token `{tok}` at byte {pos}")
            }
        }
    }
}

type Tokens<'a> = &'a [(Token, usize)];
type PResult<'a, T> = Result<(T, Tokens<'a>), ParseError>;

fn pop(tokens: Tokens<'_>) -> PResult<'_, (&Token, usize)> {
    match tokens {
        [(tok, pos), rest @ ..] => Ok(((tok, *pos), rest)),
        [] => Err(ParseError::UnexpectedEnd),
    }
}

fn fail(tokens: Tokens) -> ParseError {
    match tokens {
        [(tok, pos), ..] => ParseError::UnexpectedToken(tok.clone(), *pos),
        [] => ParseError::UnexpectedEnd,
    }
}

// --- Patterns (for lambdas and let bindings) ---

#[derive(Debug)]
enum Pattern {
    Assign(String),
    Destructure(Vec<Match>),
}

/// A destructuring match: field name, optional (renamed) variable
#[derive(Debug)]
struct Match {
    field: String,
    var: Option<String>,
}

fn one_pattern(tokens: Tokens) -> PResult<Pattern> {
    let ((tok, _pos), rest) = pop(tokens)?;
    match tok {
        Token::Name(label) => Ok((Pattern::Assign(label.clone()), rest)),
        Token::LeftBrace => do_destructure(rest, Vec::new()),
        _ => Err(fail(tokens)),
    }
}

fn do_destructure(tokens: Tokens, mut acc: Vec<Match>) -> PResult<Pattern> {
    match tokens {
        [(Token::RightBrace, _), rest @ ..] => {
            acc.reverse();
            Ok((Pattern::Destructure(acc), rest))
        }
        [(Token::Name(field), _), (Token::Colon, _), (Token::Name(var), _), rest @ ..] => {
            acc.push(Match {
                field: field.clone(),
                var: Some(var.clone()),
            });
            match rest {
                [(Token::RightBrace, _), rest @ ..] => {
                    acc.reverse();
                    Ok((Pattern::Destructure(acc), rest))
                }
                [(Token::Comma, _), rest @ ..] => do_destructure(rest, acc),
                _ => Err(fail(rest)),
            }
        }
        [(Token::Name(field), _), rest @ ..] => {
            acc.push(Match {
                field: field.clone(),
                var: None,
            });
            match rest {
                [(Token::RightBrace, _), rest @ ..] => {
                    acc.reverse();
                    Ok((Pattern::Destructure(acc), rest))
                }
                [(Token::Comma, _), rest @ ..] => do_destructure(rest, acc),
                _ => Err(fail(rest)),
            }
        }
        _ => Err(fail(tokens)),
    }
}

fn do_patterns(tokens: Tokens, mut acc: Vec<Pattern>) -> PResult<Vec<Pattern>> {
    let (pattern, tokens) = one_pattern(tokens)?;
    acc.push(pattern);
    let ((tok, pos), rest) = pop(tokens)?;
    match tok {
        Token::Comma => do_patterns(rest, acc),
        Token::RightParen => Ok((acc, rest)),
        _ => Err(ParseError::UnexpectedToken(tok.clone(), pos)),
    }
}

fn destructured(matches: &[Match], body: Node) -> Node {
    matches.iter().fold(body, |acc, m| {
        let var = m.var.as_deref().unwrap_or(&m.field);
        node(Expr::Let {
            label: var.to_string(),
            definition: Box::new(node(Expr::Apply {
                func: Box::new(node(Expr::Select {
                    label: m.field.clone(),
                })),
                argument: Box::new(node(Expr::Variable {
                    label: "$".to_string(),
                })),
            })),
            body: Box::new(acc),
        })
    })
}

// --- Block parsing (for REPL/editor: let without continuation) ---

pub fn block(tokens: Tokens) -> PResult<Node> {
    let ((tok, _pos), _rest) = pop(tokens)?;
    match tok {
        Token::Let => {
            let rest = &tokens[1..]; // skip Let token
            let (pattern, rest) = one_pattern(rest)?;
            let rest = match rest {
                [(Token::Equal, _), rest @ ..] => rest,
                _ => return Err(fail(rest)),
            };
            let (value, rest) = expression(rest)?;
            match block(rest) {
                Ok((then, rest)) => {
                    let exp = match pattern {
                        Pattern::Assign(label) => node(Expr::Let {
                            label,
                            definition: Box::new(value),
                            body: Box::new(then),
                        }),
                        Pattern::Destructure(matches) => node(Expr::Let {
                            label: "$".to_string(),
                            definition: Box::new(value),
                            body: Box::new(destructured(&matches, then)),
                        }),
                    };
                    Ok((exp, rest))
                }
                Err(ParseError::UnexpectedEnd) => {
                    let then = node(Expr::Vacant);
                    let exp = match pattern {
                        Pattern::Assign(label) => node(Expr::Let {
                            label,
                            definition: Box::new(value),
                            body: Box::new(then),
                        }),
                        Pattern::Destructure(matches) => node(Expr::Let {
                            label: "$".to_string(),
                            definition: Box::new(value),
                            body: Box::new(destructured(&matches, then)),
                        }),
                    };
                    Ok((exp, rest))
                }
                Err(other) => Err(other),
            }
        }
        _ => expression(tokens),
    }
}

// --- Expression parsing ---

pub fn expression(tokens: Tokens) -> PResult<Node> {
    let ((tok, _start), rest) = pop(tokens)?;

    let (exp, rest) = match tok {
        Token::Name(label) => (
            node(Expr::Variable {
                label: label.clone(),
            }),
            rest,
        ),

        Token::Let => {
            let (pattern, rest) = one_pattern(rest)?;
            let rest = match rest {
                [(Token::Equal, _), rest @ ..] => rest,
                _ => return Err(fail(rest)),
            };
            let (value, rest) = expression(rest)?;
            let (then, rest) = expression(rest)?;
            let exp = match pattern {
                Pattern::Assign(label) => node(Expr::Let {
                    label,
                    definition: Box::new(value),
                    body: Box::new(then),
                }),
                Pattern::Destructure(matches) => node(Expr::Let {
                    label: "$".to_string(),
                    definition: Box::new(value),
                    body: Box::new(destructured(&matches, then)),
                }),
            };
            (exp, rest)
        }

        Token::LeftParen => {
            let (patterns_reversed, rest) = do_patterns(rest, Vec::new())?;
            let rest = match rest {
                [(Token::RightArrow, _), (Token::LeftBrace, _), rest @ ..] => rest,
                _ => return Err(fail(rest)),
            };
            let (body, rest) = expression(rest)?;
            let rest = match rest {
                [(Token::RightBrace, _), rest @ ..] => rest,
                _ => return Err(fail(rest)),
            };
            // Fold reversed patterns to build nested lambdas (auto-currying)
            let exp =
                patterns_reversed
                    .into_iter()
                    .rev()
                    .fold(body, |body, pattern| match pattern {
                        Pattern::Assign(label) => node(Expr::Lambda {
                            label,
                            body: Box::new(body),
                        }),
                        Pattern::Destructure(matches) => node(Expr::Lambda {
                            label: "$".to_string(),
                            body: Box::new(destructured(&matches, body)),
                        }),
                    });
            (exp, rest)
        }

        Token::Integer(raw) => {
            let value: i64 = raw.parse().expect("lexer produced invalid integer");
            (node(Expr::Integer { value }), rest)
        }

        Token::Minus => {
            let ((next_tok, _pos), rest) = pop(rest)?;
            match next_tok {
                Token::Integer(raw) => {
                    let value: i64 = raw.parse().expect("lexer produced invalid integer");
                    (node(Expr::Integer { value: -value }), rest)
                }
                _ => return Err(ParseError::UnexpectedToken(tok.clone(), _start)),
            }
        }

        Token::String(value) => (
            node(Expr::String {
                value: value.clone(),
            }),
            rest,
        ),

        Token::LeftSquare => return do_list(rest, Vec::new()),

        Token::LeftBrace => return do_record(rest, Vec::new()),

        Token::Uppername(label) => (
            node(Expr::Tag {
                label: label.clone(),
            }),
            rest,
        ),

        Token::Match => match rest {
            [(Token::LeftBrace, _), rest @ ..] => {
                let (exp, rest) = clauses(rest)?;
                (exp, rest)
            }
            _ => {
                let (subject, rest) = expression(rest)?;
                match rest {
                    [(Token::LeftBrace, _), rest @ ..] => {
                        let (exp, rest) = clauses(rest)?;
                        (
                            node(Expr::Apply {
                                func: Box::new(exp),
                                argument: Box::new(subject),
                            }),
                            rest,
                        )
                    }
                    _ => return Err(fail(rest)),
                }
            }
        },

        Token::Perform => match rest {
            [(Token::Uppername(label), _), rest @ ..] => (
                node(Expr::Perform {
                    label: label.clone(),
                }),
                rest,
            ),
            _ => return Err(fail(rest)),
        },

        Token::Handle => match rest {
            [(Token::Uppername(label), _), rest @ ..] => (
                node(Expr::Handle {
                    label: label.clone(),
                }),
                rest,
            ),
            _ => return Err(fail(rest)),
        },

        Token::Bang => match rest {
            [(Token::Name(label), _), rest @ ..] => (
                node(Expr::Builtin {
                    identifier: label.clone(),
                }),
                rest,
            ),
            _ => return Err(fail(rest)),
        },

        Token::Hash => match rest {
            [(Token::Name(label), _), rest @ ..] => (
                node(Expr::Reference {
                    identifier: label.clone(),
                }),
                rest,
            ),
            _ => return Err(fail(rest)),
        },

        Token::At => match rest {
            [(Token::Name(label), _), rest @ ..] => (
                node(Expr::Release {
                    package: label.clone(),
                    release: 0,
                    identifier: String::new(),
                }),
                rest,
            ),
            _ => return Err(fail(rest)),
        },

        _ => return Err(ParseError::UnexpectedToken(tok.clone(), _start)),
    };

    after_expression(exp, rest)
}

fn after_expression(exp: Node, rest: Tokens) -> PResult<Node> {
    match rest {
        // Function application: exp(arg, ...)
        [(Token::LeftParen, _), rest @ ..] => {
            let (arg, rest) = expression(rest)?;
            let (args, rest) = do_args(rest, vec![arg])?;
            let exp = args.into_iter().fold(exp, |acc, arg| {
                node(Expr::Apply {
                    func: Box::new(acc),
                    argument: Box::new(arg),
                })
            });
            after_expression(exp, rest)
        }
        // Field access: exp.field
        [(Token::Dot, _), (Token::Name(label), _), rest @ ..] => {
            let select = node(Expr::Select {
                label: label.clone(),
            });
            let exp = node(Expr::Apply {
                func: Box::new(select),
                argument: Box::new(exp),
            });
            after_expression(exp, rest)
        }
        _ => Ok((exp, rest)),
    }
}

fn do_args<'a>(tokens: Tokens<'a>, mut acc: Vec<Node>) -> PResult<'a, Vec<Node>> {
    match tokens {
        [(Token::RightParen, _), rest @ ..] => Ok((acc, rest)),
        [(Token::Comma, _), rest @ ..] => {
            let (arg, rest) = expression(rest)?;
            acc.push(arg);
            do_args(rest, acc)
        }
        _ => Err(fail(tokens)),
    }
}

// --- Lists ---

fn do_list<'a>(tokens: Tokens<'a>, mut acc: Vec<Node>) -> PResult<'a, Node> {
    match tokens {
        [(Token::RightSquare, _), rest @ ..] => {
            Ok((build_list(acc, node(Expr::Tail)), rest))
        }
        _ => {
            let (item, rest) = expression(tokens)?;
            acc.push(item);
            match rest {
                [(Token::Comma, _), (Token::DotDot, _), rest @ ..] => {
                    let (tail, rest) = expression(rest)?;
                    let ((tok, pos), rest) = pop(rest)?;
                    match tok {
                        Token::RightSquare => Ok((build_list(acc, tail), rest)),
                        _ => Err(ParseError::UnexpectedToken(tok.clone(), pos)),
                    }
                }
                [(Token::Comma, _), rest @ ..] => do_list(rest, acc),
                [(Token::RightSquare, _), rest @ ..] => {
                    Ok((build_list(acc, node(Expr::Tail)), rest))
                }
                _ => Err(fail(rest)),
            }
        }
    }
}

fn build_list(items: Vec<Node>, tail: Node) -> Node {
    items.into_iter().rev().fold(tail, |acc, item| {
        node(Expr::Apply {
            func: Box::new(node(Expr::Apply {
                func: Box::new(node(Expr::Cons)),
                argument: Box::new(item),
            })),
            argument: Box::new(acc),
        })
    })
}

// --- Records ---

struct RecordField {
    label: String,
    value: Node,
}

fn do_record<'a>(tokens: Tokens<'a>, mut acc: Vec<RecordField>) -> PResult<'a, Node> {
    let ((tok, _pos), rest) = pop(tokens)?;
    match tok {
        Token::RightBrace => Ok((node(Expr::Empty), rest)),
        Token::Name(label) => {
            let ((next_tok, _next_pos), rest2) = pop(rest)?;
            match next_tok {
                Token::Colon => {
                    let (value, rest2) = expression(rest2)?;
                    acc.push(RecordField {
                        label: label.clone(),
                        value,
                    });
                    match rest2 {
                        [(Token::Comma, _), rest2 @ ..] => do_record(rest2, acc),
                        [(Token::RightBrace, _), rest2 @ ..] => {
                            Ok((build_record(acc, node(Expr::Empty)), rest2))
                        }
                        _ => Err(fail(rest2)),
                    }
                }
                Token::Comma => {
                    acc.push(RecordField {
                        label: label.clone(),
                        value: node(Expr::Variable {
                            label: label.clone(),
                        }),
                    });
                    do_record(rest2, acc)
                }
                Token::RightBrace => {
                    acc.push(RecordField {
                        label: label.clone(),
                        value: node(Expr::Variable {
                            label: label.clone(),
                        }),
                    });
                    Ok((build_record(acc, node(Expr::Empty)), rest2))
                }
                _ => Err(ParseError::UnexpectedToken(next_tok.clone(), _next_pos)),
            }
        }
        Token::DotDot => {
            let (value, rest) = expression(rest)?;
            let ((tok, pos), rest) = pop(rest)?;
            match tok {
                Token::RightBrace => Ok((build_overwrite(acc, value), rest)),
                _ => Err(ParseError::UnexpectedToken(tok.clone(), pos)),
            }
        }
        _ => Err(ParseError::UnexpectedToken(tok.clone(), _pos)),
    }
}

fn build_record(fields: Vec<RecordField>, base: Node) -> Node {
    fields.into_iter().rev().fold(base, |acc, field| {
        node(Expr::Apply {
            func: Box::new(node(Expr::Apply {
                func: Box::new(node(Expr::Extend {
                    label: field.label,
                })),
                argument: Box::new(field.value),
            })),
            argument: Box::new(acc),
        })
    })
}

fn build_overwrite(fields: Vec<RecordField>, base: Node) -> Node {
    fields.into_iter().rev().fold(base, |acc, field| {
        node(Expr::Apply {
            func: Box::new(node(Expr::Apply {
                func: Box::new(node(Expr::Overwrite {
                    label: field.label,
                })),
                argument: Box::new(field.value),
            })),
            argument: Box::new(acc),
        })
    })
}

// --- Match/Case ---

fn clauses(tokens: Tokens) -> PResult<Node> {
    let (clauses, tail, rest) = do_clauses(tokens, Vec::new())?;
    // Clauses accumulated in order; fold from last to first (matching Gleam's reversed list + fold)
    let exp = clauses
        .into_iter()
        .rev()
        .fold(tail, |exp, (label, branch)| {
            let case_node = node(Expr::Case { label });
            let inner = node(Expr::Apply {
                func: Box::new(case_node),
                argument: Box::new(branch),
            });
            node(Expr::Apply {
                func: Box::new(inner),
                argument: Box::new(exp),
            })
        });
    Ok((exp, rest))
}

type ClausesResult<'a> = Result<(Vec<(String, Node)>, Node, Tokens<'a>), ParseError>;

fn do_clauses(tokens: Tokens, mut acc: Vec<(String, Node)>) -> ClausesResult {
    let ((tok, _pos), rest) = pop(tokens)?;
    match tok {
        Token::RightBrace => Ok((acc, node(Expr::NoCases), rest)),
        Token::Uppername(label) => {
            let (branch, rest) = expression(rest)?;
            acc.push((label.clone(), branch));
            do_clauses(rest, acc)
        }
        Token::Bar => {
            let (otherwise, rest) = expression(rest)?;
            match rest {
                [(Token::RightBrace, _), rest @ ..] => Ok((acc, otherwise, rest)),
                _ => Err(fail(rest)),
            }
        }
        _ => Err(ParseError::UnexpectedToken(tok.clone(), _pos)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer;
    use crate::token::{drop_comments, drop_whitespace};

    fn parse(source: &str) -> Result<Node, ParseError> {
        let tokens = lexer::lex(source);
        let tokens = drop_whitespace(tokens);
        let tokens = drop_comments(tokens);
        let (node, remaining) = expression(&tokens)?;
        if !remaining.is_empty() {
            return Err(fail(remaining));
        }
        Ok(node)
    }

    fn parse_block(source: &str) -> Result<Node, ParseError> {
        let tokens = lexer::lex(source);
        let tokens = drop_whitespace(tokens);
        let tokens = drop_comments(tokens);
        let (node, _remaining) = block(&tokens)?;
        Ok(node)
    }

    // Helpers to build expected IR nodes
    fn var(s: &str) -> Node {
        node(Expr::Variable {
            label: s.to_string(),
        })
    }
    fn int(v: i64) -> Node {
        node(Expr::Integer { value: v })
    }
    fn str_lit(s: &str) -> Node {
        node(Expr::String {
            value: s.to_string(),
        })
    }
    fn tag(s: &str) -> Node {
        node(Expr::Tag {
            label: s.to_string(),
        })
    }
    fn lam(label: &str, body: Node) -> Node {
        node(Expr::Lambda {
            label: label.to_string(),
            body: Box::new(body),
        })
    }
    fn app(func: Node, arg: Node) -> Node {
        node(Expr::Apply {
            func: Box::new(func),
            argument: Box::new(arg),
        })
    }
    fn let_bind(label: &str, def: Node, body: Node) -> Node {
        node(Expr::Let {
            label: label.to_string(),
            definition: Box::new(def),
            body: Box::new(body),
        })
    }
    fn select(label: &str) -> Node {
        node(Expr::Select {
            label: label.to_string(),
        })
    }
    fn extend(label: &str) -> Node {
        node(Expr::Extend {
            label: label.to_string(),
        })
    }
    fn overwrite(label: &str) -> Node {
        node(Expr::Overwrite {
            label: label.to_string(),
        })
    }
    fn case_node(label: &str) -> Node {
        node(Expr::Case {
            label: label.to_string(),
        })
    }

    // --- Atom tests ---

    #[test]
    fn test_variable() {
        assert_eq!(parse("x"), Ok(var("x")));
    }

    #[test]
    fn test_integer() {
        assert_eq!(parse("12"), Ok(int(12)));
    }

    #[test]
    fn test_negative_integer() {
        assert_eq!(parse("-100"), Ok(int(-100)));
    }

    #[test]
    fn test_string() {
        assert_eq!(parse("\"hello\""), Ok(str_lit("hello")));
    }

    #[test]
    fn test_string_escape() {
        assert_eq!(parse("\"\\\"\""), Ok(str_lit("\"")));
    }

    #[test]
    fn test_tag() {
        assert_eq!(parse("Ok"), Ok(tag("Ok")));
    }

    #[test]
    fn test_builtin() {
        assert_eq!(
            parse("!int_add"),
            Ok(node(Expr::Builtin {
                identifier: "int_add".to_string()
            }))
        );
    }

    #[test]
    fn test_perform() {
        assert_eq!(
            parse("perform Log"),
            Ok(node(Expr::Perform {
                label: "Log".to_string()
            }))
        );
    }

    #[test]
    fn test_handle() {
        assert_eq!(
            parse("handle Log"),
            Ok(node(Expr::Handle {
                label: "Log".to_string()
            }))
        );
    }

    #[test]
    fn test_reference() {
        assert_eq!(
            parse("#somecid"),
            Ok(node(Expr::Reference {
                identifier: "somecid".to_string()
            }))
        );
    }

    #[test]
    fn test_named_reference() {
        assert_eq!(
            parse("@std"),
            Ok(node(Expr::Release {
                package: "std".to_string(),
                release: 0,
                identifier: String::new(),
            }))
        );
    }

    // --- Lambda tests ---

    #[test]
    fn test_single_lambda() {
        assert_eq!(parse("(x) -> { 5 }"), Ok(lam("x", int(5))));
    }

    #[test]
    fn test_multi_param_lambda() {
        assert_eq!(
            parse("(x, y) -> { 5 }"),
            Ok(lam("x", lam("y", int(5))))
        );
    }

    #[test]
    fn test_destructuring_lambda() {
        // ({x: a, y: b}) -> { 5 }
        let expected = lam(
            "$",
            let_bind(
                "a",
                app(select("x"), var("$")),
                let_bind("b", app(select("y"), var("$")), int(5)),
            ),
        );
        assert_eq!(parse("({x: a, y: b}) -> { 5 }"), Ok(expected));
    }

    // --- Application tests ---

    #[test]
    fn test_apply() {
        assert_eq!(parse("a(1)"), Ok(app(var("a"), int(1))));
    }

    #[test]
    fn test_chained_apply() {
        assert_eq!(
            parse("a(10)(20)"),
            Ok(app(app(var("a"), int(10)), int(20)))
        );
    }

    #[test]
    fn test_nested_apply() {
        assert_eq!(
            parse("x(y(3))"),
            Ok(app(var("x"), app(var("y"), int(3))))
        );
    }

    #[test]
    fn test_multi_arg_apply() {
        assert_eq!(
            parse("a(x, y)"),
            Ok(app(app(var("a"), var("x")), var("y")))
        );
    }

    // --- Let tests ---

    #[test]
    fn test_let_simple() {
        assert_eq!(
            parse("let x = 5\n   x"),
            Ok(let_bind("x", int(5), var("x")))
        );
    }

    #[test]
    fn test_let_nested() {
        assert_eq!(
            parse("let x = 5\n   let y = 1\n   x"),
            Ok(let_bind("x", int(5), let_bind("y", int(1), var("x"))))
        );
    }

    #[test]
    fn test_let_destructure() {
        // let {x: a, y: _} = rec  a
        let expected = let_bind(
            "$",
            var("rec"),
            let_bind(
                "a",
                app(select("x"), var("$")),
                let_bind("_", app(select("y"), var("$")), var("a")),
            ),
        );
        assert_eq!(
            parse("let {x: a, y: _} = rec\n   a"),
            Ok(expected)
        );
    }

    #[test]
    fn test_let_destructure_shorthand() {
        // let {x, y} = rec  a
        let expected = let_bind(
            "$",
            var("rec"),
            let_bind(
                "x",
                app(select("x"), var("$")),
                let_bind("y", app(select("y"), var("$")), var("a")),
            ),
        );
        assert_eq!(
            parse("let {x, y} = rec\n   a"),
            Ok(expected)
        );
    }

    #[test]
    fn test_let_empty_destructure() {
        // let {} = rec  a
        let expected = let_bind("$", var("rec"), var("a"));
        assert_eq!(
            parse("let {} = rec\n   a"),
            Ok(expected)
        );
    }

    // --- Field access tests ---

    #[test]
    fn test_field_access() {
        assert_eq!(parse("a.foo"), Ok(app(select("foo"), var("a"))));
    }

    #[test]
    fn test_field_access_chained() {
        // b(x).foo
        assert_eq!(
            parse("b(x).foo"),
            Ok(app(select("foo"), app(var("b"), var("x"))))
        );
    }

    #[test]
    fn test_field_access_then_call() {
        // a.foo(2)
        assert_eq!(
            parse("a.foo(2)"),
            Ok(app(app(select("foo"), var("a")), int(2)))
        );
    }

    // --- List tests ---

    #[test]
    fn test_empty_list() {
        assert_eq!(parse("[]"), Ok(node(Expr::Tail)));
    }

    #[test]
    fn test_list() {
        // [1, 2]
        let expected = app(
            app(node(Expr::Cons), int(1)),
            app(app(node(Expr::Cons), int(2)), node(Expr::Tail)),
        );
        assert_eq!(parse("[1, 2]"), Ok(expected));
    }

    #[test]
    fn test_list_spread() {
        // [1, ..x]
        let expected = app(app(node(Expr::Cons), int(1)), var("x"));
        assert_eq!(parse("[1, ..x]"), Ok(expected));
    }

    // --- Record tests ---

    #[test]
    fn test_empty_record() {
        assert_eq!(parse("{}"), Ok(node(Expr::Empty)));
    }

    #[test]
    fn test_record() {
        // {a: 5, b: {}}
        let expected = app(
            app(extend("a"), int(5)),
            app(app(extend("b"), node(Expr::Empty)), node(Expr::Empty)),
        );
        assert_eq!(parse("{a: 5, b: {}}"), Ok(expected));
    }

    #[test]
    fn test_record_shorthand() {
        // {a, b}
        let expected = app(
            app(extend("a"), var("a")),
            app(app(extend("b"), var("b")), node(Expr::Empty)),
        );
        assert_eq!(parse("{a, b}"), Ok(expected));
    }

    #[test]
    fn test_overwrite() {
        // {a: 5, ..x}
        let expected = app(app(overwrite("a"), int(5)), var("x"));
        assert_eq!(parse("{a: 5, ..x}"), Ok(expected));
    }

    #[test]
    fn test_identity_spread() {
        // {..x}
        assert_eq!(parse("{..x}"), Ok(var("x")));
    }

    #[test]
    fn test_overwrite_shorthand() {
        // {a, ..x}
        let expected = app(app(overwrite("a"), var("a")), var("x"));
        assert_eq!(parse("{a, ..x}"), Ok(expected));
    }

    // --- Match tests ---

    #[test]
    fn test_match_empty() {
        assert_eq!(parse("match { }"), Ok(node(Expr::NoCases)));
    }

    #[test]
    fn test_match_with_subject_empty() {
        assert_eq!(
            parse("match x { }"),
            Ok(app(node(Expr::NoCases), var("x")))
        );
    }

    #[test]
    fn test_match_branches() {
        // match { Ok x Error(y) -> { y } }
        let expected = app(
            app(case_node("Ok"), var("x")),
            app(
                app(case_node("Error"), lam("y", var("y"))),
                node(Expr::NoCases),
            ),
        );
        assert_eq!(
            parse("match {\n      Ok x\n      Error(y) -> { y }\n    }"),
            Ok(expected)
        );
    }

    #[test]
    fn test_open_match() {
        // match Ok(2) { Ok(a) -> { a } | (x) -> { 0 } }
        let expected = app(
            app(
                app(case_node("Ok"), lam("a", var("a"))),
                lam("x", int(0)),
            ),
            app(tag("Ok"), int(2)),
        );
        assert_eq!(
            parse("match Ok(2) {\n    Ok(a) -> { a }\n    | (x) -> { 0 }\n  }"),
            Ok(expected)
        );
    }

    // --- Tagged application ---

    #[test]
    fn test_tagged_apply() {
        assert_eq!(parse("Ok(2)"), Ok(app(tag("Ok"), int(2))));
    }

    // --- Perform with application ---

    #[test]
    fn test_perform_apply() {
        assert_eq!(
            parse("perform Log(\"stop\")"),
            Ok(app(
                node(Expr::Perform {
                    label: "Log".to_string()
                }),
                str_lit("stop")
            ))
        );
    }

    // --- Comment test ---

    #[test]
    fn test_comment_ignored() {
        assert_eq!(
            parse("// let x = 5\n   let y = 1\n   y"),
            Ok(let_bind("y", int(1), var("y")))
        );
    }

    // --- Block mode ---

    #[test]
    fn test_block_let_no_body() {
        assert_eq!(
            parse_block("let x = 5"),
            Ok(let_bind("x", int(5), node(Expr::Vacant)))
        );
    }

    #[test]
    fn test_block_let_with_body() {
        assert_eq!(
            parse_block("let x = 5\nx"),
            Ok(let_bind("x", int(5), var("x")))
        );
    }

    // --- Error tests ---

    #[test]
    fn test_unexpected_end() {
        assert_eq!(parse(""), Err(ParseError::UnexpectedEnd));
    }

    #[test]
    fn test_unexpected_token() {
        assert!(matches!(parse(")"), Err(ParseError::UnexpectedToken(_, _))));
    }
}
