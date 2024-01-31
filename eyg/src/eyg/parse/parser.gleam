import gleam/int
import gleam/list
import gleam/result.{try}
import eygir/expression as e
import eyg/parse/token as t
import gleam/io

pub type Reason {
  UnexpectEnd
}

pub fn parse(tokens) {
  case expression(tokens) {
    Ok(#(e, [])) -> Ok(e)
    Ok(#(_, leftover)) -> {
      io.debug(leftover)
      panic
    }
    Error(reason) -> Error(reason)
  }
}

pub type Pattern {
  Assign(String)
  Destructure(List(#(String, String)))
}

fn one_pattern(tokens) {
  case tokens {
    [#(t.Name(label), _), ..rest] -> Ok(#(Assign(label), rest))
    [#(t.LeftBrace, _), ..rest] -> {
      use #(matches, rest) <- try(do_pattern(rest, []))
      Ok(#(Destructure(matches), rest))
    }
  }
}

pub fn expression(tokens) {
  use #(#(token, start), rest) <- try(pop(tokens))

  use #(exp, rest) <- try(case token {
    t.Name(label) -> Ok(#(e.Variable(label), rest))
    t.Let -> {
      use #(pattern, rest) <- try(one_pattern(rest))
      use rest <- try(case rest {
        [#(t.Equal, _), ..rest] -> Ok(rest)
      })
      use #(value, rest) <- try(expression(rest))
      use #(then, rest) <- try(expression(rest))
      let exp = case pattern {
        Assign(label) -> e.Let(label, value, then)
        Destructure(matches) ->
          e.Let(
            "$",
            value,
            list.fold(matches, then, fn(acc, pair) {
              let #(field, var) = pair
              e.Let(var, e.Apply(e.Select(field), e.Variable("$")), acc)
            }),
          )
      }
      Ok(#(exp, rest))
    }
    t.LeftParen -> {
      use #(pattern, rest) <- try(one_pattern(rest))
      use rest <- try(case rest {
        [#(t.RightParen, _), #(t.RightArrow, _), ..rest] -> Ok(rest)
      })
      use #(body, rest) <- try(expression(rest))
      let exp = case pattern {
        Assign(label) -> e.Lambda(label, body)
        Destructure(matches) ->
          e.Lambda(
            "$",
            list.fold(matches, body, fn(acc, pair) {
              let #(field, var) = pair
              e.Let(var, e.Apply(e.Select(field), e.Variable("$")), acc)
            }),
          )
      }
      Ok(#(exp, rest))
    }
    t.Integer(raw) -> {
      let assert Ok(value) = int.parse(raw)
      Ok(#(e.Integer(value), rest))
    }
    t.String(value) -> Ok(#(e.Str(value), rest))
    t.LeftSquare -> do_list(rest, [])
    t.LeftBrace -> do_record(rest, [])
    t.Uppername(label) -> Ok(#(e.Tag(label), rest))
    t.Match -> {
      case rest {
        [#(t.LeftBrace, _), ..rest] -> {
          clauses(rest)
        }
        _ -> {
          use #(subject, rest) <- try(expression(rest))
          case rest {
            [#(t.LeftBrace, _), ..rest] -> {
              use #(exp, rest) <- try(clauses(rest))
              Ok(#(e.Apply(exp, subject), rest))
            }
          }
        }
      }
    }
    t.Perform ->
      case rest {
        [#(t.Uppername(label), _), ..rest] -> Ok(#(e.Perform(label), rest))
      }
    t.Handle ->
      case rest {
        [#(t.Uppername(label), _), ..rest] -> Ok(#(e.Handle(label), rest))
      }
    t.Shallow ->
      case rest {
        [#(t.Uppername(label), _), ..rest] -> Ok(#(e.Shallow(label), rest))
      }
    _ -> {
      io.debug(token)
      todo as "unexpected token"
    }
  })
  after_expression(exp, rest)
}

fn do_pattern(tokens, acc) {
  case tokens {
    [#(t.RightBrace, _), ..rest] -> Ok(#(acc, rest))
    [#(t.Name(field), _), #(t.Colon, _), #(t.Name(var), _), ..rest] -> {
      let acc = [#(field, var), ..acc]
      case rest {
        [#(t.RightBrace, _), ..rest] -> Ok(#(acc, rest))
        [#(t.Comma, _), ..rest] -> do_pattern(rest, acc)
        _ -> {
          io.debug(rest)
          panic
        }
      }
    }
    [#(t.Name(field), _), ..rest] -> {
      let acc = [#(field, field), ..acc]
      case rest {
        [#(t.RightBrace, _), ..rest] -> Ok(#(acc, rest))
        [#(t.Comma, _), ..rest] -> do_pattern(rest, acc)
        _ -> {
          io.debug(rest)
          panic
        }
      }
    }
  }
}

fn after_expression(exp, rest) {
  case rest {
    [#(t.RightArrow, _), ..rest] -> {
      use #(body, rest) <- try(expression(rest))
      case exp {
        e.Variable(label) -> Ok(#(e.Lambda(label, body), rest))
      }
    }
    [#(t.LeftParen, _), ..rest] -> {
      use #(arg, rest) <- try(expression(rest))
      use #(args, rest) <- try(do_args(rest, [arg]))
      let args = list.reverse(args)
      let exp = list.fold(args, exp, e.Apply)
      after_expression(exp, rest)
    }
    [#(t.Dot, _), #(t.Name(label), _), ..rest] ->
      after_expression(e.Apply(e.Select(label), exp), rest)
    _ -> Ok(#(exp, rest))
  }
}

fn do_args(tokens, acc) {
  case tokens {
    [#(t.RightParen, _), ..rest] -> Ok(#(acc, rest))
    [#(t.Comma, _), ..rest] -> {
      use #(arg, rest) <- try(expression(rest))
      do_args(rest, [arg, ..acc])
    }
  }
}

// this supports trailing comma
fn do_list(tokens, acc) {
  // use #(t,rest)
  case tokens {
    [] -> Error(UnexpectEnd)
    [#(t.RightSquare, _), ..rest] -> Ok(#(e.do_list(acc, e.Tail), rest))
    _ -> {
      use #(item, rest) <- try(expression(tokens))
      let acc = [item, ..acc]
      case rest {
        [#(t.Comma, _), #(t.DotDot, _), ..rest] -> {
          use #(tail, rest) <- try(expression(rest))
          case rest {
            [#(t.RightSquare, _), ..rest] -> Ok(#(e.do_list(acc, tail), rest))
          }
        }
        [#(t.Comma, _), ..rest] -> do_list(rest, acc)

        [#(t.RightSquare, _), ..rest] -> Ok(#(e.do_list(acc, e.Tail), rest))
      }
    }
  }
}

fn do_record(rest, acc) {
  use #(#(token, _), rest) <- try(pop(rest))
  case token {
    t.RightBrace -> Ok(#(e.Empty, rest))
    t.Name(label) ->
      case rest {
        [#(t.Colon, _), ..rest] -> {
          use #(value, rest) <- try(expression(rest))
          let acc = [#(label, value), ..acc]

          // replace above with field function

          case rest {
            [#(t.Comma, _), ..rest] -> do_record(rest, acc)

            [#(t.RightBrace, _), ..rest] ->
              Ok(#(e.do_record(acc, e.Empty), rest))
            _ -> {
              io.debug(#("fo", rest))
              panic as "bad times"
            }
          }
        }
        [#(t.Comma, _), ..rest] -> {
          let acc = [#(label, e.Variable(label)), ..acc]
          do_record(rest, acc)
        }
        [#(t.RightBrace, _), ..rest] -> {
          let acc = [#(label, e.Variable(label)), ..acc]
          Ok(#(e.do_record(acc, e.Empty), rest))
        }
      }
    t.DotDot -> {
      use #(value, rest) <- try(expression(rest))
      use rest <- try(case rest {
        [#(t.RightBrace, _), ..rest] -> Ok(rest)
      })
      Ok(#(e.do_overwrite(acc, value), rest))
    }
  }
}

fn clauses(tokens) {
  use #(clauses, rest) <- try(do_clauses(tokens, []))
  let exp =
    list.fold(clauses, e.NoCases, fn(exp, clause) {
      let #(label, branch) = clause
      e.Apply(e.Apply(e.Case(label), branch), exp)
    })
  Ok(#(exp, rest))
}

fn do_clauses(tokens, acc) {
  case tokens {
    [#(t.RightBrace, _), ..rest] -> Ok(#(acc, rest))
    [#(t.Uppername(label), _), ..rest] -> {
      use #(branch, rest) <- try(expression(rest))
      let acc = [#(label, branch), ..acc]
      do_clauses(rest, acc)
    }
  }
}

fn pop(tokens) {
  case tokens {
    [t, ..rest] -> Ok(#(t, rest))
    [] -> Error(UnexpectEnd)
  }
}
