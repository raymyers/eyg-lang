import gleam/list
import gleam/option.{None, Some}
import eyg/ast
import eyg/ast/expression as e
import eyg/ast/pattern as p
import eyg/typer

// Union is a set of variants a variant can be tag or tagged data
// The sugar is for Tag or Tag Constructor
pub type Sugar(n) {
  Tag(name: String)
}

pub fn tag(name) {
  ast.function(
    p.Row([#(name, "then")]),
    ast.call(ast.variable("then"), ast.tuple_([])),
  )
}

// TupleVariant(
//   label: String,
//   parameters: List(String),
//   then: e.Expression(typer.Metadata, e.Expression(typer.Metadata, Nil)),
// )
// by convention change the highest level key i.e. name in pattern follows through to name in calls.
pub fn match(tree) {
  case tree {
    e.Function(
      p.Row([#(name, "then")]),
      #(_, e.Call(#(_, e.Variable("then")), #(_, e.Tuple([])))),
    ) -> Ok(Tag(name))
    //   e.Let(
    //     p.Variable(n1),
    //     #(
    //       _,
    //       e.Function(
    //         p.Tuple(elements),
    //         #(
    //           _,
    //           e.Function(
    //             p.Row([#(n2, "then")]),
    //             #(_, e.Call(#(_, e.Variable("then")), #(_, e.Tuple(e_call)))),
    //           ),
    //         ),
    //       ),
    //     ),
    //     then,
    //   ) if n1 == n2 -> {
    //     try parameters = all_elements_named(elements)
    //     try calls = all_elements_variables(e_call)
    //     case parameters == calls {
    //       True -> Ok(TupleVariant(n1, parameters, then))
    //       False -> Error(Nil)
    //     }
    //   }
    _ -> Error(Nil)
  }
}

fn all_elements_named(elements) {
  list.try_map(
    elements,
    fn(e) {
      case e {
        Some(v) -> Ok(v)
        None -> Error(Nil)
      }
    },
  )
}

fn all_elements_variables(elements) {
  list.try_map(
    elements,
    fn(e) {
      case e {
        #(_, e.Variable(x)) -> Ok(x)
        _ -> Error(Nil)
      }
    },
  )
}
