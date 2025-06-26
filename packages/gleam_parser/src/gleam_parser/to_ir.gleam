import eyg/ir/tree as ir
import gleam/float
import gleam/int
import gleam/list
import gleam_parser/ast
import gleam_parser/token

// Convert our AST to EYG IR format
pub fn to_annotated(
  expr: ast.Expr,
  rev: List(Int),
) -> #(ir.Expression(List(Int)), List(Int)) {
  case expr {
    // Basic expressions
    ast.Variable(name, _) -> #(ir.Variable(name), rev)

    ast.Literal(value, _) -> {
      case value {
        ast.StringValue(val) -> #(ir.String(val), rev)
        ast.NumberValue(val) -> {
          // Convert float to int if it's a whole number, otherwise keep as string representation
          case int.to_float(float.truncate(val)) == val {
            True -> #(ir.Integer(float.truncate(val)), rev)
            False -> {
              // For non-integer numbers, we might need to handle differently
              // For now, convert to integer (this might need adjustment)
              #(ir.Integer(float.truncate(val)), rev)
            }
          }
        }
        ast.BoolValue(True) -> {
          // True is represented as Tag("True") applied to Empty
          #(ir.Apply(#(ir.Tag("True"), rev), #(ir.Empty, rev)), rev)
        }
        ast.BoolValue(False) -> {
          // False is represented as Tag("False") applied to Empty  
          #(ir.Apply(#(ir.Tag("False"), rev), #(ir.Empty, rev)), rev)
        }
        ast.NilValue -> #(ir.Empty, rev)
        ast.BinaryValue(val) -> #(ir.Binary(val), rev)
        _ -> #(ir.Vacant, rev)
        // Fallback for other value types
      }
    }

    // Binary operations
    ast.Binary(left, operator, right, _) -> {
      let left_ir = to_annotated(left, [0, ..rev])
      let right_ir = to_annotated(right, [1, ..rev])

      // Convert operator token to builtin function name
      let builtin_name = case operator {
        token.Plus -> "int_add"
        token.Minus -> "int_subtract"
        token.Star -> "int_multiply"
        token.Slash -> "int_divide"
        token.EqualEqual -> "int_equal"
        token.BangEqual -> "int_not_equal"
        token.Less -> "int_less_than"
        token.LessEqual -> "int_less_equal"
        token.Greater -> "int_greater_than"
        token.GreaterEqual -> "int_greater_equal"
        _ -> "unknown_op"
      }

      #(
        ir.Apply(
          #(ir.Apply(#(ir.Builtin(builtin_name), rev), left_ir), rev),
          right_ir,
        ),
        rev,
      )
    }

    // Unary operations
    ast.Unary(operator, right, _) -> {
      let right_ir = to_annotated(right, [0, ..rev])

      let builtin_name = case operator {
        token.Minus -> "int_negate"
        token.Bang -> "bool_not"
        _ -> "unknown_unary_op"
      }

      #(ir.Apply(#(ir.Builtin(builtin_name), rev), right_ir), rev)
    }

    // Grouping (just return the inner expression)
    ast.Grouping(expression, _) -> to_annotated(expression, rev)

    // Function calls
    ast.Call(callee, arguments, _) -> {
      let callee_ir = to_annotated(callee, [0, ..rev])

      // Apply arguments left to right
      list.index_fold(arguments, callee_ir, fn(acc, arg, i) {
        let arg_ir = to_annotated(arg, [i + 1, ..rev])
        #(ir.Apply(acc, arg_ir), rev)
      })
    }

    // Lambda expressions
    ast.Lambda(parameters, body, _) -> {
      let body_ir = to_annotated(body, [list.length(parameters), ..rev])

      // Create nested lambdas for multiple parameters
      list.fold_right(parameters, body_ir, fn(acc, param) {
        #(ir.Lambda(param, acc), rev)
      })
    }

    // Builtin functions
    ast.Builtin(name, _) -> #(ir.Builtin(name), rev)

    // Records
    ast.Record(fields, _) -> {
      let len = list.length(fields) * 2
      let empty_record = #(ir.Empty, rev)

      // Build record by extending empty record with each field
      let #(_, result) =
        list.fold_right(fields, #(len, empty_record), fn(acc, field) {
          let #(i, acc_ir) = acc
          let i = i - 2
          let field_value = to_annotated(field.value, [i + 1, ..rev])
          let extended = #(
            ir.Apply(
              #(
                ir.Apply(#(ir.Extend(field.name), [i, ..rev]), field_value),
                rev,
              ),
              acc_ir,
            ),
            rev,
          )
          #(i, extended)
        })

      result
    }

    // Empty record
    ast.EmptyRecord(_) -> #(ir.Empty, rev)

    // Record access
    ast.Access(object, name, _) -> {
      let object_ir = to_annotated(object, [1, ..rev])
      #(ir.Apply(#(ir.Select(name), [0, ..rev]), object_ir), rev)
    }

    // Lists
    ast.List(elements, _) -> {
      let len = list.length(elements)
      let tail_ir = #(ir.Tail, [len, ..rev])

      // Build list by consing elements onto tail
      let #(_, result) =
        list.fold_right(elements, #(len, tail_ir), fn(acc, element) {
          let #(i, acc_ir) = acc
          let i = i - 1
          let element_ir = to_annotated(element, [i, ..rev])
          let consed = #(
            ir.Apply(#(ir.Apply(#(ir.Cons, rev), element_ir), rev), acc_ir),
            rev,
          )
          #(i, consed)
        })

      result
    }

    // List spread (for now, just convert the expression)
    ast.Spread(expression, _) -> to_annotated(expression, rev)

    // Union constructors
    ast.Union(constructor, value, _) -> {
      let value_ir = to_annotated(value, [1, ..rev])
      #(ir.Apply(#(ir.Tag(constructor), [0, ..rev]), value_ir), rev)
    }

    // Effects
    ast.Perform(effect, arguments, _) -> {
      case arguments {
        [] -> #(ir.Perform(effect), rev)
        [arg] -> {
          let arg_ir = to_annotated(arg, [1, ..rev])
          #(ir.Apply(#(ir.Perform(effect), [0, ..rev]), arg_ir), rev)
        }
        _ -> {
          // Multiple arguments - create a record/tuple
          let args_record =
            ast.Record(
              list.index_map(arguments, fn(arg, i) {
                ast.RecordField(int.to_string(i), arg)
              }),
              1,
            )
          let args_ir = to_annotated(args_record, [1, ..rev])
          #(ir.Apply(#(ir.Perform(effect), [0, ..rev]), args_ir), rev)
        }
      }
    }

    // Handle expressions
    ast.Handle(effect, handler, fallback, _) -> {
      let handler_ir = to_annotated(handler, [1, ..rev])
      let fallback_ir = to_annotated(fallback, [2, ..rev])

      // Handle is represented as Apply(Apply(Handle(effect), handler), fallback)
      #(
        ir.Apply(
          #(ir.Apply(#(ir.Handle(effect), [0, ..rev]), handler_ir), rev),
          fallback_ir,
        ),
        rev,
      )
    }

    // Let bindings (variable assignments)
    ast.Var(pattern, value, body, _) -> {
      case pattern {
        ast.Variable(name, _) -> {
          let value_ir = to_annotated(value, [1, ..rev])
          let body_ir = to_annotated(body, [2, ..rev])
          #(ir.Let(name, value_ir, body_ir), rev)
        }
        ast.Destructure(fields, _) -> {
          // For destructuring, we need to create a series of let bindings
          // that extract each field from the value
          let value_ir = to_annotated(value, [1, ..rev])

          // Create let bindings for each field
          let body_ir = to_annotated(body, [2 + list.length(fields), ..rev])

          list.fold_right(fields, body_ir, fn(acc, field) {
            let select_ir = #(
              ir.Apply(#(ir.Select(field.name), rev), #(
                ir.Variable("$destructure"),
                rev,
              )),
              rev,
            )
            // Extract variable name from the field value expression
            let var_name = case field.value {
              ast.Variable(name, _) -> name
              _ -> "_unknown"
            }
            #(ir.Let(var_name, select_ir, acc), rev)
          })
          |> fn(destructure_body) {
            #(ir.Let("$destructure", value_ir, destructure_body), rev)
          }
        }
        _ -> {
          // Fallback for other pattern types
          let value_ir = to_annotated(value, [1, ..rev])
          let body_ir = to_annotated(body, [2, ..rev])
          #(ir.Let("_", value_ir, body_ir), rev)
        }
      }
    }

    // If statements
    ast.IfStatement(condition, then_branch, else_branch, _) -> {
      let condition_ir = to_annotated(condition, [0, ..rev])
      let then_ir = to_annotated(then_branch, [1, ..rev])
      let else_ir = to_annotated(else_branch, [2, ..rev])

      // If is represented as a match on the condition with True/False cases
      let true_case = #(
        ir.Apply(#(ir.Apply(#(ir.Case("True"), rev), then_ir), rev), #(
          ir.NoCases,
          rev,
        )),
        rev,
      )
      let false_case = #(
        ir.Apply(#(ir.Apply(#(ir.Case("False"), rev), else_ir), rev), true_case),
        rev,
      )

      #(ir.Apply(false_case, condition_ir), rev)
    }

    // Blocks
    ast.Block(statements, _) -> {
      case statements {
        [] -> #(ir.Empty, rev)
        [single] -> to_annotated(single, rev)
        _ -> {
          // Convert multiple statements to nested let bindings
          let len = list.length(statements)
          let last_stmt = case list.last(statements) {
            Ok(stmt) -> stmt
            Error(_) -> ast.EmptyRecord(1)
          }
          let last_ir = to_annotated(last_stmt, [len - 1, ..rev])

          let init_stmts = case list.take(statements, len - 1) {
            [] -> []
            stmts -> stmts
          }

          list.fold_right(
            list.index_map(init_stmts, fn(stmt, i) { #(stmt, i) }),
            last_ir,
            fn(acc, stmt_with_index) {
              let #(stmt, i) = stmt_with_index
              let stmt_ir = to_annotated(stmt, [i, ..rev])
              #(ir.Let("_" <> int.to_string(i), stmt_ir, acc), rev)
            },
          )
        }
      }
    }

    // Thunks (zero-argument lambdas)
    ast.Thunk(body, _) -> {
      let body_ir = to_annotated(body, [1, ..rev])
      #(ir.Lambda("_", body_ir), rev)
    }

    // Named references
    ast.NamedRef(module, index, _) -> {
      #(ir.Release(module, index, module), rev)
    }

    // Match expressions
    ast.Match(value, cases, _) -> {
      let value_ir = to_annotated(value, [0, ..rev])
      let len = list.length(cases)

      // Build the case expression from right to left
      let nocases = #(ir.NoCases, [len + 1, ..rev])

      let #(_, cases_ir) =
        list.fold_right(cases, #(len + 1, nocases), fn(acc, case_) {
          let #(i, acc_ir) = acc
          let i = i - 1

          // Extract pattern and body
          let pattern_constructor = case case_.pattern {
            ast.ConstructorPattern(constructor, _, _) -> constructor
            _ -> "Unknown"
          }

          let body_ir = to_annotated(case_.body, [0, i, ..rev])
          let case_ir = #(
            ir.Apply(
              #(ir.Apply(#(ir.Case(pattern_constructor), rev), body_ir), rev),
              acc_ir,
            ),
            rev,
          )
          #(i, case_ir)
        })

      #(ir.Apply(cases_ir, value_ir), rev)
    }

    // Constructor patterns (used in match expressions)
    ast.ConstructorPattern(constructor, value, _) -> {
      let value_ir = to_annotated(value, [1, ..rev])
      #(ir.Apply(#(ir.Tag(constructor), [0, ..rev]), value_ir), rev)
    }

    // Wildcard patterns
    ast.Wildcard(_) -> #(ir.Variable("_"), rev)

    // Destructure patterns (standalone)
    ast.Destructure(fields, _) -> {
      // This shouldn't appear standalone, but if it does, create a record
      let field_exprs =
        list.map(fields, fn(field) {
          let var_name = case field.value {
            ast.Variable(name, _) -> name
            _ -> "_unknown"
          }
          ast.RecordField(field.name, ast.Variable(var_name, 1))
        })
      to_annotated(ast.Record(field_exprs, 1), rev)
    }
  }
}

// Helper function to convert with default revision
pub fn to_ir(expr: ast.Expr) -> #(ir.Expression(List(Int)), List(Int)) {
  to_annotated(expr, [])
}
