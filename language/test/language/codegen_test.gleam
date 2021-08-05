import language/codegen/javascript
import language/ast/builder.{
  binary, call, case_, clause, destructure, function, let_, rest, var,
}
import language/type_.{Data}
import language/ast
import language/scope
import language/ast/support.{with_equal}

fn compile(untyped, scope) {
  let Ok(#(type_, tree, typer)) = ast.infer(untyped, scope)
  javascript.render(#(type_, tree), False)
}

pub fn variable_assignment_test() {
  let untyped =
    let_("foo", binary("My First Value"), let_("foo", var("foo"), var("foo")))
  let js = compile(untyped, scope.new())
  let [l1, l2, l3] = js
  let "let foo$1 = \"My First Value\";" = l1
  let "let foo$2 = foo$1;" = l2
  let "foo$2" = l3
}

pub fn let_destructure_test() {
  let scope =
    scope.new()
    |> scope.newtype("User", [], [#("User", [Data("Binary", [])])])
  let untyped =
    destructure(
      "User",
      ["first_name"],
      call(var("User"), [binary("abc")]),
      var("first_name"),
    )
  let js = compile(untyped, scope)
  let [l1, l2] = js
  let "let [first_name$1, ] = User$1(\"abc\", );" = l1
  let "first_name$1" = l2
}

pub fn case_with_boolean_test() {
  let scope =
    scope.new()
    |> with_equal
  let untyped =
    function(
      ["bool"],
      case_(
        var("bool"),
        [clause("True", [], binary("hello")), rest("ping", binary("bye!"))],
      ),
    )
  let js = compile(untyped, scope)
  let [l1, l2, l3, l4, l5, l6, l7, l8, l9, l10] = js
  let "((bool$1, ) => {" = l1
  let "  return ((subject) => {" = l2
  let "  if (subject.type == \"True\") {" = l3
  let "    let [] = Object.values(subject)" = l4
  let "    return \"hello\";" = l5
  let "  } else {" = l6
  let "    let ping = subject;" = l7
  let "    return \"bye!\";" = l8
  let "  }})(bool$1);" = l9
  let "})" = l10
}

pub fn simple_function_call_test() {
  let scope =
    scope.new()
    |> with_equal
  let untyped = call(var("equal"), [binary("foo"), binary("bar")])
  let js = compile(untyped, scope)
  let [l1] = js
  let "equal$1(\"foo\", \"bar\", )" = l1
}

pub fn oneline_function_test() {
  let scope = scope.new()
  let untyped = let_("x", function(["x"], var("x")), var("x"))
  let js = compile(untyped, scope)
  let [l1, l2] = js
  let "let x$1 = ((x$1, ) => { return x$1; });" = l1
  let "x$1" = l2
}

pub fn call_oneline_function_test() {
  let scope = scope.new()
  let untyped = call(function(["x"], var("x")), [binary("hello")])
  let js = compile(untyped, scope)
  let [l1] = js
  let "((x$1, ) => { return x$1; })(\"hello\", )" = l1
}

pub fn multiline_function_test() {
  let scope =
    scope.new()
    |> with_equal
  let untyped =
    let_(
      "test",
      function(
        ["a", "b"],
        let_(
          "a",
          call(var("equal"), [var("a"), binary("blah")]),
          call(var("equal"), [var("b"), binary("other")]),
        ),
      ),
      var("test"),
    )
  let js = compile(untyped, scope)
  let [l1, l2, l3, l4, l5] = js
  let "let test$1 = ((a$1, b$1, ) => {" = l1
  let "  let a$2 = equal$1(a$1, \"blah\", );" = l2
  let "  return equal$1(b$1, \"other\", );" = l3
  let "});" = l4
}
