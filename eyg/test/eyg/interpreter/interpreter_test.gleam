import gleam/io
import gleam/dynamic
import gleam/list
import gleam/map
import gleam/option.{None}
import gleam/string
import eyg/analysis
import eyg/ast/expression as e
import eyg/ast/pattern as p
import eyg/interpreter/interpreter as r
import eyg/interpreter/tree_walk
import eyg/interpreter/tail_call
import eyg/interpreter/stepwise
import eyg/typer
import eyg/typer/monotype as t
import eyg/codegen/javascript

pub fn tuples_test() {
    let empty = map.new()
    let source = e.tuple_([e.tuple_([]), e.binary("hello")])

    assert Ok(r.Tuple([r.Tuple([]), r.Binary("hello")])) = tree_walk.eval(source, empty)
    assert Ok(r.Tuple([r.Tuple([]), r.Binary("hello")])) = tail_call.eval(source, empty)
    // I wonder if handling Ok/Error makes interpreter slower
    assert Ok(r.Tuple([r.Tuple([]), r.Binary("hello")])) = stepwise.eval(source, empty)
}

pub fn tuple_patterns_test() {
    let empty = map.new()
    let source = e.let_(
        p.Tuple(["x", "y"]), 
        e.tuple_([e.binary("foo"), e.binary("bar")]), 
        e.tuple_([e.variable("y"), e.variable("x")])
        )

    assert Ok(r.Tuple([r.Binary("bar"), r.Binary("foo")])) = tree_walk.eval(source, empty)
    assert Ok(r.Tuple([r.Binary("bar"), r.Binary("foo")])) = tail_call.eval(source, empty)
    assert Ok(r.Tuple([r.Binary("bar"), r.Binary("foo")])) = stepwise.eval(source, empty)
}

pub fn incorrect_tuple_size_match_test() {
    let empty = map.new()
    let source = e.let_(
        p.Tuple(["x", "y"]), 
        e.tuple_([]), 
        e.tuple_([])
        )

    assert Error(_) = tree_walk.eval(source, empty)
    assert Error(_) = tail_call.eval(source, empty)
    assert Error(_) = stepwise.eval(source, empty)
}

pub fn not_a_tuple_match_test() {
    let empty = map.new()
    let source = e.let_(
        p.Tuple(["x", "y"]), 
        e.binary(""), 
        e.binary("")
        )

    assert Error(_) = tree_walk.eval(source, empty)
    assert Error(_) = tail_call.eval(source, empty)
    assert Error(_) = stepwise.eval(source, empty)
}


pub fn record_access_test() {
    let empty = map.new()
    let source = e.access(e.record([#("foo", e.tuple_([]))]), "foo")

    assert Ok(r.Tuple([])) = tree_walk.eval(source, empty) 
    assert Ok(r.Tuple([])) = tail_call.eval(source, empty) 
    assert Ok(r.Tuple([])) = stepwise.eval(source, empty)
}

pub fn record_missing_key_test() {
    let empty = map.new()
    let source = e.access(e.record([#("foo", e.tuple_([]))]), "bar")

    assert Error(_) = tree_walk.eval(source, empty) 
    assert Error(_) = tail_call.eval(source, empty) 
    assert Error(_) = stepwise.eval(source, empty)
}

pub fn invalid_access_test() {
    let empty = map.new()
    let source = e.access(e.binary("not a record"), "bar")

    assert Error(_) = tree_walk.eval(source, empty) 
    assert Error(_) = tail_call.eval(source, empty) 
    assert Error(_) = stepwise.eval(source, empty)
}


pub fn variables_test() {
    let empty = map.new()
    let source = e.let_(p.Variable("a"), e.tuple_([]), e.variable("a"))

    assert Ok(r.Tuple([])) = tree_walk.eval(source, empty)
    assert Ok(r.Tuple([])) = tail_call.eval(source, empty)
    assert Ok(r.Tuple([])) = stepwise.eval(source, empty)
}

pub fn unknown_variable_test() {
    let empty = map.new()
    let source = e.variable("a")

    assert Error(_) = tree_walk.eval(source, empty)
    assert Error(_) = tail_call.eval(source, empty)
    assert Error(_) = stepwise.eval(source, empty)
}

pub fn functions_test() {
    let empty = map.new()
    let source = e.call(e.function(p.Variable("x"), e.variable("x")), e.tuple_([]))

    assert Ok(r.Tuple([])) = tree_walk.eval(source, empty) 
    assert Ok(r.Tuple([])) = tail_call.eval(source, empty) 
    assert Ok(r.Tuple([])) = stepwise.eval(source, empty)


    let source = e.call(e.function(p.Tuple([]), e.binary("inner")), e.tuple_([]))
    assert Ok(r.Binary("inner")) = tree_walk.eval(source, empty) 
    assert Ok(r.Binary("inner")) = tail_call.eval(source, empty) 
    assert Ok(r.Binary("inner")) = stepwise.eval(source, empty)
}

pub fn unions_test() {
    let empty = map.new()
    let source = e.case_(e.tagged("True", e.tuple_([])), [
        #("False", p.Tuple([]), e.binary("no")),
        #("True", p.Tuple([]), e.binary("yes"))
    ])
    assert Ok(r.Binary("yes")) = tree_walk.eval(source, empty) 
    assert Ok(r.Binary("yes")) = tail_call.eval(source, empty) 
    assert Ok(r.Binary("yes")) = stepwise.eval(source, empty)


    let empty = map.new()
    let source = e.case_(e.tagged("Some", e.binary("foo")), [
        #("Some", p.Variable("a"), e.variable("a")),
        #("None", p.Tuple([]), e.binary("BAD"))
    ])
    assert Ok(r.Binary("foo")) = tree_walk.eval(source, empty) 
    assert Ok(r.Binary("foo")) = tail_call.eval(source, empty) 
    assert Ok(r.Binary("foo")) = stepwise.eval(source, empty)
}

pub fn unhandled_case_test()  {
    let empty = map.new()
    let source = e.case_(e.tagged("True", e.tuple_([])), [
        #("False", p.Tuple([]), e.binary("no")),
    ])
    assert Error(_) = tree_walk.eval(source, empty) 
    assert Error(_) = tail_call.eval(source, empty)
    assert Error(_) = stepwise.eval(source, empty)
}

pub fn invalid_match_test()  {
    let empty = map.new()
    let source = e.case_(e.binary("not a union"), [
        #("False", p.Tuple([]), e.binary("no")),
    ])
    assert Error(_) = tree_walk.eval(source, empty) 
    assert Error(_) = tail_call.eval(source, empty)
    assert Error(_) = stepwise.eval(source, empty)
}

pub fn eval_hole_test() {
    let empty = map.new()
    let source = e.hole()

    assert Error(_) = tree_walk.eval(source, empty)
    assert Error(_) = tail_call.eval(source, empty)
    assert Error(_) = stepwise.eval(source, empty)
}

fn tail() { 
    r.Tagged("Nil", r.Tuple([]))
}

fn cons(h,t) {
     r.Tagged("Cons", r.Tuple([h, t]))

}

pub fn recursive_test() {
    let source = e.let_(
        p.Variable("move"),
        e.function(p.Tuple(["from", "to"]), 
            e.case_(e.variable("from"), [
                #("Nil", p.Tuple([]), e.variable("to")),
                #("Cons", p.Tuple(["item", "from"]), e.let_(
                    p.Variable("to"),
                    e.tagged("Cons", e.tuple_([e.variable("item"), e.variable("to")])),
                    e.call(e.variable("move"), e.tuple_([e.variable("from"), e.variable("to")]))
                ))
            ])
        ),
        e.call(e.variable("move"), e.variable("x"))
    )
    let empty = map.new()
    |> map.insert("x", r.Tuple([tail(), tail()]))
    assert Ok(r.Tagged("Nil", r.Tuple([]))) = tree_walk.eval(source, empty) 
    assert Ok(r.Tagged("Nil", r.Tuple([]))) = tail_call.eval(source, empty) 
    assert Ok(r.Tagged("Nil", r.Tuple([]))) = stepwise.eval(source, empty)


    let empty = map.new()
    |> map.insert("x", r.Tuple([cons(r.Binary("1"),cons(r.Binary("2"),tail())), tail()]))
    assert Ok(r.Tagged("Cons", r.Tuple([r.Binary("2"), r.Tagged("Cons", r.Tuple([r.Binary("1"), r.Tagged("Nil", r.Tuple([]))]))]))) = tree_walk.eval(source, empty) 
    assert Ok(r.Tagged("Cons", r.Tuple([r.Binary("2"), r.Tagged("Cons", r.Tuple([r.Binary("1"), r.Tagged("Nil", r.Tuple([]))]))]))) = tail_call.eval(source, empty) 
    assert Ok(r.Tagged("Cons", r.Tuple([r.Binary("2"), r.Tagged("Cons", r.Tuple([r.Binary("1"), r.Tagged("Nil", r.Tuple([]))]))]))) = stepwise.eval(source, empty)

}

pub fn builtin_test()  {
    let env = map.new()
    |> map.insert("string", r.Record([#("reverse", r.BuiltinFn(fn(object) {
        assert r.Binary(value) = object
        Ok(r.Binary(string.reverse(value)))
    }))]))
    let source = e.call(e.access(e.variable("string"), "reverse"), e.binary("hello"))

    assert Ok(r.Binary("olleh")) = tree_walk.eval(source, env) 
    assert Ok(r.Binary("olleh")) = tail_call.eval(source, env) 
    assert Ok(r.Binary("olleh")) = stepwise.eval(source, env)

}
