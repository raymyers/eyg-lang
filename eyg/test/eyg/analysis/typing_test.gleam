import gleam/io
import gleam/map
import gleam/option.{None, Some}
import gleam/set
import gleam/setx
import eyg/analysis/expression as e
import eyg/analysis/typ.{ftv} as t
import eyg/analysis/env
import eyg/analysis/infer.{infer}
// top level analysis
import eyg/analysis/scheme.{Scheme}
import eyg/analysis/unification.{resolve, resolve_effect, resolve_row}
import gleam/javascript
import gleeunit/should

pub fn free_type_variables_test() {
  ftv(t.Unbound(0))
  |> should.equal(setx.singleton(t.Term(0)))

  ftv(t.Binary)
  |> should.equal(set.new())

  ftv(t.Integer)
  |> should.equal(set.new())

  ftv(t.Fun(t.Integer, t.Closed, t.Integer))
  |> should.equal(set.new())

  ftv(t.Fun(t.Unbound(1), t.Closed, t.Unbound(1)))
  |> should.equal(setx.singleton(t.Term(1)))

  // rows
  ftv(t.Record(t.Closed))
  |> should.equal(set.new())

  ftv(t.Union(t.Closed))
  |> should.equal(set.new())

  let row = t.Extend("r", t.Unbound(1), t.Extend("s", t.Unbound(2), t.Open(3)))
  ftv(t.Record(row))
  |> should.equal(set.from_list([t.Term(1), t.Term(2), t.Row(3)]))

  // effects
  let eff = t.Extend("r", #(t.Unbound(1), t.Unbound(2)), t.Open(3))
  ftv(t.Fun(t.Integer, eff, t.Integer))
  |> should.equal(set.from_list([t.Term(1), t.Term(2), t.Effect(3)]))
}

// Primitive
pub fn binary_test() {
  let exp = e.Binary
  let env = env.empty()
  let typ = t.Binary
  let eff = t.Closed
  let ref = javascript.make_reference(0)

  let _ = infer(env, exp, typ, eff, ref)

  let typ = t.Unbound(1)
  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Binary = resolve(sub, typ)
}

pub fn integer_test() {
  let exp = e.Integer
  let env = env.empty()
  let typ = t.Integer
  let eff = t.Closed
  let ref = javascript.make_reference(0)

  let _ = infer(env, exp, typ, eff, ref)

  let typ = t.Unbound(1)
  let ref = javascript.make_reference(0)

  let sub = infer(env, exp, typ, eff, ref)
  assert t.Integer = resolve(sub, typ)
}

// Variables
pub fn variables_test() {
  let exp = e.Let("x", e.Binary, e.Variable("x"))
  let env = env.empty()
  let typ = t.Binary
  let eff = t.Closed
  let ref = javascript.make_reference(0)

  let _ = infer(env, exp, typ, eff, ref)

  let typ = t.Unbound(1)
  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Binary = resolve(sub, typ)
}

// let x = x is an error

// Functions
pub fn function_test() {
  let exp = e.Lambda("x", e.Binary)
  let env = env.empty()
  let typ = t.Fun(t.Integer, t.Closed, t.Binary)
  let eff = t.Closed

  let ref = javascript.make_reference(0)
  let _ = infer(env, exp, typ, eff, ref)

  let typ = t.Unbound(-1)
  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Fun(t.Unbound(_), t.Open(_), t.Binary) = resolve(sub, typ)
}

pub fn pure_function_test() {
  let exp = e.Lambda("x", e.Variable("x"))
  let env = env.empty()
  let typ = t.Unbound(-1)
  let eff = t.Closed

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Fun(t.Unbound(x), t.Open(2), t.Unbound(y)) = resolve(sub, typ)
  assert True = x == y
}

pub fn pure_function_call_test() {
  let func = e.Lambda("x", e.Variable("x"))
  let exp = e.Apply(func, e.Binary)
  let env = env.empty()
  let typ = t.Binary
  let eff = t.Closed

  let ref = javascript.make_reference(0)
  let _ = infer(env, exp, typ, eff, ref)

  let typ = t.Unbound(-1)
  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Binary = resolve(sub, typ)
}

// call generic could be a test row(a = id(Int) b = id(Int))

fn field(row: t.Row(a), label) {
  case row {
    t.Open(_) | t.Closed -> Error(Nil)
    t.Extend(l, t, _) if l == label -> Ok(t)
    t.Extend(_, _, tail) -> field(tail, label)
  }
}

// Records
pub fn record_creation_test() {
  let exp = e.Record([], option.None)
  let env = env.empty()
  let typ = t.Unbound(-1)
  let eff = t.Closed

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Record(row) = resolve(sub, typ)
  should.equal(row, t.Closed)

  let exp = e.Record([#("foo", e.Binary), #("bar", e.Integer)], option.None)
  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Record(row) = resolve(sub, typ)
  assert t.Extend(
    label: "bar",
    value: t.Integer,
    tail: t.Extend(label: "foo", value: t.Binary, tail: t.Closed),
  ) = row
}

pub fn record_update_test() {
  let exp = e.Record([], option.Some("x"))
  let env = env.empty()
  let x = Scheme([], t.Unbound(-2))
  let env = map.insert(env, "x", x)
  let typ = t.Unbound(-1)
  let eff = t.Closed

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Record(row) = resolve(sub, typ)
  assert t.Open(x) = row
  assert t.Record(row) = resolve(sub, t.Unbound(-2))
  assert t.Open(y) = row
  should.equal(x, y)

  let exp = e.Record([#("foo", e.Binary)], option.Some("x"))
  let env = env.empty()
  let mono =
    t.Record(t.Extend("foo", t.Binary, t.Extend("bar", t.Integer, t.Closed)))
  let x = Scheme([], mono)
  let env = map.insert(env, "x", x)
  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Record(row) = resolve(sub, typ)
  assert t.Extend(
    label: "foo",
    value: t.Binary,
    tail: t.Extend(label: "bar", value: t.Integer, tail: t.Closed),
  ) = row
}

// TODO update type
// pub fn record_update_type_test() {
//   let exp = e.Record([#("foo", e.Binary)], option.Some("x"))
//   let env = env.empty()
//   let mono =
//     t.Record(t.Extend("foo", t.Integer, t.Extend("bar", t.Integer, t.Closed)))
//   let x = Scheme([], mono)
//   let env = map.insert(env, "x", x)
//   let typ = t.Unbound(-1)
//   let eff = t.Closed

//   let ref = javascript.make_reference(0)
//   let sub = infer(env, exp, typ, eff, ref)
//   assert t.Record(row) = resolve(sub, typ)
//   assert t.Extend(
//     label: "foo",
//     value: t.Binary,
//     tail: t.Extend(label: "bar", value: t.Integer, tail: t.Closed),
//   ) = row
// }

pub fn select_test() {
  let exp = e.Select("foo")
  let env = env.empty()
  let typ = t.Unbound(-1)
  let eff = t.Closed

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Fun(t.Record(t.Extend(l, a, t.Open(_))), _eff, b) = resolve(sub, typ)
  should.equal(a, b)
  should.equal(l, "foo")

  let exp = e.Apply(exp, e.Variable("x"))
  let env = env.empty()
  let x = Scheme([], t.Record(t.Extend("foo", t.Binary, t.Closed)))
  let env = map.insert(env, "x", x)

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)

  assert t.Binary = resolve(sub, typ)
}

pub fn combine_select_test() {
  let exp =
    e.Let(
      "_",
      e.Apply(e.Select("foo"), e.Variable("x")),
      e.Apply(e.Select("bar"), e.Variable("x")),
    )
  let env = env.empty()
  let x = Scheme([], t.Unbound(-2))
  let env = map.insert(env, "x", x)
  let typ = t.Unbound(-1)
  let eff = t.Closed

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)

  assert t.Unbound(x) = resolve(sub, typ)
  assert t.Record(row) = resolve(sub, t.Unbound(-2))
  assert Ok(t.Unbound(y)) = field(row, "foo")
  should.not_equal(x, y)
  assert Ok(t.Unbound(z)) = field(row, "bar")
  should.equal(x, z)
}

// Unions
pub fn tag_test() {
  let exp = e.Tag("foo")
  let env = env.empty()
  let typ = t.Unbound(-1)
  let eff = t.Closed

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Fun(a, _eff, t.Union(t.Extend(l, b, t.Open(_)))) = resolve(sub, typ)
  should.equal(a, b)
  should.equal(l, "foo")

  let exp = e.Apply(exp, e.Binary)
  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Union(t.Extend(l, a, t.Open(_))) = resolve(sub, typ)
  should.equal(a, t.Binary)
  should.equal(l, "foo")
}

// empty match is an error
pub fn closed_match_test() {
  let branches = [#("Some", "v", e.Variable("v")), #("None", "", e.Binary)]
  let exp = e.Match(e.Variable("x"), branches, None)
  let env = env.empty()
  let x = Scheme([], t.Unbound(-2))
  let env = map.insert(env, "x", x)
  let typ = t.Unbound(-1)
  let eff = t.Closed

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Binary = resolve(sub, typ)
  assert t.Union(t.Extend(
    label: "None",
    value: t.Unbound(1),
    tail: t.Extend(label: "Some", value: t.Binary, tail: t.Closed),
  )) = resolve(sub, t.Unbound(-2))
}

pub fn open_match_test() {
  let branches = [#("Some", "v", e.Variable("v")), #("None", "", e.Binary)]
  let exp = e.Match(e.Variable("x"), branches, Some(#("", e.Binary)))
  let env = env.empty()
  let x = Scheme([], t.Unbound(-2))
  let env = map.insert(env, "x", x)
  let typ = t.Unbound(-1)
  let eff = t.Closed

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Binary = resolve(sub, typ)
  assert t.Union(t.Extend(
    label: "None",
    value: t.Unbound(_),
    tail: t.Extend(label: "Some", value: t.Binary, tail: t.Open(_)),
  )) = resolve(sub, t.Unbound(-2))
}

pub fn single_effect_test() {
  let exp = e.Perform("Log")
  let env = env.empty()
  let typ = t.Unbound(-1)
  let eff = t.Open(-2)

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  // No effects untill called
  assert t.Open(-2) = resolve_effect(sub, eff)
  assert t.Fun(t.Unbound(arg), fn_eff, t.Unbound(ret)) = resolve(sub, typ)
  assert Ok(#(t.Unbound(lift), t.Unbound(cont))) = field(fn_eff, "Log")
  should.not_equal(lift, cont)
  should.equal(arg, lift)
  should.equal(cont, ret)

  // test effects are raised when called
  let exp = e.Apply(exp, e.Binary)
  let typ = t.Integer
  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert Ok(#(t.Binary, t.Integer)) =
    resolve_effect(sub, eff)
    |> field("Log")
}

pub fn collect_effects_test() {
  let exp = e.Apply(e.Perform("Log"), e.Apply(e.Perform("Ask"), e.Binary))
  let env = env.empty()
  let typ = t.Unbound(-1)
  let eff = t.Open(-2)

  let ref = javascript.make_reference(0)
  let sub = infer(env, exp, typ, eff, ref)
  assert t.Unbound(final) = resolve(sub, typ)
  let raised = resolve_effect(sub, eff)
  assert Ok(#(t.Binary, t.Unbound(ret1))) = field(raised, "Ask")
  assert Ok(#(t.Unbound(lift2), t.Unbound(ret2))) = field(raised, "Log")
  should.equal(ret1, lift2)
  should.equal(ret2, final)
}
// infer apply where func &arg create effect and final application
// path + errors + warnings + fixpoint + equi/iso + external lookup + hash + zipper
