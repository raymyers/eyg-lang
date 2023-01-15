import harness/ffi/env
import harness/ffi/core
import harness/ffi/integer
import harness/ffi/linked_list
import harness/ffi/string
import eyg/runtime/interpreter as r
import eyg/analysis/typ as t

pub fn lib() {
  let #(types, values) =
    env.init()
    |> env.extend("equal", core.equal())
    |> env.extend("debug", core.debug())
    |> env.extend("fix", core.fix())
    // integer
    |> env.extend("ffi_add", integer.add())
    |> env.extend("ffi_subtract", integer.subtract())
    |> env.extend("ffi_multiply", integer.multiply())
    |> env.extend("ffi_divide", integer.divide())
    |> env.extend("ffi_absolute", integer.absolute())
    |> env.extend("ffi_int_parse", integer.int_parse())
    |> env.extend("ffi_int_to_string", integer.int_to_string())
    // string
    |> env.extend("ffi_append", string.append())
    |> env.extend("ffi_uppercase", string.uppercase())
    |> env.extend("ffi_lowercase", string.lowercase())
    |> env.extend("ffi_length", string.length())
    // list
    |> env.extend("ffi_fold", fold())
    |> env.extend("ffi_pop", linked_list.pop())
}

// TODO move fold to list and test
pub fn fold() {
  #(
    t.Fun(
      t.LinkedList(t.Unbound(-7)),
      t.Open(-8),
      t.Fun(
        t.Unbound(-9),
        t.Open(-10),
        t.Fun(
          t.Fun(
            t.Unbound(-7),
            t.Open(-11),
            t.Fun(t.Unbound(-9), t.Open(-12), t.Unbound(-9)),
          ),
          t.Open(-13),
          t.Unbound(-9),
        ),
      ),
    ),
    builtin3(fn(list, initial, f, k) {
      assert r.LinkedList(elements) = list
      do_fold(elements, initial, f, k)
    }),
  )
}

fn do_fold(elements, state, f, k) {
  case elements {
    [] -> r.continue(k, state)
    [e, ..rest] ->
      r.eval_call(f, e, r.eval_call(_, state, do_fold(rest, _, f, k)))
  }
}

fn builtin3(f) {
  r.Builtin(fn(a, k) {
    r.continue(
      k,
      r.Builtin(fn(b, k) {
        r.continue(k, r.Builtin(fn(c, k) { f(a, b, c, k) }))
      }),
    )
  })
}
