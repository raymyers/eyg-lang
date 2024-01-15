import gleam/int
import gleam/list
import gleam/dict.{type Dict}
import gleam/option.{type Option, None, Some}
import gleam/string
import eygir/expression as e
import gleam/javascript/promise.{type Promise as JSPromise}

pub type Failure {
  NotAFunction(Term)
  UndefinedVariable(String)
  Vacant(comment: String)
  NoMatch(term: Term)
  UnhandledEffect(String, Term)
  IncorrectTerm(expected: String, got: Term)
  MissingField(String)
}

// TODO separate interpreter from runner
// TODO separate async run from async eval

pub fn run(source, env, term, extrinsic) {
  case
    eval(
      source,
      env,
      Stack(CallWith(term, [], env), WillRenameAsDone(extrinsic)),
    )
  {
    // could eval the f and return it by wrapping in a value and then separetly calling eval call in handle
    // Can I have a type called Running, that has a Cont but not Value, and separaetly Return with Value and not Cont
    // The eval fn above could use Not a Function Error in any case which is not a Function
    Value(term) -> Ok(term)
    Abort(failure, path, _env, _k) -> Error(#(failure, path))
    // Cont(_, _) -> panic("should have evaluated and not be a Cont at all")
    // other runtime errors return error, maybe this should be the same
    Async(_, _, _, _) ->
      panic(
        "cannot return async value some sync run. This effect would not be allowed by type system",
      )
  }
}

pub fn run_async(source, env, term, extrinsic) {
  let ret =
    handle(
      eval(
        source,
        env,
        Stack(CallWith(term, [], env), WillRenameAsDone(extrinsic)),
      ),
      extrinsic,
    )
  flatten_promise(ret, extrinsic)
}

// not really eval as includes handlers
pub fn eval_async(source, env, extrinsic) {
  let ret = handle(eval(source, env, WillRenameAsDone(extrinsic)), extrinsic)
  flatten_promise(ret, extrinsic)
}

pub fn flatten_promise(ret, extrinsic) {
  case ret {
    // could eval the f and return it by wrapping in a value and then separetly calling eval call in handle
    // Can I have a type called Running, that has a Cont but not Value, and separaetly Return with Value and not Cont
    // The eval fn above could use Not a Function Error in any case which is not a Function
    Value(term) -> promise.resolve(Ok(term))
    Abort(failure, path, env, _k) ->
      promise.resolve(Error(#(failure, path, env)))
    Async(p, rev, env, k) ->
      promise.await(p, fn(return) {
        let next = loop(V(Value(return)), rev, env, k)
        flatten_promise(handle(next, extrinsic), extrinsic)
      })
  }
}

pub fn handle(return, extrinsic) {
  case return {
    Value(term) -> Value(term)
    Abort(failure, rev, env, k) -> Abort(failure, rev, env, k)
    Async(promise, rev, env, k) -> Async(promise, rev, env, k)
  }
}

pub type Term {
  Binary(value: BitArray)
  Integer(value: Int)
  Str(value: String)
  LinkedList(elements: List(Term))
  Record(fields: List(#(String, Term)))
  Tagged(label: String, value: Term)
  Function(
    param: String,
    body: e.Expression,
    env: List(#(String, Term)),
    path: List(Int),
  )
  Defunc(Switch, List(Term))
  Promise(JSPromise(Term))
}

pub type Switch {
  Cons
  Extend(String)
  Overwrite(String)
  Select(String)
  Tag(String)
  Match(String)
  NoCases
  Perform(String)
  Handle(String)
  Resume(Stack, List(Int), Env)
  Shallow(String)
  Builtin(String)
}

pub type Path =
  List(Int)

// Keep Stack) outsie
pub type Kontinue {
  // arg path then call path
  Arg(e.Expression, Path, Path, Env)
  Apply(Term, Path, Env)
  Assign(String, e.Expression, Path, Env)
  CallWith(Term, Path, Env)
  Delimit(String, Term, Path, Env, Bool)
}

pub type Stack {
  Stack(Kontinue, Stack)
  // TODO actually a function
  WillRenameAsDone(
    Dict(String, fn(Term, Stack) -> #(Control, List(Int), Env, Stack)),
  )
}

pub const unit = Record([])

pub const true = Tagged("True", unit)

pub const false = Tagged("False", unit)

pub fn ok(value) {
  Tagged("Ok", value)
}

pub fn error(reason) {
  Tagged("Error", reason)
}

// This might not give in runtime core, more runtime presentation
pub fn to_string(term) {
  case term {
    Binary(value) -> e.print_bit_string(value)
    Integer(value) -> int.to_string(value)
    Str(value) -> string.concat(["\"", value, "\""])
    LinkedList(items) ->
      list.map(items, to_string)
      |> list.intersperse(", ")
      |> list.prepend("[")
      |> list.append(["]"])
      |> string.concat
    Record(fields) ->
      fields
      |> list.map(field_to_string)
      |> list.intersperse(", ")
      |> list.prepend("{")
      |> list.append(["}"])
      |> string.concat
    Tagged(label, value) -> string.concat([label, "(", to_string(value), ")"])
    Function(param, _, _, _) -> string.concat(["(", param, ") -> { ... }"])
    Defunc(d, args) ->
      string.concat([
        "Defunc: ",
        string.inspect(d),
        " ",
        ..list.intersperse(list.map(args, to_string), ", ")
      ])
    Promise(_) -> string.concat(["Promise: "])
  }
}

fn field_to_string(field) {
  let #(k, v) = field
  string.concat([k, ": ", to_string(v)])
}

pub fn reason_to_string(reason) {
  case reason {
    UndefinedVariable(var) -> string.append("variable undefined: ", var)
    IncorrectTerm(expected, got) ->
      string.concat([
        "unexpected term, expected: ",
        expected,
        " got: ",
        to_string(got),
      ])
    MissingField(field) -> string.concat(["missing record field: ", field])
    NoMatch(term) -> string.concat(["no cases matched for: ", to_string(term)])
    NotAFunction(term) ->
      string.concat(["function expected got: ", to_string(term)])
    UnhandledEffect("Abort", reason) ->
      string.concat(["Aborted with reason: ", to_string(reason)])
    UnhandledEffect(effect, lift) ->
      string.concat(["unhandled effect ", effect, "(", to_string(lift), ")"])
    Vacant(note) -> string.concat(["tried to run a todo: ", note])
  }
}

pub fn field(term, field) {
  case term {
    Record(fields) ->
      case list.key_find(fields, field) {
        Ok(value) -> Ok(value)
        Error(Nil) -> Error(Nil)
      }
    _ -> Error(Nil)
  }
}

pub type Return {
  // It's messy to have Value and Cont, but I don't know how to do this in a tail recursive way
  // This problem will hopefully go away as I build a more sophisticated interpreter.
  // Value is needed for returning from eval/run
  // Cont is needed to break the stack (with loop).
  // I could remove Value and always return a result from run, but that would make it not easy to check correct Effects in tests.
  Value(term: Term)

  Abort(reason: Failure, rev: List(Int), env: Env, k: Stack)
  Async(promise: JSPromise(Term), rev: List(Int), env: Env, k: Stack)
}

pub fn eval_call(f, arg, env, k: Stack) {
  // allways produces value even if abort
  let #(c, rev, e, k) = step_call(f, arg, [], env, k)
  loop(c, rev, e, k)
}

pub fn step_call(f, arg, rev, env: Env, k: Stack) {
  case f {
    Function(param, body, captured, rev) -> {
      let env = Env(..env, scope: [#(param, arg), ..captured])
      #(E(body), rev, env, k)
    }
    // builtin needs to return result for the case statement
    Defunc(switch, applied) ->
      case switch, applied {
        Cons, [item] -> prim(cons(item, arg, rev, env, k), rev, env, k)
        Extend(label), [value] ->
          prim(extend(label, value, arg, rev, env, k), rev, env, k)
        Overwrite(label), [value] ->
          prim(overwrite(label, value, arg, rev, env, k), rev, env, k)
        Select(label), [] -> prim(select(label, arg, rev, env, k), rev, env, k)
        Tag(label), [] -> prim(Value(Tagged(label, arg)), rev, env, k)
        Match(label), [branch, rest] ->
          match(label, branch, rest, arg, rev, env, k)
        NoCases, [] -> prim(Abort(NoMatch(arg), rev, env, k), rev, env, k)
        // env is part of k
        Perform(label), [] -> perform(label, arg, rev, env, k)
        Handle(label), [handler] -> deep(label, handler, arg, rev, env, k)
        // Ok so I am lost as to why resume works or is it even needed
        // I think it is in the situation where someone serializes a
        // partially applied continuation function in handler
        Resume(popped, rev, env), [] -> {
          let k = move(popped, k)
          #(V(Value(arg)), rev, env, k)
        }
        Shallow(label), [handler] -> {
          shallow(label, handler, arg, rev, env, k)
        }
        Builtin(key), applied ->
          call_builtin(key, list.append(applied, [arg]), rev, env, k)

        switch, _ -> {
          let applied = list.append(applied, [arg])
          #(V(Value(Defunc(switch, applied))), rev, env, k)
        }
      }

    term -> prim(Abort(NotAFunction(term), rev, env, k), rev, env, k)
  }
}

pub fn prim(return, rev, env, k) {
  #(V(return), rev, env, k)
}

pub type Always =
  #(Control, List(Int), Env, Stack)

pub type Arity {
  Arity1(fn(Term, List(Int), Env, Stack) -> Always)
  Arity2(fn(Term, Term, List(Int), Env, Stack) -> Always)
  Arity3(fn(Term, Term, Term, List(Int), Env, Stack) -> Always)
}

fn call_builtin(key, applied, rev, env: Env, kont) -> Always {
  case dict.get(env.builtins, key) {
    Ok(func) ->
      case func, applied {
        // pretty sure impl wont use path
        Arity1(impl), [x] -> impl(x, rev, env, kont)
        Arity2(impl), [x, y] -> impl(x, y, rev, env, kont)
        Arity3(impl), [x, y, z] -> impl(x, y, z, rev, env, kont)
        _, _args -> #(V(Value(Defunc(Builtin(key), applied))), rev, env, kont)
      }
    Error(Nil) ->
      prim(Abort(UndefinedVariable(key), rev, env, kont), rev, env, kont)
  }
}

// In interpreter because circular dependencies interpreter -> spec -> stdlib/linked list

pub type Control {
  E(e.Expression)
  V(Return)
}

// TODO rename when I fix return
pub type StepR {
  K(Control, List(Int), Env, Stack)
  Done(Return)
}

pub fn eval(exp: e.Expression, env, k) {
  loop(E(exp), [], env, k)
}

// Loop is always tail recursive.
// It is used to string individual steps into an eval call.
// If not separated the eval implementation causes stack overflows.
// This is because eval needs references to itself in continuations.
pub fn loop(c, p, e, k) {
  let next = step(c, p, e, k)
  case next {
    K(c, p, e, k) -> loop(c, p, e, k)
    Done(return) -> return
  }
}

pub fn loop_till(c, p, e, k) {
  case step(c, p, e, k) {
    K(c, p, e, k) -> loop_till(c, p, e, k)
    Done(return) -> {
      let assert True = V(return) == c
      #(return, e)
    }
  }
}

pub fn resumable(exp: e.Expression, env, k) {
  loop_till(E(exp), [], env, k)
}

pub type Env {
  Env(scope: List(#(String, Term)), builtins: dict.Dict(String, Arity))
}

fn step(exp, rev, env: Env, k) {
  case exp {
    E(e.Lambda(param, body)) ->
      K(V(Value(Function(param, body, env.scope, rev))), rev, env, k)
    E(e.Apply(f, arg)) -> {
      K(E(f), [0, ..rev], env, Stack(Arg(arg, [1, ..rev], rev, env), k))
    }

    E(e.Variable(x)) -> {
      let return = case list.key_find(env.scope, x) {
        Ok(term) -> Value(term)
        Error(Nil) -> Abort(UndefinedVariable(x), rev, env, k)
      }
      K(V(return), rev, env, k)
    }
    E(e.Let(var, value, then)) -> {
      K(E(value), [0, ..rev], env, Stack(Assign(var, then, [1, ..rev], env), k))
    }

    E(e.Binary(value)) -> K(V(Value(Binary(value))), rev, env, k)
    E(e.Integer(value)) -> K(V(Value(Integer(value))), rev, env, k)
    E(e.Str(value)) -> K(V(Value(Str(value))), rev, env, k)
    E(e.Tail) -> K(V(Value(LinkedList([]))), rev, env, k)
    E(e.Cons) -> K(V(Value(Defunc(Cons, []))), rev, env, k)
    E(e.Vacant(comment)) ->
      K(V(Abort(Vacant(comment), rev, env, k)), rev, env, k)
    E(e.Select(label)) -> K(V(Value(Defunc(Select(label), []))), rev, env, k)
    E(e.Tag(label)) -> K(V(Value(Defunc(Tag(label), []))), rev, env, k)
    E(e.Perform(label)) -> K(V(Value(Defunc(Perform(label), []))), rev, env, k)
    E(e.Empty) -> K(V(Value(Record([]))), rev, env, k)
    E(e.Extend(label)) -> K(V(Value(Defunc(Extend(label), []))), rev, env, k)
    E(e.Overwrite(label)) ->
      K(V(Value(Defunc(Overwrite(label), []))), rev, env, k)
    E(e.Case(label)) -> K(V(Value(Defunc(Match(label), []))), rev, env, k)
    E(e.NoCases) -> K(V(Value(Defunc(NoCases, []))), rev, env, k)
    E(e.Handle(label)) -> K(V(Value(Defunc(Handle(label), []))), rev, env, k)
    E(e.Shallow(label)) -> K(V(Value(Defunc(Shallow(label), []))), rev, env, k)
    E(e.Builtin(identifier)) ->
      K(V(Value(Defunc(Builtin(identifier), []))), rev, env, k)
    V(Value(value)) -> apply_k(value, k)
    // Other could be any kind of Halt function and always get a path
    V(other) -> Done(other)
  }
}

fn apply_k(value, k) {
  case k {
    Stack(switch, k) ->
      case switch {
        Assign(label, then, rev, env) -> {
          let env = Env(..env, scope: [#(label, value), ..env.scope])
          K(E(then), rev, env, k)
        }
        Arg(arg, rev, call_rev, env) ->
          K(E(arg), rev, env, Stack(Apply(value, call_rev, env), k))
        Apply(f, rev, env) -> {
          let #(c, rev, e, k) = step_call(f, value, rev, env, k)
          K(c, rev, e, k)
        }
        CallWith(arg, rev, env) -> {
          let #(c, rev, e, k) = step_call(value, arg, rev, env, k)
          K(c, rev, e, k)
        }
        Delimit(_, _, _, _, _) -> {
          apply_k(value, k)
        }
      }
    WillRenameAsDone(_) -> Done(Value(value))
  }
}

fn cons(item, tail, rev, env, k) {
  case tail {
    LinkedList(elements) -> Value(LinkedList([item, ..elements]))
    term -> Abort(IncorrectTerm("LinkedList", term), rev, env, k)
  }
}

fn select(label, arg, rev, env, k) {
  case arg {
    Record(fields) ->
      case list.key_find(fields, label) {
        Ok(value) -> Value(value)
        Error(Nil) -> Abort(MissingField(label), rev, env, k)
      }
    term ->
      Abort(
        IncorrectTerm(string.append("Record (-select) ", label), term),
        rev,
        env,
        k,
      )
  }
}

fn extend(label, value, rest, rev, env, k) {
  case rest {
    Record(fields) -> Value(Record([#(label, value), ..fields]))
    term -> Abort(IncorrectTerm("Record (-extend) ", term), rev, env, k)
  }
}

fn overwrite(label, value, rest, rev, env, k) {
  case rest {
    Record(fields) ->
      case list.key_pop(fields, label) {
        Ok(#(_old, fields)) -> Value(Record([#(label, value), ..fields]))
        Error(Nil) -> Abort(MissingField(label), rev, env, k)
      }
    term -> Abort(IncorrectTerm("Record (-overwrite) ", term), rev, env, k)
  }
}

fn match(label, matched, otherwise, value, rev, env, k) {
  case value {
    Tagged(l, term) ->
      case l == label {
        True -> step_call(matched, term, rev, env, k)
        False -> step_call(otherwise, value, rev, env, k)
      }
    term -> {
      let message = string.concat(["Tagged |", label])
      prim(Abort(IncorrectTerm(message, term), rev, env, k), rev, env, k)
    }
  }
}

fn move(delimited, acc) {
  case delimited {
    WillRenameAsDone(_) -> acc
    Stack(step, rest) -> move(rest, Stack(step, acc))
  }
}

fn do_perform(label, arg, i_rev, i_env, k, acc) {
  case k {
    Stack(Delimit(l, h, rev, e, True), rest) if l == label -> {
      let resume = Defunc(Resume(acc, i_rev, i_env), [])
      let k =
        Stack(CallWith(arg, rev, e), Stack(CallWith(resume, rev, e), rest))
      #(V(Value(h)), rev, e, k)
    }
    Stack(Delimit(l, h, rev, e, False), rest) if l == label -> {
      let acc = Stack(Delimit(label, h, rev, e, False), acc)
      let resume = Defunc(Resume(acc, i_rev, i_env), [])
      let k =
        Stack(CallWith(arg, rev, e), Stack(CallWith(resume, rev, e), rest))
      #(V(Value(h)), rev, e, k)
    }
    Stack(kontinue, rest) ->
      do_perform(label, arg, i_rev, i_env, rest, Stack(kontinue, acc))
    WillRenameAsDone(extrinsic) -> {
      case dict.get(extrinsic, label) {
        Ok(handler) -> handler(arg, k)
        Error(Nil) -> #(
          V(Abort(
            UnhandledEffect(label, arg),
            i_rev,
            i_env,
            // inefficient to move back in error case
            move(acc, WillRenameAsDone(dict.new())),
          )),
          i_rev,
          i_env,
          k,
        )
      }
    }
  }
}

pub fn perform(label, arg, i_rev, i_env, k: Stack) {
  do_perform(label, arg, i_rev, i_env, k, WillRenameAsDone(dict.new()))
}

// rename handle and move the handle for runner with handles out
pub fn deep(label, handle, exec, rev, env, k) {
  let k = Stack(Delimit(label, handle, rev, env, False), k)
  step_call(exec, Record([]), rev, env, k)
}

// somewhere this needs outer k
fn shallow(label, handle, exec, rev, env: Env, k) -> Always {
  let k = Stack(Delimit(label, handle, rev, env, True), k)
  step_call(exec, Record([]), rev, env, k)
}
