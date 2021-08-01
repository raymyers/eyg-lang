import gleam/io
import gleam/list
import language/type_.{Data, Function, PolyType, Type, Variable}

// pub type Type {
//   Function(arguments: List(Type), return: Type)
//   App(name: String, parameters: List(Type))
//   Variable(Int)
// }
pub opaque type Scope {
  // varibles are polytype in one thing
  Scope(
    // Maybe remove polytype
    variables: List(#(String, PolyType)),
    // variables: List(#(String, #(List(Int), Type))),
    // called datatypes from haskell
    // forall a, Some(a) -> Option(a)
    // #(name, parameters, constructors(name, arguments))
    // This is a polytype for n-things
    types: List(#(String, List(Int), List(#(String, List(Type))))),
  )
}

// types: List(Nil)
pub fn new() {
  Scope([], [])
}

pub fn set_variable(scope, label, type_) {
  let Scope(variables: variables, ..) = scope
  let variables = [#(label, type_), ..variables]
  Scope(..scope, variables: variables)
}

// Free vars in forall are those vars that are free
// in the type minus those bound by quantifiers
pub fn free_variables(scope) {
  let Scope(variables: variables, ..) = scope
  list.map(
    variables,
    fn(entry) {
      let #(_name, poly) = entry
      type_.free_variables(poly)
    },
  )
  |> list.fold([], fn(more, acc) { list.append(more, acc) })
}

pub fn newtype(scope, type_name, params, constructors) {
  let Scope(types: types, ..) = scope
  let types = [#(type_name, params, constructors), ..types]
  let scope = Scope(..scope, types: types)
  list.fold(
    constructors,
    scope,
    fn(constructor, scope) {
      let #(fn_name, arguments) = constructor
      // Constructor when instantiate will be unifiying to a concrete type
      let new_type = Data(type_name, list.map(params, Variable))
      set_variable(
        scope,
        fn_name,
        PolyType(forall: params, type_: Function(arguments, new_type)),
      )
    },
  )
}

// assign and lookup
pub fn get_variable(scope, label) {
  let Scope(variables: variables, ..) = scope
  case list.key_find(variables, label) {
    Ok(value) -> Ok(value)
    Error(Nil) -> {
      io.debug(label)
      Error(todo("Variable not in environment"))
    }
  }
}

pub fn get_constructor(scope, constructor) {
  let Scope(types: types, ..) = scope
  do_get_constructor(types, constructor)
}

fn do_get_constructor(types, constructor) {
  case types {
    [#(type_name, params, variants), ..types] ->
      case list.key_find(variants, constructor) {
        Ok(arguments) -> Ok(#(type_name, params, arguments))
        Error(Nil) -> do_get_constructor(types, constructor)
      }
  }
}

// fn generalise_type(type_, typer) {
//   case type_ {
//     Function(arguments, return) -> todo("some")
//   }
//   // App(_) -> 
//   // Variable(_) -> []
// }
fn instantiate() {
  todo
}
