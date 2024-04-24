import gleam/list

// isomorphic as the opposite of kinded, all types have the same kind.
// This is my terminology.
// Avoid calling simple, is there a more precise name

pub type Type(var) {
  Var(key: var)
  Fun(Type(var), Type(var), Type(var))
  Binary
  Integer
  String
  List(Type(var))
  Record(Type(var))
  Union(Type(var))
  Empty
  RowExtend(String, Type(var), Type(var))
  EffectExtend(String, #(Type(var), Type(var)), Type(var))
  Promise(Type(var))
}

pub const unit = Record(Empty)

pub const boolean = Union(
  RowExtend("True", unit, RowExtend("False", unit, Empty)),
)

pub fn rows(rows) {
  list.fold(list.reverse(rows), Empty, fn(tail, row) {
    let #(label, value) = row
    RowExtend(label, value, tail)
  })
}

pub fn record(fields) {
  Record(rows(fields))
}

pub fn union(fields) {
  Union(rows(fields))
}

pub fn result(value, reason) {
  Union(RowExtend("Ok", value, RowExtend("Error", reason, Empty)))
}

pub const file = Record(
  RowExtend("name", String, RowExtend("content", Binary, Empty)),
)
