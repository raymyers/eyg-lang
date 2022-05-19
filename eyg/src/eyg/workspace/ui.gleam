import gleam/dynamic
import gleam/io
import gleam/option.{None, Some}
import gleam/javascript/array.{Array}
import gleam/javascript/promise.{Promise}
import eyg/ast/editor
import platform/browser
import eyg/workspace/workspace.{Bench, Editor, State}

external fn fetch(String) -> Promise(String) =
  "../../browser_ffi" "fetchSource"

// TODO move to workspace
pub fn init() {
  let state = State(focus: Editor, editor: None)

  let task =
    promise.map(
      fetch("./saved.json"),
      fn(data) {
        fn(before) {
          let e = editor.init(data, browser.harness())
          let state = State(..before, editor: Some(e))

          #(state, array.from_list([]))
        }
      },
    )
  #(state, array.from_list([task]))
}

pub type Transform(n) =
  fn(State(n)) -> #(State(n), Array(Promise(fn(State(n)) -> #(State(n), Nil))))

pub fn click(marker) -> Transform(n) {
  fn(before: State(n)) {
    let state = case marker {
      ["editor", ..rest] -> {
        let editor = case rest, before.editor {
          [], _ -> before.editor
          [x], Some(editor) -> Some(editor.handle_change(editor, x))
        }
        State(..before, focus: Editor, editor: editor)
      }
      ["bench"] -> State(..before, focus: Bench)
      _ -> before
    }
    #(state, array.from_list([]))
  }
}

pub fn keydown(key: String, ctrl: Bool, text: String) -> Transform(n) {
  fn(before) {
    let state = case before {
      State(focus: Editor, editor: Some(editor)) -> {
        let editor = editor.handle_keydown(editor, key, ctrl, text)
        State(..before, editor: Some(editor))
      }
      _ -> before
    }
    #(state, array.from_list([]))
  }
}

// views
pub fn editor_focused(state: State(n)) {
  state.focus == Editor
}

pub fn bench_focused(state: State(n)) {
  state.focus == Bench
}

pub fn get_editor(state: State(n)) {
  case state.editor {
    None -> dynamic.from(Nil)
    Some(editor) -> dynamic.from(editor)
  }
}

// Bench rename panel benches?
pub type Mount {
  Mount(value: String)
}

// TODO add inspect to std lib
external fn inspect_gleam(a) -> String =
  "../../gleam" "inspect"

external fn inspect(a) -> String =
  "" "JSON.stringify"

pub fn benches(state: State(n)) {
  case state.editor {
    None -> []

    Some(editor) ->
      case editor.eval(editor) {
        Ok(code) ->
          case dynamic.field("test", Ok)(code) {
            Ok(test) -> [Mount(inspect(code)), Mount(inspect(test))]
            Error(_) -> []
          }
        _ -> []
      }
  }
  |> array.from_list()
}
