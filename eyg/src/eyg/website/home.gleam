import eyg/website/components
import eyg/website/components/snippet
import eyg/website/home/state
import eyg/website/page
import lustre
import lustre/attribute as a
import lustre/element
import lustre/element/html as h
import lustre/event
import morph/editable as e

pub fn page(bundle) {
  page.app("eyg/website/home", "client", bundle)
}

pub fn client() {
  let app = lustre.application(state.init, state.update, render)
  let assert Ok(_) = lustre.start(app, "#app", Nil)
  Nil
}

fn render(state) {
  let src =
    e.Block(
      [#(e.Bind("message"), e.Call(e.Perform("Alert"), [e.String("Go")]))],
      e.Vacant(""),
      True,
    )
  h.div([a.class("yellow-gradient")], [
    components.header(),
    h.div([a.class("mx-auto max-w-2xl")], [
      snippet.render(snippet.init(src, effects())),
    ]),
  ])
}

fn effects() {
  []
}
