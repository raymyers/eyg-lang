import gleam/io
import gleam/javascript/array
import gleam/javascript/promise
import gleam/list
import gleam/string
import midas/node
import midas/sdk/netlify
import midas/task as t
import mysig/build
import mysig/dev
import mysig/route.{Route}
import plinth/node/process
import snag
import website/routes/documentation
import website/routes/editor
import website/routes/home
import website/routes/news

pub fn main() {
  do_main(list.drop(array.to_list(process.argv()), 2))
}

fn do_main(args) {
  use result <- promise.map(case args {
    [] as args | ["develop", ..args] -> develop(args)
    ["deploy"] -> deploy(args)
    _ -> {
      promise.resolve(snag.error("no runner for: " <> args |> string.join(" ")))
    }
  })
  case result {
    Ok(Nil) -> Nil
    Error(reason) -> io.println(snag.pretty_print(reason))
  }
}

// doesn't have client secret
pub const netlify_local_app = netlify.App(
  "cQmYKaFm-2VasrJeeyobXXz5G58Fxy2zQ6DRMPANWow",
  "http://localhost:8080/auth/netlify",
)

const site_id = "eae24b5b-4854-4973-8a9f-8fb3b1c423c0"

fn deploy(_args) {
  use files <- promise.try_await(build.to_files(routes()))
  let task = {
    use token <- t.do(netlify.authenticate(netlify_local_app))
    use _ <- t.do(netlify.deploy_site(token, site_id, files))
    use _ <- t.do(t.log("Deployed"))
    t.done(Nil)
  }
  node.run(task, ".")
}

fn develop(_args) {
  dev.serve(routes())
  promise.resolve(Ok(Nil))
}

fn routes() {
  Route(index: home.page(), items: [
    #("documentation", Route(index: documentation.page(), items: [])),
    #("editor", Route(index: editor.page(), items: [])),
    #("news", news.route()),
  ])
}
