"""The compiled browser bundle of an app with pages, as a Lake target (DDD-LAPI-07).

`browser_target(...)` returns the Lake declaration: it runs the app's server executable once
with LEANAPP_EMIT_CLIENT to emit the generated client and `pages.json`, stages the entry
(`adapters/domain/browser/App.mjs`) and the LeanReact runtime next to the LeanJS module that
`app%` wrote at elaboration, and bundles them with esbuild. Rebuilt when the server binary or
any staged source changes. Used by ddd_partiful.py and ddd_prepare_common.py.
"""
import json
from pathlib import Path


def browser_target(target, server, out_name, *, root, peer, node_modules, args=()):
    q = lambda value: json.dumps(str(value))
    engine = Path(peer) / 'engine'
    runtime_sources = sorted(str(path) for path in (engine / 'runtime').glob('*.mjs'))
    arguments = ', '.join(q(arg) for arg in args)
    return f'''
target {target} pkg : FilePath := do
  let some server ← findLeanExe? `{server} | error "{server} is not declared"
  let serverJob ← server.exe.fetch
  let entry : FilePath := {q(Path(root) / 'adapters/domain/browser/App.mjs')}
  let engine : FilePath := {q(engine)}
  let runtime : Array FilePath := #[{', '.join(q(path) for path in runtime_sources)}]
  let adapters : Array FilePath := #[engine / "adapters" / "leanjs-react.mjs", engine / "adapters" / "leanjs-contract.mjs"]
  let contract : Array FilePath := #[engine / "LeanContract" / "Fetch.mjs", engine / "LeanContract" / "Codecs.mjs"]
  let inputs ← (#[entry] ++ runtime ++ adapters ++ contract).mapM fun file => (inputTextFile file : SpawnM _)
  let out := pkg.dir / ".lake" / "ddd-browser" / {q(out_name)}
  buildFileAfterDep (out / "app.mjs") (serverJob.add (Job.mixArray inputs)) fun exe => do
    IO.FS.createDirAll (out / "runtime")
    proc {{ cmd := exe.toString, args := #[{arguments}], cwd := pkg.dir, env := #[("LEANAPP_EMIT_CLIENT", some out.toString)] }}
    IO.FS.writeFile (out / "entry.mjs") (← IO.FS.readFile entry)
    for file in runtime ++ contract do
      IO.FS.writeFile (out / "runtime" / file.fileName.get!) (← IO.FS.readFile file)
    for file in adapters do
      -- Keep Fetch.CallFailure a single ESM identity after staging the runtime.
      let text := (← IO.FS.readFile file).replace "../LeanContract/Fetch.mjs" "./Fetch.mjs"
      IO.FS.writeFile (out / "runtime" / file.fileName.get!) text
    proc {{
      cmd := {q(Path(node_modules) / '.bin/esbuild')}
      cwd := pkg.dir
      env := #[("NODE_PATH", some {q(node_modules)})]
      args := #[(out / "entry.mjs").toString, "--bundle", "--format=esm", "--platform=browser",
        "--target=es2022", "--define:process.env.NODE_ENV=\\"production\\"", s!"--outfile={{out / "app.mjs"}}"] }}
'''
