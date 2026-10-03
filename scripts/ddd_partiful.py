#!/usr/bin/env python3
"""Build the authored local Partiful graph without editing peers or release pins.

SPEC is the directory holding `partiful_v2/` (milestone 2, served by `lake exe partiful`) and
`partiful/` (milestone 1, kept as `lake exe partiful_m1` for its regression acceptance).
The generated Lake workspace builds the browser bundle itself (DDD-LAPI-07): the target
`partiful_browser` runs the app binary to emit the client, stages the LeanReact runtime and
bundles it with esbuild, and the `partiful` executable `needs` that target. After this
script stages the graph, `lake exe partiful` in the workspace builds and serves everything,
with no Python step and no environment variable. This script stays for development across
local sibling checkouts; an app repository puts the same declarations in its own lakefile.
"""
import argparse
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from ddd_browser_target import browser_target as shared_browser_target  # noqa: E402

p = argparse.ArgumentParser()
p.add_argument('db', type=Path)
p.add_argument('portable', type=Path)
p.add_argument('spec', type=Path)
p.add_argument('--sqlite', type=Path, help='Existing 4.33 SQLite checkout (defaults to the DB dependency)')
p.add_argument('--node-modules', type=Path,
               help='Installed LeanReact node_modules with esbuild (defaults to PORTABLE/node_modules)')
p.add_argument('--prepare-only', action='store_true')
p.add_argument('--only', help='Build only this executable (partiful or partiful_m1)')
p.add_argument('--only-v2', action='store_true', help='Stage only partiful_v2/')
a = p.parse_args()
root = Path.cwd().resolve()
db, peer, spec = (path.resolve() for path in (a.db, a.portable, a.spec))
node_modules = (a.node_modules or peer / 'node_modules').resolve()
assert (root / 'LeanApi.lean').is_file()
assert (node_modules / '.bin/esbuild').exists(), f'esbuild is not installed under {node_modules}'
workspace = root / '.lake/ddd-common'
# One source tree for both apps. Milestone 2's `partiful_v2/` is staged as the modules it names
# (`Partiful.Domain`, `Partiful.Views`, `Partiful.Main`), byte for byte. Milestone 1's
# `partiful/` shares the workspace (and its 1.8 GB of dependency builds) for its regression
# acceptance, so its modules are renamed `PartifulM1.*`: only its `import Partiful.` lines change.
source = root / '.lake/ddd-partiful-source'
source.mkdir(parents=True, exist_ok=True)
APP = re.compile(r'^app% (\S+) where', re.M)

def browser_target(target, server, entry_name, out_name):
    return shared_browser_target(target, server, out_name, root=root, peer=peer, node_modules=node_modules)

engine = peer / 'engine'
runtime_sources = sorted(str(path) for path in (engine / 'runtime').glob('*.mjs'))
q = lambda value: json.dumps(str(value))
config = ''
targets = []

# Milestone 2: `partiful_v2/`, compiled unchanged. Its Main already takes its arguments.
v2 = spec / 'partiful_v2'
if (v2 / 'Main.lean').is_file():
    (source / 'Partiful').mkdir(exist_ok=True)
    for name in ('Domain', 'Views', 'Main'):
        shutil.copyfile(v2 / f'{name}.lean', source / 'Partiful' / f'{name}.lean')
    main = (v2 / 'Main.lean').read_text()
    assert 'def main (args : List String)' in main, 'partiful_v2/Main.lean must define main (args)'
    app = APP.search(main).group(1)
    # Lake gives each executable its own root module, and `needs` makes the root wait for the
    # bundle. So `partiful` is rooted at a module that only imports the authored Main (whose
    # `main` it links), and the browser target runs `partiful_server`, rooted at Main itself.
    (source / 'PartifulLaunch.lean').write_text(
        '/- Generated: `lake exe partiful` runs the authored Main once the browser bundle is built. -/\nimport Partiful.Main\n')
    config += f'''
-- Resolves `Partiful.*` imports (no `Partiful.lean` exists; only the executables are built).
lean_lib Partiful where
  srcDir := {q(source)}

/-- The authored Main. The browser target runs it once to emit the client. -/
lean_exe partiful_server where
  srcDir := {q(source)}
  root := `Partiful.Main
''' + browser_target('partiful_browser', 'partiful_server', 'App.mjs', app) + f'''
/-- `lake exe partiful [migrate [--check]]`: builds the bundle first, then gates the
database and serves the API and the pages. -/
lean_exe partiful where
  srcDir := {q(source)}
  root := `PartifulLaunch
  needs := #[partiful_browser]
'''
    targets += [('partiful', app)]
    # The same Main before its migration was written (the post: "LeanDB won't apply the new
    # schema until there's a migration for the old rows"), for the gate's refusal check.
    unmigrated, count = re.subn(r'\n  migrations := \[.*?\n  \]\n', '\n', main, flags=re.S)
    assert count == 1, 'partiful_v2/Main.lean: expected one multi-line `migrations := [...]` clause'
    (source / 'PartifulUnmigrated.lean').write_text(
        '/- Generated: partiful_v2/Main.lean without its `migrations` clause. -/\n' + unmigrated)
    config += f'''
lean_exe partiful_unmigrated where
  srcDir := {q(source)}
  root := `PartifulUnmigrated
'''
    targets += [('partiful_unmigrated', None)]

# Milestone 1: `partiful/`, for its regression acceptance (`partiful_m1`).
m1 = spec / 'partiful'
if (m1 / 'Main.lean').is_file() and not a.only_v2:
    (source / 'PartifulM1').mkdir(exist_ok=True)
    rename = lambda text: text.replace('import Partiful.', 'import PartifulM1.').replace('import LeanApi.Domain', 'import LeanApiDomain.App')
    for name in ('Domain', 'Views'):
        (source / 'PartifulM1' / f'{name}.lean').write_text(rename((m1 / f'{name}.lean').read_text()))
    main = rename((m1 / 'Main.lean').read_text())
    (source / 'PartifulM1Main.lean').write_text(main)
    # A `main : IO Unit` that calls `.serve` cannot see process arguments, so the launcher's
    # copy passes them to `NativeApp.main` (for `migrate [--check]`).
    launch = re.sub(r'^def main : IO Unit := (\S+)\.serve (.*)$',
                    r'def main (args : List String) : IO UInt32 := \1.main args \2', main, flags=re.M)
    (source / 'PartifulM1Launch.lean').write_text(
        '/- Generated launcher: the milestone 1 Main, with `main` taking its arguments. -/\n' + launch)
    app = APP.search(main).group(1)
    config += f'''
lean_lib PartifulM1 where
  srcDir := {q(source)}
  roots := #[`PartifulM1, `PartifulM1Main, `PartifulM1Launch]
lean_exe partiful_m1_server where
  srcDir := {q(source)}
  root := `PartifulM1Main
''' + browser_target('partiful_m1_browser', 'partiful_m1_server', 'App.mjs', app) + f'''
lean_exe partiful_m1 where
  srcDir := {q(source)}
  root := `PartifulM1Launch
  needs := #[partiful_m1_browser]
'''
    targets += [('partiful_m1', app)]

assert targets, f'no partiful_v2/ or partiful/ app under {spec}'
prepare = ['python3', str(root / 'scripts/ddd_prepare_common.py'), str(db), str(peer), '--node-modules', str(node_modules)]
if a.sqlite:
    prepare += ['--sqlite', str(a.sqlite)]
subprocess.run(prepare, check=True)
with (workspace / 'lakefile.lean').open('a') as lakefile:
    lakefile.write(config)
if a.prepare_only:
    raise SystemExit(0)
env = dict(os.environ, LEAN_NUM_THREADS='2')
for exe, app in targets:
    if a.only and exe != a.only:
        continue
    subprocess.run(['lake', 'build', exe], cwd=workspace, env=env, check=True)
    if app is None:
        print(f'PASS: {exe}')
        continue
    web = workspace / '.lake/ddd-browser' / app
    assert (web / 'app.mjs').is_file(), f'the {exe} browser target did not produce app.mjs'
    print(f'PASS: {exe}: native Domain/Views/Main and compiled browser at {web}')
    print(f'Run: (cd {workspace} && lake exe {exe})')
