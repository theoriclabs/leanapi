#!/usr/bin/env python3
"""Isolated linked 4.33 validation, using source checkouts without writing to peers."""
import argparse
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('db', type=Path)
p.add_argument('portable', type=Path)
p.add_argument('--output', type=Path, default=Path('.lake/ddd-common'))
p.add_argument('--sqlite', type=Path, help='Existing 4.33 SQLite checkout (defaults to DB dependency)')
p.add_argument('--node-modules', type=Path,
               help='Installed LeanReact node_modules with esbuild: adds the fixture apps\' browser targets')
a = p.parse_args()
root, db, peer, out = (x.resolve() for x in (Path.cwd(), a.db, a.portable, a.output))
assert (root / 'LeanApi.lean').is_file()
assert (db / 'LeanDb.lean').is_file()
assert (peer / 'engine/LeanApp/Domain.lean').is_file()
assert out.is_relative_to(root / '.lake')
sqlite = a.sqlite.resolve() if a.sqlite else db / '.lake/packages/leansqlite'
archive = sqlite / '.lake/build/lib/libleansqlite.a'
assert archive.is_file(), 'Build the peer SQLite dependency first; this script never builds in peers'
crypto = root / '.lake/packages/leancrypto'
openssl = next((x for x in (Path('/opt/homebrew/opt/openssl@3'), Path('/usr/local/opt/openssl@3'))
                if (x / 'lib/libcrypto.a').is_file()), None)
assert openssl, 'An existing OpenSSL static library is required; nothing is provisioned'
q = lambda x: json.dumps(str(x))
out.mkdir(parents=True, exist_ok=True)
config = f'''import Lake
open System Lake DSL
package domain_common_checks where
  moreLinkArgs := #[{q(openssl / 'lib/libcrypto.a')}]

extern_lib leansqlite pkg := do
  let source ← inputBinFile {q(archive)}
  source.mapM fun path => do
    -- Lake's :shared facet writes beside the archive, so never return a peer path.
    let destination := pkg.staticLibDir / nameToStaticLib "leansqlite"
    IO.FS.createDirAll pkg.staticLibDir
    IO.FS.writeBinFile destination (← IO.FS.readBinFile path)
    return destination
target cryptoBinding pkg : FilePath := do
  let source ← inputTextFile {q(crypto / 'bindings/leancrypto.c')}
  buildO (pkg.buildDir / "cryptoBinding.o") source
    #["-I", (← getLeanIncludeDir).toString, "-I", {q(openssl / 'include')}]
    (traceArgs := #["-fPIC", "-std=c11", "-O2"]) (extraDepTrace := getLeanTrace)
extern_lib leancrypto pkg := do
  let object ← cryptoBinding.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leancrypto") #[object]

lean_lib SQLite where
  srcDir := {q(sqlite)}
  needs := #[leansqlite]
  precompileModules := true
lean_lib LeanCrypto where
  srcDir := {q(crypto)}
  needs := #[leancrypto]
lean_lib LeanDb where
  srcDir := {q(db)}
lean_lib LeanApi where
  srcDir := {q(root)}
'''
for lib, directory in (('LeanOntology', peer / 'engine'), ('LeanContract', peer / 'engine'),
                       ('LeanApp', peer / 'engine'), ('LeanReact', peer / 'engine'), ('LeanJS', peer / 'engine'), ('LeanApiDomain', root / 'adapters/domain'),
                       ('LeanDbDomain', db / 'adapters/domain'),
                       ('Tests', root / 'tests'), ('DomainChecks', root / 'adapters/domain/tests'),
                       ('Notes', root / 'examples/notes'),
                       ('PrivateGames', root / 'examples/private-games'),
                       ('PolicyView', root / 'examples/policy-view'),
                       ('Helpdesk', root / 'examples/helpdesk'), ('Billing', root / 'examples/billing'),
                       ('Scheduling', root / 'examples/scheduling'), ('TeamsDemo', root / 'examples/teams-demo')):
    name = 'AuthChecks' if lib == 'DomainChecks' else lib
    roots = f'`{name}, `ContractFixture' if lib == 'DomainChecks' else f'`{name}'
    globs = f'.one `{name}, .one `ContractFixture' if lib == 'DomainChecks' else f'.one `{name}, .submodules `{name}'
    config += f'''lean_lib {lib} where
  srcDir := {q(directory)}
  roots := #[{roots}]
  globs := #[{globs}]
'''
# The post-shaped portable fixture (`tests.domain.PostPart1`), when the peer has it.
if (peer / 'tests/domain/PostPart1.lean').is_file():
    config += f'''lean_lib LeanReactPostFixture where
  srcDir := {q(peer)}
  roots := #[`tests.domain.PostPart1]
lean_exe domain_post_app where
  srcDir := {q(root / 'adapters/domain/tests')}
  root := `PostApp
'''
# Fixture modules the check executables import (`PartifulBefore`).
config += f'''lean_lib DomainFixtures where
  srcDir := {q(root / 'adapters/domain/tests')}
  roots := #[`PartifulBefore]
'''
config += f'''lean_exe leanapi_tests where
  srcDir := {q(root / 'tests')}
  root := `Main
lean_exe domain_contract_checks where
  srcDir := {q(root / 'adapters/domain/tests')}
  root := `ContractChecks
lean_exe domain_prepared_checks where
  srcDir := {q(root / 'adapters/domain/tests')}
  root := `PreparedChecks
lean_exe domain_native_read_checks where
  srcDir := {q(root / 'adapters/domain/tests')}
  root := `NativeReadChecks
lean_exe domain_native_command_checks where
  srcDir := {q(root / 'adapters/domain/tests')}
  root := `NativeCommandsChecks
lean_exe domain_kdf_gate_checks where
  srcDir := {q(root / 'adapters/domain/tests')}
  root := `KDFGateChecks
lean_exe domain_route_checks where
  srcDir := {q(root / 'adapters/domain/tests')}
  root := `RouteChecks
lean_exe domain_migration_checks where
  srcDir := {q(root / 'adapters/domain/tests')}
  root := `MigrationChecks
lean_exe domain_library_app where
  srcDir := {q(root / 'adapters/domain/tests')}
  root := `LibraryApp
'''
# The generality fixture serves a LeanReact `App`; its bundle is a Lake target too.
if a.node_modules:
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from ddd_browser_target import browser_target
    config += browser_target('library_browser', 'domain_library_app', 'LibraryApp', root=root, peer=peer,
                             node_modules=a.node_modules.resolve(), args=['v2'])
(out / 'lakefile.lean').write_text(config)
(out / 'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
print(out)
