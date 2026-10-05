#!/usr/bin/env python3
"""Create an ignored local validation workspace; no dependency checkout or peer writes."""
import argparse
import json
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument('peer', type=Path)
p.add_argument('--output', type=Path, default=Path('.lake/ddd-native'))
a = p.parse_args()
root = Path.cwd().resolve()
peer = a.peer.resolve()
out = a.output.resolve()
assert (root / 'LeanApi.lean').is_file()
assert (peer / 'engine/LeanContract/Http.lean').is_file()
assert out.is_relative_to(root / '.lake'), 'Validation config must remain ignored in this repo'
out.mkdir(parents=True, exist_ok=True)
q = lambda path: json.dumps(str(path))
config = f'''import Lake
open Lake DSL
package domain_checks where
  packagesDir := {q(root / '.lake/packages')}
require leanapi from {q(root)}
'''
for lib in ('LeanOntology', 'LeanContract', 'LeanApp'):
    config += f'lean_lib {lib} where\n  srcDir := {q(peer / "engine")}\n'
config += f'''lean_lib LeanApiDomain where
  srcDir := {q(root / 'adapters/domain')}
  roots := #[`LeanApiDomain]
  globs := #[.one `LeanApiDomain, .submodules `LeanApiDomain]
lean_lib DomainChecks where
  srcDir := {q(root / 'adapters/domain/tests')}
  roots := #[`AuthChecks, `ContractFixture]
  globs := #[.one `AuthChecks, .one `ContractFixture]
lean_exe domain_contract_checks where
  srcDir := {q(root / 'adapters/domain/tests')}
  root := `ContractChecks
'''
(out / 'lakefile.lean').write_text(config)
(out / 'lean-toolchain').write_bytes((root / 'lean-toolchain').read_bytes())
print(out)
