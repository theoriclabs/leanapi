#!/usr/bin/env python3
"""Run the peer compiler corpus/parity gate without writing into the peer repo."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess

p = argparse.ArgumentParser()
p.add_argument('peer', type=Path)
p.add_argument('portable', type=Path)
p.add_argument('scratch', type=Path)
p.add_argument('--lean', default='lean')
p.add_argument('--node-modules', type=Path, help='Installed parser dependencies (defaults to PEER/node_modules)')
a = p.parse_args()
a.peer, a.portable, a.scratch = (x.resolve() for x in (a.peer, a.portable, a.scratch))
fixtures = a.scratch / 'tests/compiler'
fixtures.mkdir(parents=True, exist_ok=True)
# Reuse the already-installed parser dependency; do not install/copy a dependency tree.
node_modules = (a.node_modules or a.peer / 'node_modules').resolve()
link = a.scratch / 'node_modules'
if node_modules.is_dir() and not link.exists():
    link.symlink_to(node_modules, target_is_directory=True)
for source in (a.peer / 'tests/compiler').iterdir():
    if source.is_file() and source.suffix in ('.lean', '.mjs'):
        shutil.copyfile(source, fixtures / source.name)
output = a.portable / 'tests/compiler'
output.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, LEAN_PATH=str(a.portable), LEAN_NUM_THREADS='2')

def lean(name, *args):
    cmd = [a.lean, '-j', '2', *args, str(fixtures / (name + '.lean'))]
    print(' '.join(cmd), flush=True)
    return subprocess.run(cmd, env=env, cwd=a.scratch, check=True)

for name in ('Corpus', 'ProofFields'):
    lean(name, '-R', str(a.scratch), '-o', str(output / (name + '.olean')))
for name in ('Generate', 'GenerateProofFields', 'Deterministic', 'Negative', 'Modules', 'Hooks'):
    lean(name)
artifacts = ['generated.mjs', 'generated.d.ts', 'generated.d.mts', 'generated.manifest.json']
before = {name: (fixtures / name).read_bytes() for name in artifacts}
lean('Generate')
assert all((fixtures / name).read_bytes() == value for name, value in before.items())
with (fixtures / 'native.json').open('w') as out:
    subprocess.run([a.lean, '-j', '2', '--run', str(fixtures / 'Native.lean')],
                   cwd=a.scratch, env=env, stdout=out, check=True)
subprocess.run(['node', '--check', str(fixtures / 'generated.mjs')], check=True)
subprocess.run(['node', '--test', str(fixtures / 'compiler.test.mjs')], cwd=a.scratch, check=True)
print('PASS: isolated LeanJS compiler, negative fixtures, deterministic generation, native/JS parity')
