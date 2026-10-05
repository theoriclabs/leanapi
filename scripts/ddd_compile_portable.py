#!/usr/bin/env python3
"""Compile peer portable sources serially into this repo, without mutating peer builds.
Developer-only checkout location is supplied by CLI, never by a release manifest.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess

p = argparse.ArgumentParser()
p.add_argument('source', type=Path, help='LeanReact engine directory')
p.add_argument('output', type=Path)
p.add_argument('modules', nargs='+')
p.add_argument('--lean', default='lean')
p.add_argument('--extra-root', type=Path, action='append', default=[])
p.add_argument('--search-path', type=Path, action='append', default=[])
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=True)
a.source = a.source.resolve()
a.output = a.output.resolve()
seen = set()
env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(a.output), *(str(x.resolve()) for x in a.search_path)]), LEAN_NUM_THREADS='2')

def build(module):
    if module in seen:
        return
    roots = [a.source, *(root.resolve() for root in a.extra_root)]
    found = next(((root, root / (module.replace('.', '/') + '.lean')) for root in roots
                  if (root / (module.replace('.', '/') + '.lean')).exists()), None)
    if found is None:
        return  # Toolchain-provided import.
    root, src = found
    source = src.read_text()
    for line in source.splitlines():
        match = re.match(r'^\s*(?:(?:public|meta|private)\s+)*import\s+(.+?)\s*$', line)
        if match:
            for dep in match[1].split():
                build(dep)
    out = a.output / (module.replace('.', '/') + '.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    print(module, flush=True)
    subprocess.run([a.lean, '-j', '2', '-R', str(root), '-o', str(out), str(src)],
                   env=env, check=True)
    seen.add(module)

for module in a.modules:
    build(module)
