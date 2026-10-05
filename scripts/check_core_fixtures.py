#!/usr/bin/env python3
"""Compile-time rejections: every fixture under fixtures/core (LeanApi.Core) and fixtures/native
(LeanApi.Native) must FAIL to compile, with the message fragment its directory's
`expected.json` records for it. Also checks that the import closure of `LeanApi.Core` is
portable (`scripts/CoreClosure.lean`).
Usage (from the repository root, after `lake build LeanApiCore TestsCore TestsNative`):
  python3 scripts/check_core_fixtures.py
"""
import json
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
failures = []
total = 0
for directory in ('fixtures/core', 'fixtures/native'):
  expected = json.loads((root / directory / 'expected.json').read_text())
  total += len(expected)
  for name, fragment in sorted(expected.items()):
    result = subprocess.run(['lake', 'env', 'lean', f'{directory}/{name}.lean'], cwd=root,
                            capture_output=True, text=True)
    output = result.stdout + result.stderr
    if result.returncode == 0:
        failures.append(f'{name}: compiled, but must be rejected')
    elif 'unknown module' in output or 'bad import' in output or 'failed, environment already contains' in output:
        failures.append(f'{name}: rejected for the wrong reason (imports)\n{output}')
    elif fragment not in output:
        failures.append(f'{name}: rejected without "{fragment}"\n{output}')
    else:
        print(f'PASS rejected: {directory}/{name}')
  listed = {p.stem for p in (root / directory).glob('*.lean')}
  for name in sorted(listed - expected.keys()):
    failures.append(f'{directory}/{name}: fixture without an expected message')
closure = subprocess.run(['lake', 'env', 'lean', 'scripts/CoreClosure.lean'], cwd=root,
                         capture_output=True, text=True)
if closure.returncode != 0:
    failures.append(f'CoreClosure: {closure.stdout}{closure.stderr}')
else:
    print(closure.stdout.strip())
if failures:
    print('\n'.join('FAIL ' + f for f in failures), file=sys.stderr)
    sys.exit(1)
print(f'PASS: {total} compile-time rejections, portable closure')
