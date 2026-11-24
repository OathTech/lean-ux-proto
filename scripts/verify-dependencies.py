#!/usr/bin/env python3
"""Check the staged inputs that the project's results rest on, without network access.

A required input is one a build or a check consumes: the locked tool packages
(compiler, QEMU, kernel build tools), the locked Linux source archive and the
Lean toolchain. Each is identified by something anyone can reproduce from a
public source: an archive by its URL and SHA-256, Lean by the version and
commit its own `lean --version` reports. A required row without a public
origin is refused. What the builds produce is checked where it is used: the
kernel by its path-independent identity at every boot (harness/linux.py), the
binary package's Kraken by its commit (binary/pin.py).

Reference pages and other optional downloads are listed as present or absent
and are never a condition: a hash of a live web page is not reproducible, and
no build reads them.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
def shared_root():
    """Staged inputs live in the original clone; a `git worktree` checkout shares them."""
    if 'LEANUX_SHARED_ROOT' in os.environ:
        return Path(os.environ['LEANUX_SHARED_ROOT'])
    if (ROOT / '.git').is_file():
        common = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', '--path-format=absolute', '--git-common-dir'],
                                capture_output=True, text=True, check=True).stdout.strip()
        return Path(common).parent
    return ROOT


SHARED = shared_root()
REQUIRED_SOURCES = {'linux'}
failures = []


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def archive(label, relative, row):
    if not str(row.get('url', '')).startswith('https://') or not re.fullmatch(r'[0-9a-f]{64}', row.get('sha256', '')):
        failures.append(f'{label}: the lock row has no public URL and SHA-256')
        return False
    path = SHARED / relative
    if not path.is_file():
        failures.append(f'{label}: missing {relative} (from {row["url"]})')
        return False
    if digest(path) != row['sha256']:
        failures.append(f'{label}: checksum mismatch: {relative}')
        return False
    return True


packages = json.loads((ROOT / 'dependencies/packages.lock.json').read_text())
good = sum(archive(f'package {row["name"]}', '.deps/downloads/debs/' + row['filename'], row) for row in packages)
print(f'tool packages: {good} of {len(packages)} verified')

optional = []
for row in json.loads((ROOT / 'dependencies/sources.lock.json').read_text()):
    if row['name'] in REQUIRED_SOURCES:
        if archive(f'source {row["name"]}', row['archive'], row):
            print(f'source {row["name"]}: verified')
    elif row.get('kind') == 'git':
        print(f'source {row["name"]}: a git pin at {row["commit"]}, checked by its consumer ({row.get("consumer", "none")})')
    else:
        optional.append((row['name'], row['archive']))

declared = (ROOT / 'lean-toolchain').read_text().strip()
pins = [row for row in json.loads((ROOT / 'dependencies/toolchains.lock.json').read_text())
        if row['name'] == 'lean' and row['toolchain'] == declared]
# Under scripts/in-bundle the launcher has already selected the toolchain and put it first on PATH;
# elsewhere ask elan for the declared toolchain. An unversioned `lean` is never trusted by name.
elan = shutil.which('elan') or str(Path(os.environ.get('ELAN_HOME') or Path.home() / '.elan') / 'bin/elan')
if os.environ.get('LEANUX_ROOT') == str(ROOT):
    command = ['lean', '--version']
elif Path(elan).is_file():
    command = [elan, 'run', declared, 'lean', '--version']
else:
    command = None
if len(pins) != 1:
    failures.append(f'lean: dependencies/toolchains.lock.json needs exactly one row for {declared}')
elif command is None:
    failures.append(f'lean: elan is not installed; install it, then: {pins[0]["install"]}')
else:
    probe = subprocess.run(command, capture_output=True, text=True)
    wanted = (f'version {pins[0]["version"]},', f'commit {pins[0]["commit"]},')
    if probe.returncode != 0 or not all(part in probe.stdout for part in wanted):
        failures.append(f'lean: {declared} is not installed at version {pins[0]["version"]}, commit '
                        f'{pins[0]["commit"]}; {pins[0]["install"]}')
    else:
        print(f'lean: {declared}, commit {pins[0]["commit"]}')

for name in ('documentation', 'lean-manual'):
    rows = json.loads((ROOT / f'dependencies/{name}.lock.json').read_text())
    present = sum((SHARED / row['path']).is_file() for row in rows)
    print(f'optional {name}: {present} of {len(rows)} present (not checked)')
for name, relative in optional:
    print(f'optional source {name}: {"present" if (SHARED / relative).is_file() else "absent"} (not checked)')

if failures:
    for line in failures:
        print(f'FAIL: {line}', file=sys.stderr)
    raise SystemExit(1)
print('PASS: every required input is present and matches its public pin.')
