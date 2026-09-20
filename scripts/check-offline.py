#!/usr/bin/env python3
"""Offline acceptance suite, launched by scripts/check-nono."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--only', choices=('isolation', 'toolchains', 'kernel', 'guest', 'syzkaller', 'syzkaller-program', 'lean-lsp', 'integrity'))
parser.add_argument('--kernel-build', type=Path, help='Optional build directory inside the repository')
args = parser.parse_args()
env = os.environ.copy()
if args.kernel_build:
    build = args.kernel_build.resolve()
    if not build.is_relative_to(ROOT / '.artifacts'):
        parser.error('kernel build directory must be inside .artifacts')
    env['LEANUX_KERNEL_BUILD'] = str(build)
out = ROOT / '.artifacts/nono-validation'
out.mkdir(parents=True, exist_ok=True)
checks = [
    ('isolation', ['python3', 'scripts/check-isolation.py'], 30),
    ('toolchains', ['python3', 'scripts/probe-toolchains.py'], 180),
    ('kernel', ['scripts/build-kernel'], 1200),
    ('guest', ['python3', 'scripts/check-guest.py'], 120),
    ('syzkaller', ['scripts/build-syzkaller'], 1200),
    ('syzkaller-program', ['python3', 'scripts/check-syzkaller.py'], 60),
    ('lean-lsp', ['scripts/lean-lsp-python', 'scripts/check-lean-lsp.py'], 90),
    ('integrity', ['python3', 'scripts/verify-dependencies.py'], 180),
]
records = []
for name, command, timeout in checks:
    if args.only and name != args.only:
        continue
    print(f'Checking {name} ...', flush=True)
    start = time.monotonic()
    with (out / f'{name}.log').open('w') as log:
        try:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=log,
                                    stderr=subprocess.STDOUT, timeout=timeout)
            code = result.returncode
        except subprocess.TimeoutExpired:
            code = 124
    record = {'check': name, 'command': command, 'exit_code': code,
              'seconds': round(time.monotonic() - start, 2),
              'checked_at_utc': datetime.now(timezone.utc).isoformat()}
    (out / f'{name}.json').write_text(json.dumps(record, indent=2) + '\n')
    records.append(record)
    print(('PASS' if code == 0 else 'FAIL') + f': {name} ({record["seconds"]}s)', flush=True)
    if code:
        print((out / f'{name}.log').read_text()[-6000:])
        raise SystemExit(code)
print('All requested nono checks passed.', flush=True)
