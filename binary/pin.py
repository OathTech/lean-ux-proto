"""Read-only check of the exact private Kraken dependency used by binary/."""
import json
from pathlib import Path
import re
import subprocess


def verify_pin(root):
    root = Path(root).resolve()
    locks = [x for x in json.loads((root / 'dependencies/sources.lock.json').read_text())
             if x['name'] == 'kraken']
    if len(locks) != 1:
        raise ValueError('expected one Kraken dependency lock')
    lock, = locks
    pins = re.findall(r'^def krakenCommit : String := "([0-9a-f]{40})"$',
                      (root / 'binary/TrustBase.lean').read_text(), re.M)
    if pins != [lock['commit']]:
        raise ValueError('TrustBase and dependency lock disagree on Kraken commit')
    if lock['toolchain'] != (root / 'binary/lean-toolchain').read_text().strip():
        raise ValueError('Kraken lock and binary toolchain disagree')
    dependencies = [x for x in json.loads((root / 'binary/lake-manifest.json').read_text())['packages']
                    if x['name'] == 'Kraken']
    if len(dependencies) != 1 or dependencies[0]['type'] != 'path':
        raise ValueError('binary must use its private path dependency for Kraken')
    private = root / '.deps/kraken'
    if private.resolve() != private or (root / 'binary' / dependencies[0]['dir']).resolve() != private:
        raise ValueError('Kraken path dependency does not resolve to the private checkout')
    def git(*args):
        return subprocess.check_output(['git', '-C', str(private), *args], text=True).strip()
    if Path(git('rev-parse', '--show-toplevel')).resolve() != private:
        raise ValueError('Kraken dependency is not a separate private Git checkout')
    actual = git('rev-parse', 'HEAD')
    if actual != lock['commit']:
        raise ValueError(f'Kraken HEAD {actual} differs from pinned {lock["commit"]}')
    dirty = git('status', '--porcelain=v1', '--untracked-files=normal')
    if dirty:
        raise ValueError(f'Kraken source tree is not clean:\n{dirty}')
    return actual
