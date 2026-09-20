#!/usr/bin/env python3
"""Check local build paths and full network blocking in the nono test profile.

Run via scripts/check-nono. The normal agent profile may allow API connections;
scripts/in-bundle itself does not enforce network or filesystem confinement.
"""
import errno
import os
from pathlib import Path
import socket
import subprocess
import sys

root = Path(os.environ['LEANUX_ROOT']).resolve()
shared = Path(os.environ['LEANUX_SHARED_ROOT']).resolve()
assert Path(sys.executable).resolve().is_relative_to(shared / '.tools'), sys.executable
for name in ('TMPDIR', 'XDG_CACHE_HOME', 'ELAN_HOME', 'LAKE_CACHE_DIR',
             'LAKE_CONFIG', 'GOPATH', 'GOMODCACHE', 'GOCACHE'):
    assert Path(os.environ[name]).resolve().is_relative_to(shared), name
for compiler, language in (('gcc', 'c'), ('g++', 'c++'), ('clang', 'c')):
    result = subprocess.run([compiler, '-E', '-x', language, '-v', '-'],
                            input='', text=True, capture_output=True, check=True)
    search = result.stderr.split('#include <...> search starts here:\n', 1)[1]
    search = search.split('End of search list.', 1)[0]
    paths = [Path(line.strip()).resolve() for line in search.splitlines() if line.strip()]
    assert paths and all(path.is_relative_to(shared / '.tools') for path in paths), (compiler, paths)
perl_module = subprocess.check_output(['perl', '-Mstrict', '-e', 'print $INC{"strict.pm"}'], text=True)
assert Path(perl_module).resolve().is_relative_to(shared / '.tools'), perl_module
for family in (socket.AF_INET, socket.AF_INET6):
    for kind in (socket.SOCK_STREAM, socket.SOCK_DGRAM):
        try:
            with socket.socket(family, kind):
                pass
        except OSError as exc:
            assert exc.errno in (errno.EPERM, errno.EACCES), exc
        else:
            raise AssertionError('Socket creation allowed; use scripts/check-nono for this test')
print('PASS: build paths and compiler headers stay local; staged Python/Perl modules selected.')
print('PASS: IPv4/IPv6 TCP/UDP socket creation is denied.')
