"""The binary experiment's s5 target; never infer it from the main oracle."""
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
_COMMON = Path(subprocess.check_output(
    ['git', '-C', str(ROOT), 'rev-parse', '--path-format=absolute', '--git-common-dir'],
    text=True).strip()).parent
ORACLE = Path(os.environ.get('LEANUX_BINARY_KERNEL_DIR',
                            _COMMON / '.artifacts/kernel-net-choice-s5')).resolve() / 'vmlinux'
IDENTITY_FILE = ROOT / 'binary/kernel-identity-s5.txt'


def pins():
    """The pinned path-independent identity of the target image, as a one-element tuple."""
    values = [line.strip() for line in IDENTITY_FILE.read_text().splitlines()
              if line.strip() and not line.startswith('#')]
    if len(values) != 1 or any(len(s) != 64 or any(c not in '0123456789abcdef' for c in s)
                               for s in values):
        raise ValueError('invalid binary target identity file')
    return tuple(values)


def verify_image():
    """Refuse an image whose path-independent identity (scripts/kernel-identity.py: the
    configuration, the symbol map and every loaded section, build IDs zeroed) is not the pinned
    one. A build of the pinned source, configuration and tools in any directory passes; the
    file's own SHA-256 depends on the build directory and identifies nothing more."""
    out = subprocess.check_output(
        [sys.executable, str(ROOT / 'scripts/kernel-identity.py'), str(ORACLE.parent)], text=True)
    actual = out.split()[0] if out.split() else ''
    if actual != pins()[0]:
        raise ValueError(f'binary target identity mismatch: {ORACLE.parent} is {actual or out!r}')
    return actual


def kernel_environment():
    verify_image()
    return dict(os.environ, LEANUX_KERNEL_DIR=str(ORACLE.parent),
                LEANUX_KERNEL_IDENTITY=pins()[0])
