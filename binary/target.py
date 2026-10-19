"""The binary experiment's s4 target; never infer it from the main oracle."""
import hashlib
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
_COMMON = Path(subprocess.check_output(
    ['git', '-C', str(ROOT), 'rev-parse', '--path-format=absolute', '--git-common-dir'],
    text=True).strip()).parent
ORACLE = Path(os.environ.get('LEANUX_BINARY_KERNEL_DIR',
                            _COMMON / '.artifacts/kernel-net-choice-s4')).resolve() / 'vmlinux'
IDENTITY_FILE = ROOT / 'binary/kernel-identity-s4.txt'


def pins():
    values = [line.strip() for line in IDENTITY_FILE.read_text().splitlines()
              if line.strip() and not line.startswith('#')]
    if len(values) != 2 or any(len(s) != 64 or any(c not in '0123456789abcdef' for c in s)
                               for s in values):
        raise ValueError('invalid binary target identity file')
    return tuple(values)


def verify_image():
    with ORACLE.open('rb') as image:
        actual = hashlib.file_digest(image, 'sha256').hexdigest()
    if actual != pins()[1]:
        raise ValueError(f'binary target ELF hash mismatch: {ORACLE} is {actual}')
    return actual


def kernel_environment():
    verify_image()
    return dict(os.environ, LEANUX_KERNEL_DIR=str(ORACLE.parent),
                LEANUX_KERNEL_IDENTITY=pins()[0])
