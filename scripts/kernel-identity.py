#!/usr/bin/env python3
"""Path-independent identity of a kernel build.

The build directory's absolute path enters the DWARF `comp_dir`, and through
it the GNU build IDs of `vmlinux` and of the vDSO image embedded in `.rodata`.
Code, data, symbols and configuration do not depend on it. This identity
hashes `.config`, `System.map` and the bytes of every loaded (SHF_ALLOC)
section of `vmlinux`, with each 20-byte NT_GNU_BUILD_ID descriptor zeroed.
Two builds of the same source, configuration and toolchain in different
directories have the same identity; any change to loaded code or data does not.

    scripts/in-bundle python3 scripts/kernel-identity.py BUILD_DIR
"""
import hashlib
from pathlib import Path
import re
import subprocess
import sys
import tempfile

# Elf64 note: namesz=4, descsz=20, type=3 (NT_GNU_BUILD_ID), "GNU\0", 20 bytes.
BUILD_ID_NOTE = re.compile(rb"\x04\x00\x00\x00\x14\x00\x00\x00\x03\x00\x00\x00GNU\x00(.{20})", re.S)


def sections(vmlinux):
    listing = subprocess.run(['readelf', '-S', '-W', str(vmlinux)], capture_output=True, text=True,
                             check=True).stdout
    names = []
    for line in listing.splitlines():
        match = re.match(r'\s*\[\s*\d+\]\s+(\S+)\s+(\S+)\s+\S+\s+\S+\s+\S+\s+\S+\s+(\S*)', line)
        if match and match.group(2) not in ('NULL', 'NOBITS') and 'A' in match.group(3):
            names.append(match.group(1))
    return names


def identity(build):
    build = Path(build)
    vmlinux = build / 'vmlinux'
    digest = hashlib.sha256()
    for name in ('.config', 'System.map'):
        data = (build / name).read_bytes()
        digest.update(f'{name}\0{len(data)}\0'.encode() + data)
    notes = 0
    with tempfile.TemporaryDirectory() as tmp:
        for name in sections(vmlinux):
            out = Path(tmp) / 'section.bin'
            subprocess.run(['objcopy', '-O', 'binary', f'--only-section={name}', str(vmlinux), str(out)], check=True)
            data = bytearray(out.read_bytes())
            for match in BUILD_ID_NOTE.finditer(bytes(data)):
                data[match.start(1):match.end(1)] = bytes(20)
                notes += 1
            digest.update(f'{name}\0{len(data)}\0'.encode() + bytes(data))
    if notes == 0:
        raise SystemExit('no GNU build-ID note found: unexpected kernel image layout')
    return digest.hexdigest(), notes


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    value, notes = identity(sys.argv[1])
    print(f'{value}  ({notes} build-ID notes zeroed)')
