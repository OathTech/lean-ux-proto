"""Finite RAM observation for C2; not an implementation of Lean EqualOutside.

Snapshots use the archive's page-delta format, with strict size/index checks.
The virtual reader observes kernel addresses through a captured CR3. A physical
footprint comparison is reported separately from virtual-address aliases.
"""
from pathlib import Path
import struct
import zlib

PAGE = 4096
IMAGE_BASE = 0xffffffff80000000
DIRECT_MAP = 0xffff888000000000
ADDRESS = 0x000ffffffffff000


class Writer:
    def __init__(self, directory, ram_bytes):
        self.directory = Path(directory)
        self.directory.mkdir()
        if ram_bytes <= 0 or ram_bytes % PAGE:
            raise ValueError('RAM size must be a positive multiple of a page')
        self.ram_bytes, self.previous, self.count = ram_bytes, None, 0

    def add(self, data):
        if len(data) != self.ram_bytes:
            raise ValueError('short physical RAM image')
        view = memoryview(data)
        if self.previous is None:
            pages = list(range(len(data) // PAGE))
        else:
            before = memoryview(self.previous)
            pages = []
            for block in range(0, len(data), 64 * PAGE):
                if before[block:block + 64 * PAGE] != view[block:block + 64 * PAGE]:
                    pages.extend(p // PAGE for p in range(block, min(block + 64 * PAGE, len(data)), PAGE)
                                 if before[p:p + PAGE] != view[p:p + PAGE])
        raw = struct.pack(f'<I{len(pages)}I', len(pages), *pages)
        raw += b''.join(view[p * PAGE:(p + 1) * PAGE] for p in pages)
        index = self.count
        (self.directory / f'{index:06d}.z').write_bytes(zlib.compress(raw, 1))
        self.previous, self.count = data, index + 1
        return index


def images(directory, ram_bytes, count):
    directory = Path(directory)
    wanted = [f'{i:06d}.z' for i in range(count)]
    if sorted(p.name for p in directory.glob('*.z')) != wanted:
        raise ValueError('missing or extra RAM snapshot')
    memory = bytearray(ram_bytes)
    for index, name in enumerate(wanted):
        raw = zlib.decompress((directory / name).read_bytes())
        if len(raw) < 4:
            raise ValueError('truncated snapshot header')
        n, = struct.unpack_from('<I', raw)
        if n > ram_bytes // PAGE or len(raw) != 4 + n * (4 + PAGE):
            raise ValueError('snapshot size disagrees with page count')
        pages = struct.unpack_from(f'<{n}I', raw, 4)
        if len(set(pages)) != n or any(p >= ram_bytes // PAGE for p in pages):
            raise ValueError('duplicate or out-of-RAM snapshot page')
        if index == 0 and tuple(range(ram_bytes // PAGE)) != pages:
            raise ValueError('snapshot zero is not complete RAM')
        offset = 4 + 4 * n
        for i, p in enumerate(pages):
            memory[p * PAGE:(p + 1) * PAGE] = raw[offset + i * PAGE:offset + (i + 1) * PAGE]
        yield bytes(memory)


def physical(memory, address, size):
    if address < 0 or size < 0 or address + size > len(memory):
        raise ValueError('physical read outside captured RAM')
    return memory[address:address + size]


def translate(memory, top, address):
    if not 0 <= address < 2**64 or address >> 47 != 0x1ffff:
        raise ValueError('only canonical kernel virtual addresses are observed')
    table = top
    for shift in (39, 30, 21, 12):
        entry = int.from_bytes(physical(memory, table + ((address >> shift) & 511) * 8, 8), 'little')
        if not entry & 1:
            raise ValueError(f'unmapped virtual address {address:#x}')
        if shift in (30, 21) and entry & 128:
            mask = (1 << shift) - 1
            return (entry & ADDRESS & ~mask) | (address & mask)
        table = entry & ADDRESS
    return table | (address & 4095)


def read(memory, top, address, size):
    result = bytearray()
    while size:
        chunk = min(size, PAGE - address % PAGE)
        result.extend(physical(memory, translate(memory, top, address), chunk))
        address, size = address + chunk, size - chunk
    return bytes(result)


def changed_runs(before, after):
    if len(before) != len(after) or len(before) % PAGE:
        raise ValueError('RAM image lengths differ or are not page aligned')
    a, b = memoryview(before), memoryview(after)
    for base in range(0, len(before), PAGE):
        if a[base:base + PAGE] == b[base:base + PAGE]:
            continue
        i = base
        while i < base + PAGE:
            if before[i] == after[i]:
                i += 1
                continue
            start = i
            while i < base + PAGE and before[i] != after[i]:
                i += 1
            yield start, i - start
