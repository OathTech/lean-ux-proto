"""Bind reported KCOV PCs to DWARF locations in the accepted Linux image."""
import hashlib
from pathlib import Path
import subprocess


def symbolize(rows, kernel):
    kernel = Path(kernel)
    addresses = sorted({pc for row in rows for pc in row['pcs']})
    if not addresses or any(int(pc, 16) == 0 for pc in addresses):
        raise ValueError('missing or invalid coverage addresses')
    # KCOV records the instruction following the instrumentation call.
    query = ''.join(hex(int(pc, 16) - 1) + '\n' for pc in addresses).encode()
    process = subprocess.run(['addr2line', '-e', kernel, '-a', '-f', '-i'], input=query,
                             capture_output=True, timeout=60, check=True)
    records, current = {}, None
    lines = process.stdout.decode().splitlines()
    index = 0
    while index < len(lines):
        if lines[index].startswith('0x'):
            current = f'0x{int(lines[index], 16) + 1:016x}'
            records[current] = []
            index += 1
        elif current is not None and index + 1 < len(lines):
            records[current].append(dict(function=lines[index], source=lines[index + 1]))
            index += 2
        else:
            raise ValueError('malformed coverage symbolization output')
    if set(records) != set(addresses) or any(not stack or all(frame['source'].startswith('??') for frame in stack)
                                            for stack in records.values()):
        raise ValueError('coverage address does not resolve in accepted kernel')
    return dict(kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
                convention='KCOV return PC minus one; DWARF inline frames',
                unique_pcs=len(addresses), locations=records)
