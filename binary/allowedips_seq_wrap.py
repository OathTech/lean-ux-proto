#!/usr/bin/env python3
"""Execute the sequence-counter boundary witness on both compiled wrappers.

Run through capped from the worktree root. Exit 1 means the mirror and binary
counter differ; an infrastructure failure also fails noisily. These are labeled
constructed states, not kernel captures or claims of kernel-entry reachability.
The fixed mirror exposes the exact UInt64 value; the binary expectation is unchanged.
"""
import json
from pathlib import Path
import re
import subprocess

from census import extract
from layouts import layouts
from pin import verify_pin
from target import ROOT, ORACLE, verify_image


def prepare(destination: Path):
    verify_image()
    verify_pin(ROOT)
    names = ['wg_allowedips_insert_v4', 'wg_allowedips_insert_v6', 'add.isra.0',
             '__sanitizer_cov_trace_pc', '__sanitizer_cov_trace_cmp1', 'write_comp_data']
    functions = extract(ORACLE, names)
    selected = []
    for name in names:
        matches = [f for f in functions if f['name'] == name]
        if len(matches) != 1:
            raise ValueError(f'expected exactly one {name}')
        selected.append(matches[0])
    rows = [row for function in selected for row in function['instructions']]
    labels = {}
    for row in rows:
        if branch := re.fullmatch(r'(j\w+|call) L_([0-9a-f]+)', row['normalized']):
            raw = bytes.fromhex(row['bytes'])
            width = 1 if len(raw) == 2 else 4
            target = int(branch[2], 16)
            if (row['pc'] + len(raw) + int.from_bytes(raw[-width:], 'little', signed=True)) % 2**64 != target:
                raise ValueError(f'branch displacement differs at {row["pc"]:x}')
            labels['L_' + branch[2]] = target
    pc_callback = selected[3]
    reads = [row for row in pc_callback['instructions'] if '<pcpu_hot+0x8>' in row['asm']]
    if len(reads) != 1:
        raise ValueError('expected one coverage preempt-count read')
    address = re.search(r'#\s+([0-9a-f]+)', reads[0]['asm'])
    if address is None:
        raise ValueError('missing coverage preempt-count address')
    layout = layouts(ORACLE)
    data = dict(
        seqOffset=layout['allowedips']['members']['seq'],
        peerListOffset=layout['wg_peer']['members']['allowedips_list'],
        instructions=[dict(pc=row['pc'], size=len(bytes.fromhex(row['bytes'])),
                           asm=row['normalized']) for row in rows],
        labels=list(labels.items()),
        hooks=[(f['entry'], f['name']) for f in selected if f['name'].startswith('__sanitizer')],
        entries=[f['entry'] for f in selected[:2]], preempt=int(address[1], 16))
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(data) + '\n')


def main():
    path = ROOT / '.tmp/allowedips/seq-wrap.json'
    prepare(path)
    subprocess.run(['lake', 'build', 'binary-allowedips-seq-wrap'], cwd=ROOT/'binary', check=True)
    return subprocess.run([str(ROOT/'binary/.lake/build/bin/binary-allowedips-seq-wrap'), str(path)]).returncode


if __name__ == '__main__':
    raise SystemExit(main())
