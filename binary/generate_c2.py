#!/usr/bin/env python3
"""Result C2: emit the replay-window range of wg_packet_rx_poll (pinned s5 image) as
Lean terms, binary/C2Image.lean.

The range is [START, DONE): counter_validate as inlined, from the load of the packet
counter to the instruction after `setb %bpl`: 70 instructions, among them
`bts %r15,(%rax)` at BTS, which Kraken expresses from its tenth patch on.

Checked here: the ELF sha256 pin (target.verify_image); every objdump byte row against the
ELF's .text bytes; every direct branch's rel8/rel32 encoding against its printed target;
the bytes and text of the `bts`; that no instruction in the range carries a
LOCK prefix. The two 8-byte comparison callbacks the range calls are five-instruction
entries that jump to the shared body `write_comp_data`, whose terms the landed
ServiceImage already holds; their ten instructions are emitted here as well.
Also checked, as facts about the ELF and not as Lean premises: no `.altinstructions` entry
patches a byte of the range, of the two entries or of the callback bodies; `.smp_locks`
is empty; the image has no `__jump_table`, `.retpoline_sites`, `.return_sites`,
`.call_sites` or `.parainstructions` section. Trusted: objdump's disassembly text, census.normalize, Kraken's AT&T parser.
Run from the worktree root with a python3 that has pyelftools:
    python3 -B binary/generate_c2.py [--check]
"""
import re
import struct
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from census import normalize          # noqa: E402
from target import ORACLE, verify_image  # noqa: E402
from elftools.elf.elffile import ELFFile  # noqa: E402

FUNCTION = 'wg_packet_rx_poll'
START, BTS, DONE = 0xffffffff8139d2a6, 0xffffffff8139d3dd, 0xffffffff8139d3ea
BTS_BYTES, BTS_TEXT = bytes.fromhex('4c0fab38'), 'bts    %r15,(%rax)'
REJECT_WINDOW, REJECT_LIMIT = 0xffffffff8139d80d, 0xffffffff8139d9c3


STUBS = {'cmp8': ('__sanitizer_cov_trace_cmp8', 0xffffffff810f40a0),
         'constCmp8': ('__sanitizer_cov_trace_const_cmp8', 0xffffffff810f4120)}
WRITE_COMP_DATA = 0xffffffff810f3fb0


def disassemble(symbol, low, high):
    out = subprocess.run(['objdump', '-d', '-w', f'--disassemble={symbol}', str(ORACLE)],
                         text=True, capture_output=True, check=True).stdout
    rows = []
    for line in out.splitlines():
        m = re.match(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)\s*(\S.*)$', line)
        if m and low <= int(m[1], 16) < high:
            rows.append(dict(pc=int(m[1], 16), raw=bytes.fromhex(m[2]), text=m[3].strip()))
    return rows


def main():
    verify_image()
    rows = disassemble(FUNCTION, START, DONE)
    assert rows[0]['pc'] == START and rows[-1]['pc'] + len(rows[-1]['raw']) == DONE
    with ORACLE.open('rb') as f:
        text = ELFFile(f).get_section_by_name('.text')
        base, data = text['sh_addr'], text.data()
    patchable = [(START, DONE), (0xffffffff810f31f0, 0xffffffff810f3250), (WRITE_COMP_DATA, 0xffffffff810f4140)]
    with ORACLE.open('rb') as f:
        elf = ELFFile(f)
        alt = elf.get_section_by_name('.altinstructions')
        alt_base, alt_data = alt['sh_addr'], alt.data()
        if len(alt_data) % 14:
            raise ValueError('unexpected .altinstructions entry size')
        for i in range(0, len(alt_data), 14):
            site = (alt_base + i + struct.unpack_from('<i', alt_data, i)[0]) % 2**64
            for k in range(max(alt_data[i + 12], 1)):
                if any(low <= site + k < high for low, high in patchable):
                    raise ValueError(f'alternatives entry patches {site:x}')
        if elf.get_section_by_name('.smp_locks')['sh_size'] != 0:
            raise ValueError('.smp_locks is not empty')
        for name in ['__jump_table', '.retpoline_sites', '.return_sites', '.call_sites', '.parainstructions']:
            if elf.get_section_by_name(name) is not None:
                raise ValueError(f'the image has a {name} section; check the range against it')
    targets = set()
    for row in rows:
        raw = row['raw']
        if data[row['pc'] - base: row['pc'] - base + len(raw)] != raw:
            raise ValueError(f'objdump bytes differ from ELF at {row["pc"]:x}')
        if 'lock' in row['text'] or raw[0] == 0xf0:
            raise ValueError(f'LOCK prefix in the range at {row["pc"]:x}')
        if row['pc'] == BTS:
            if raw != BTS_BYTES or row['text'] != BTS_TEXT:
                raise ValueError('the instruction at BTS is not the expected bts')
        row['asm'] = normalize(row['text'])
        if branch := re.fullmatch(r'(j\w+|call) L_([0-9a-f]+)', row['asm']):
            target = int(branch[2], 16)
            width = 1 if len(raw) == 2 else 4
            actual = (row['pc'] + len(raw) + int.from_bytes(raw[-width:], 'little', signed=True)) % 2**64
            if actual != target:
                raise ValueError(f'branch encoding differs at {row["pc"]:x}')
            targets.add((branch[1], target))
    leaving = sorted({t for kind, t in targets if kind != "call" and not START <= t < DONE})
    if leaving != [REJECT_WINDOW, REJECT_LIMIT]:
        raise ValueError(f'unexpected exits: {[hex(t) for t in leaving]}')
    callees = sorted({t for kind, t in targets if kind == 'call'})
    if callees != sorted([0xffffffff810f31f0] + [a for _, a in STUBS.values()]):
        raise ValueError(f'unexpected callees: {[hex(c) for c in callees]}')
    stubs = {}
    for name, (symbol, address) in STUBS.items():
        part = disassemble(symbol, address, address + 20)
        if [len(r['raw']) for r in part] != [4, 3, 3, 5, 5] or part[0]['pc'] != address:
            raise ValueError(f'{symbol} is not the expected five-instruction entry')
        for r in part:
            if data[r['pc'] - base: r['pc'] - base + len(r['raw'])] != r['raw']:
                raise ValueError(f'objdump bytes differ from ELF at {r["pc"]:x}')
            r['asm'] = normalize(r['text'])
        last = part[-1]
        if (last['pc'] + 5 + int.from_bytes(last['raw'][-4:], 'little', signed=True)) % 2**64 != WRITE_COMP_DATA \
                or last['asm'] != f'jmp L_{WRITE_COMP_DATA:016x}':
            raise ValueError(f'{symbol} does not end in a jump to write_comp_data')
        stubs[name] = part
    if len(rows) != 70:
        raise ValueError(f'the range has {len(rows)} instructions, not 70')

    def block(name, part):
        asm = '\n'.join(r['asm'] for r in part)
        sizes = ', '.join(str(len(r['raw'])) for r in part)
        return [f'def {name} : List (Kraken.Sized Directive) :=',
                f'  List.zipWith (fun d n => ⟨d, n⟩) (parse("{asm}")) [{sizes}]']

    image = ['import Image', 'open Kraken.X64.Parser', 'namespace Binary.C2.Range',
             '-- Generated by binary/generate_c2.py from the pinned s5 ELF; no instruction substitution.',
             f'-- counter_validate inlined in {FUNCTION}: [{START:#x}, {DONE:#x}).',
             f'-- 70 instructions, `bts %r15,(%rax)` (4c 0f ab 38) at {BTS:#x} among them.',
             f'def entry : Int64 := .ofNat {START}',
             f'def donePC : Int64 := .ofNat {DONE}',
             f'def rejectWindowPC : Int64 := .ofNat {REJECT_WINDOW}',
             f'def rejectLimitPC : Int64 := .ofNat {REJECT_LIMIT}',
             'def callees : List Int64 := [' + ', '.join(f'.ofNat {c}' for c in callees) + ']',
             f'def count : Nat := {len(rows)}']
    image += block('code', rows)
    for name, (symbol, address) in STUBS.items():
        image += [f'def {name}Entry : Int64 := .ofNat {address}  -- {symbol}'] + block(f'{name}Stub', stubs[name])
    image += ['/-- The literal instructions of the range and of the two callback entries. -/',
              'def fetch (pc : Int64) : Option Binary.Decoded :=',
              '  ((Binary.Image.fetchIn entry code pc).orElse fun _ =>',
              '    (Binary.Image.fetchIn cmp8Entry cmp8Stub pc).orElse fun _ =>',
              '    Binary.Image.fetchIn constCmp8Entry constCmp8Stub pc)',
              'end Binary.C2.Range', '']
    rendered = '\n'.join(image)
    path = HERE / 'C2Image.lean'
    if '--check' in sys.argv[1:]:
        if path.read_text() != rendered:
            raise SystemExit('C2Image.lean differs from the pinned ELF')
        print('C2Image.lean matches the pinned ELF')
    else:
        path.write_text(rendered)
    calls = sum(1 for r in rows if r.get('asm', '').startswith('call'))
    print(f'{len(rows)} instructions, {DONE - START} bytes, {calls} call sites, '
          f'callees {[hex(c) for c in callees]}')


if __name__ == '__main__':
    main()
