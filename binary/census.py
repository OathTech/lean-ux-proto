#!/usr/bin/env python3
"""Rebuild the WireGuard instruction census from the pinned ELF and Kraken parser.

No opcode whitelist stands in for a parser test. Full symbol extents include
their inline code; addr2line -i supplies inline attribution for every instruction.
Outputs are ephemeral, under .tmp/binary-tv by default.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ORACLE = ROOT.parents[1] / '.artifacts/kernel-net-choice-s4/vmlinux'


def run(*args, **kw):
    result = subprocess.run(args, text=True, capture_output=True, check=True, **kw)
    if result.stderr.strip():
        raise RuntimeError(f'{args[0]} emitted unexpected diagnostics: {result.stderr}')
    return result.stdout


def frames(kernel, pcs):
    lines = run('addr2line', '-e', str(kernel), '-a', '-f', '-i',
                input=''.join(f'{p:x}\n' for p in pcs)).splitlines()
    result, pc = {}, None
    i = 0
    while i < len(lines):
        if lines[i].startswith('0x'):
            pc = int(lines[i], 16)
            result[pc] = []
            i += 1
        else:
            assert pc is not None and i + 1 < len(lines), lines[i:]
            result[pc].append([lines[i], lines[i + 1]])
            i += 2
    assert set(result) == set(pcs)
    return result


def normalize(asm):
    """Presentation only. No unsupported opcode is substituted with a no-op."""
    asm = asm.split('#')[0].strip()
    asm = re.sub(r'\s+<[^>]+>', '', asm)
    # Numeric direct branches become labels; the real layout resolves them.
    asm = re.sub(r'^(j\w+|callq?)\s+([0-9a-f]{8,})$', r'\1 L_\2', asm)
    return asm


def extract(kernel, extra_names=()):
    config = json.loads((ROOT / 'correspondence/kcov.json').read_text())
    names = set(config['functions']) | set(extra_names)
    sizes = {}
    for row in run('nm', '-S', '--defined-only', str(kernel)).splitlines():
        cols = row.split()
        if len(cols) == 4:
            sizes[(int(cols[0], 16), cols[3])] = int(cols[1], 16)
    listing = run('objdump', '-d', '-w', str(kernel))
    functions, current = [], None
    for line in listing.splitlines():
        m = re.match(r'^([0-9a-f]+) <(.+)>:$', line)
        if m:
            addr, name = int(m[1], 16), m[2]
            base = name.split('.')[0]
            current = dict(name=name, base=base, entry=addr, instructions=[]) if base in names else None
            if current is not None:
                functions.append(current)
        elif current is not None:
            m = re.match(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)\s*(\S.*)$', line)
            if m:
                current['instructions'].append(dict(pc=int(m[1], 16), bytes=m[2].strip(), asm=m[3]))
    for f in functions:
        size = sizes[(f['entry'], f['name'])]
        assert size > 0, f['name']
        f['size'] = size
        f['instructions'] = [i for i in f['instructions'] if i['pc'] < f['entry'] + size]
    locations = frames(kernel, [i['pc'] for f in functions for i in f['instructions']])
    # Also include a listed non-WG caller if any of its inline frames is WG.
    functions = [f for f in functions if f['name'] in extra_names or any('/wireguard/' in src
                 for i in f['instructions'] for _, src in locations[i['pc']])]
    for f in functions:
        for i in f['instructions']:
            i['frames'] = locations[i['pc']]
            i['normalized'] = normalize(i['asm'])
    return functions


def census(kernel, out):
    out.mkdir(parents=True, exist_ok=True)
    functions = extract(kernel)
    spellings = sorted({i['normalized'] for f in functions for i in f['instructions']})
    source = out / 'instructions.txt'
    source.write_text('\n'.join(spellings) + '\n')
    rows = [json.loads(s) for s in run(str(ROOT / 'binary/.lake/build/bin/binary-probe'),
                                    'parse', str(source)).splitlines()]
    assert len(rows) == len(spellings)
    parsed = {r['asm']: r for r in rows}
    total = Counter()
    table = ['| Function (splits separate) | Instructions | Supported | Shallow | Deep | KCOV transfers | First blocker |',
             '| --- | ---: | ---: | ---: | ---: | ---: | --- |']
    for f in functions:
        counts = Counter()
        blocker = '—'
        pcs = {i['pc'] for i in f['instructions']}
        leaders = {f['entry']}
        for i in f['instructions']:
            a = i['normalized']
            p = parsed[a]
            deep = bool(re.search(r'%[fg]s:|\b(swapgs|cli|sti|popf\w*|pushf\w*|rdmsr|wrmsr|iret\w*)\b', a))
            kind = 'supported' if p['ok'] else 'deep' if deep else 'shallow'
            i['classification'] = kind
            if not p['ok']:
                i['error'] = p['error']
                if blocker == '—':
                    blocker = f"`{i['pc']:x}: {a}`"
            counts[kind] += 1
            counts['rip'] += int('%rip' in a)
            counts['indirect'] += int(bool(re.match(r'(call|jmp)\s+\*', a)))
            counts['kcov'] += int('<__sanitizer_cov_trace_pc>' in i['asm'])
            counts['inline'] += int(len(i['frames']) > 1)
            counts['calls'] += int(a.startswith('call '))
            counts['comparisons'] += int('<__sanitizer_cov_trace_' in i['asm'] and '_cmp' in i['asm'])
            counts['switches'] += int('<__sanitizer_cov_trace_switch>' in i['asm'])
            if m := re.match(r'j\w+\s+L_([0-9a-f]+)$', a):
                target = int(m[1], 16)
                if target in pcs:
                    leaders.add(target)
            if a.startswith(('j', 'call ', 'ret')):
                following = i['pc'] + len(bytes.fromhex(i['bytes']))
                if following in pcs:
                    leaders.add(following)
        counts['regions'] = len(leaders)
        f['counts'] = dict(counts)
        total.update(counts)
        table.append(f"| `{f['name']}` | {len(f['instructions'])} | {counts['supported']} | {counts['shallow']} | {counts['deep']} | {counts['kcov']} | {blocker} |")
    (out / 'census.json').write_text(json.dumps(dict(functions=functions, totals=dict(total)), indent=2)+'\n')
    (out / 'table.md').write_text('\n'.join(table)+'\n')
    print(json.dumps(dict(functions=len(functions), totals=dict(total)), indent=2))
    print('Unsupported forms:', Counter(i['normalized'].split()[0] for f in functions for i in f['instructions'] if i['classification'] != 'supported'))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--kernel', type=Path, default=ORACLE)
    p.add_argument('--out', type=Path, default=ROOT / '.tmp/binary-tv')
    args = p.parse_args()
    census(args.kernel, args.out)
