#!/usr/bin/env python3
"""Lane C measurement (docs/2026-10-15-design-c-fib-trie.md): which IPv4
routing functions the corpus already reaches, from a check run's dump.

KCOV instruments every file (CONFIG_KCOV_INSTRUMENT_ALL=y), so a run dump's
`coverage-map.json` (PC -> DWARF frames) and `coverage.jsonl` (per trace and
operation, the PCs hit) and `comparisons.jsonl` (the compare records with
operands) carry the routing code's coverage although `net/ipv4/*.c` is not
anchored. Usage:

    python3 scripts/probes/c-fib-coverage.py <run dump dir> [file ...]

Prints, per function of the named files (default: fib_trie.c,
fib_frontend.c, fib_semantics.c, route.c under net/ipv4), the distinct
lines hit, the traces reaching it, and the compare sites with their
distinct operand pairs. Read-only.
"""
import json, sys, glob, collections, os

run = sys.argv[1]
SITES = set()
args = sys.argv[2:]
if args and args[0] == '--sites':
    SITES = set(args[1].split(','))
    args = args[2:]
files = args or ['net/ipv4/fib_trie.c', 'net/ipv4/fib_frontend.c', 'net/ipv4/fib_semantics.c', 'net/ipv4/route.c']

def src_of(frames):
    out = []
    for f in frames:
        s = f['source'].split('/.deps/linux/')[-1]
        path, _, line = s.split(" ")[0].rpartition(":")
        if path in files:
            out.append((path, f['function'], int(line)))
    return out

lines = collections.defaultdict(set)          # (file, function) -> lines
traces = collections.defaultdict(set)         # (file, function) -> trace ids
cmp_sites = collections.defaultdict(set)      # (file, function, line) -> operand pairs
cmp_count = collections.Counter()
site_traces = collections.defaultdict(set)    # 'file:line' -> trace ids
ops = collections.defaultdict(set)            # (file, function) -> (trace, op index)
for chunk in sorted(glob.glob(os.path.join(run, 'chunk-*', 'linux'))):
    mp = os.path.join(chunk, 'coverage-map.json')
    if not os.path.exists(mp):
        continue
    loc = json.load(open(mp))['locations']
    pcmap = {pc: src_of(frames) for pc, frames in loc.items()}
    pcmap = {pc: v for pc, v in pcmap.items() if v}
    cov = os.path.join(chunk, 'coverage.jsonl')
    for row in open(cov):
        r = json.loads(row)
        for pc in r['pcs']:
            for path, fn, line in pcmap.get(pc, ()):
                lines[(path, fn)].add(line)
                traces[(path, fn)].add(r['id'])
                ops[(path, fn)].add((r['id'], r['index']))
    cmp = os.path.join(chunk, 'comparisons.jsonl')
    cmap = os.path.join(chunk, 'comparison-map.json')
    if os.path.exists(cmp) and os.path.exists(cmap):
        cloc = json.load(open(cmap))['locations']
        cpcmap = {pc: src_of(frames) for pc, frames in cloc.items()}
        cpcmap = {pc: v for pc, v in cpcmap.items() if v}
        for row in open(cmp):
            r = json.loads(row)
            for rec in r['records']:
                pc = rec[3]
                for path, fn, line in cpcmap.get(pc, ()):
                    cmp_sites[(path, fn, line)].add((rec[1], rec[2]))
                    if f'{path}:{line}' in SITES:
                        site_traces[f'{path}:{line}'].add((r['id'], rec[1], rec[2]))
                    cmp_count[(path, fn, line)] += 1

SHOW = {'fib_table_insert', 'fib_add_ifaddr', 'resize', 'collapse', 'inet_rtm_delroute', 'fib_table_flush', 'fib_table_delete', 'ip_route_input_slow', 'fib_del_ifaddr', 'fib_magic', 'fib_validate_source', 'ipv4_dst_check', 'rt_flush_dev'}
for key in sorted(lines):
    path, fn = key
    extra = ''
    if fn in SHOW:
        extra = f"; lines {sorted(lines[key])}; traces {sorted(traces[key])[:12]}"
    print(f'{path} {fn}: {len(lines[key])} lines ({min(lines[key])}-{max(lines[key])}), {len(traces[key])} traces, {len(ops[key])} operations{extra}')
print('--- compare sites')
for key in sorted(cmp_sites):
    path, fn, line = key
    print(f'{path}:{line} {fn}: {cmp_count[key]} records, {len(cmp_sites[key])} distinct operand pairs; e.g. {sorted(cmp_sites[key])[:3]}')

if SITES:
    print('--- traces per site')
    for site in sorted(site_traces):
        ids = sorted({t for t, _, _ in site_traces[site]})
        print(f'{site}: {len(ids)} traces: {ids[:20]}; operand samples {sorted({(a, b) for _, a, b in site_traces[site]})[:8]}')
