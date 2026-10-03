#!/usr/bin/env python3
"""Step 0 of the choice-stream strategy: the enumeration probe's report
(docs/2026-10-03-choice-stream-strategy.md, section 10).

Reads the Linux run directories of a check on the net-probe kernel and
reports, from the generic records (LEANUX_PROBE / LEANUX_RPROBE):

1. the inventory: every random and clock consumer in the trace windows, by
   symbolized call chain, with counts per operation type;
2. the cross-check: every per-site record of the merged instrument
   (LEANUX_HIDDEN / LEANUX_RHIDDEN, coverage child) has a generic record with
   the same value at the same call chain's site;
3. ordering: how remote sections and task-stream records interleave by
   sequence number, against the convention (task records before remote).

    scripts/in-bundle python3 scripts/probe-choice-enumeration.py VMLINUX CHECK_DIR [CHECK_DIR ...]
"""
import json
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

KINDS = {1: 'get_random_bytes', 101: 'get_random_u8', 102: 'get_random_u16', 104: 'get_random_u32',
         108: 'get_random_u64', 110: '__get_random_u32_below', 300: 'section_start', 301: 'section_stop'}
CLOCKS = ['ktime_get_mono_fast_ns', 'ktime_get_raw_fast_ns', 'ktime_get_boot_fast_ns', 'ktime_get_tai_fast_ns',
          'ktime_get_real_fast_ns', 'ktime_get_real_ts64', 'ktime_get', 'ktime_get_with_offset',
          'ktime_get_coarse_with_offset', 'ktime_get_raw', 'ktime_get_ts64', 'ktime_get_seconds',
          'ktime_get_real_seconds', 'ktime_get_raw_ts64', 'getboottime64', 'ktime_get_coarse_real_ts64',
          'ktime_get_coarse_ts64']
for k, name in enumerate(CLOCKS, start=200):
    KINDS[k] = name
# the merged per-site instrument's sites
PER_SITE = {1: 'drivers/net/wireguard/noise.c:541', 2: 'drivers/net/wireguard/noise.c:688',
            3: 'drivers/net/wireguard/noise.c:501', 4: 'drivers/net/wireguard/peerlookup.c:132'}


def rows(boot, prefix):
    out = []
    for line in boot.splitlines():
        line = line.rstrip('\r')
        if line.startswith(prefix + ' '):
            out.append(json.loads(line[len(prefix) + 1:]))
    return out


def symbolize(vmlinux, ips):
    ips = sorted(set(ips))
    query = ''.join(hex(int(ip, 16) - 1) + '\n' for ip in ips).encode()
    out = subprocess.run(['addr2line', '-e', vmlinux, '-a', '-i', '-f'], input=query, capture_output=True,
                         check=True).stdout.decode().splitlines()
    chains, k = [], 0
    while k < len(out):
        if out[k].startswith('0x'):
            chains.append([])
            k += 1
        else:
            chains[-1].append((out[k], out[k + 1].split('/.deps/linux/')[-1].split(' ')[0]))
            k += 2
    if len(chains) != len(ips):
        raise SystemExit('malformed addr2line output')
    return dict(zip(ips, chains))


def clamp(b):
    b = bytearray(b)
    b[0] &= 248
    b[31] = (b[31] & 127) | 64
    return bytes(b)


def main():
    vmlinux, dirs = sys.argv[1], [Path(d) for d in sys.argv[2:]]
    # a chunk rerun as halves (output limit) has a linux run but no model inputs
    linux_dirs = [p for d in dirs for p in sorted(d.glob('chunk-*/linux')) if (p.parent / 'model/inputs.jsonl').exists()]
    traces = {}
    probe, hidden = [], []
    for ld in linux_dirs:
        boot = (ld / 'boot.log').read_text(errors='replace')
        for t in (json.loads(l) for l in (ld.parent / 'model/inputs.jsonl').read_text().splitlines()):
            traces[t['id']] = t
        probe += [dict(r, stream='task') for r in rows(boot, 'LEANUX_PROBE')]
        probe += [dict(r, stream='remote') for r in rows(boot, 'LEANUX_RPROBE')]
        hidden += [dict(r, stream=s) for s, p in (('task', 'LEANUX_HIDDEN'), ('remote', 'LEANUX_RHIDDEN'))
                   for r in rows(boot, p) if r['mode'] == 'pc']
    chains = symbolize(vmlinux, [rec[1] for r in probe for rec in r['records']])

    def site(chain):
        return ' <- '.join(f'{fn}@{src}' for fn, src in chain)

    # 1. inventory
    inventory = defaultdict(Counter)        # op type -> (kind, chain) -> count
    per_op = Counter()
    for r in probe:
        op = traces[r['id']]['ops'][r['index']]['op']
        per_op[op] += 1
        for kind, ip, seq, length, data in r['records']:
            if kind in (300, 301):
                continue
            inventory[op][(KINDS.get(kind, kind), r['stream'], site(chains[ip]))] += 1
    # 2. cross-check
    by_op = defaultdict(list)
    for r in probe:
        by_op[(r['id'], r['index'])] += r['records']
    matched, unmatched = 0, []
    for h in hidden:
        for s, ip, data in h['records']:
            value = bytes.fromhex(data)
            want = PER_SITE[s]
            ok = False
            for kind, pip, seq, length, pdata in by_op[(h['id'], h['index'])]:
                srcs = {src for _, src in chains[pip]}
                if want not in srcs:
                    continue
                pv = bytes.fromhex(pdata)
                if (s in (1, 2) and kind == 1 and clamp(pv[:32]) == value[:32]) or \
                   (s == 4 and kind == 104 and pv[:4] == value[:4]) or \
                   (s == 3 and kind == 205 and pv[:16] == value[:16]):
                    ok = True
                    break
            matched += ok
            if not ok:
                unmatched.append((h['id'], h['index'], s))
    # 3. ordering
    overlaps, interleaved, stop_order = 0, 0, 0
    sections_seen = 0
    for (tid, idx), recs in by_op.items():
        starts = [(seq, ip) for kind, ip, seq, _, _ in recs if kind == 300]
        stops = [seq for kind, ip, seq, _, _ in recs if kind == 301]
        sections_seen += len(starts)
    for r in probe:
        if r['stream'] != 'remote':
            continue
        # area order is stop order; check whether start sequence numbers are increasing in it
        st = [seq for kind, _, seq, _, _ in r['records'] if kind == 300]
        if st != sorted(st):
            stop_order += 1
        open_ = 0
        for kind, _, seq, _, _ in r['records']:
            if kind == 300:
                if open_:
                    overlaps += 1
                open_ += 1
            elif kind == 301:
                open_ -= 1
    task_seqs = defaultdict(list)
    for r in probe:
        if r['stream'] == 'task':
            task_seqs[(r['id'], r['index'])] += [seq for kind, _, seq, _, _ in r['records'] if kind not in (300, 301)]
    for r in probe:
        if r['stream'] != 'remote':
            continue
        first = [seq for kind, _, seq, _, _ in r['records'] if kind == 300]
        if first and any(s > min(first) for s in task_seqs.get((r['id'], r['index']), [])):
            interleaved += 1
    report = {
        'traces': len(traces), 'probe_rows': len(probe), 'rows_per_op_type': dict(per_op),
        'cross_check': {'per_site_records': matched + len(unmatched), 'matched_by_generic': matched,
                        'unmatched': unmatched[:20]},
        'ordering': {'sections': sections_seen, 'remote_rows_with_start_order_not_area_order': stop_order,
                     'nested_or_overlapping_sections': overlaps,
                     'ops_with_task_records_after_a_remote_section_start': interleaved},
        'inventory': {op: [[k[0], k[1], k[2], n] for k, n in c.most_common()] for op, c in inventory.items()},
    }
    print(json.dumps(report, indent=1))


if __name__ == '__main__':
    main()
