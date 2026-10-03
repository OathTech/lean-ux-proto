#!/usr/bin/env python3
"""Feasibility probe for hidden inputs (docs/2026-10-03-hidden-inputs-design.md,
section 7, step 1). Reads a Linux run directory made on the net-hidden kernel
and checks:

1. every record's call site resolves to its declared hook line;
2. every operation that produced a handshake response carries, in its remote
   stream and in both children, one clamped 32-byte response ephemeral and at
   least one index draw;
3. every handshake initiation wg0 sent to a fixture listener is reproduced
   byte for byte by harness/noise.py from the send worker's records (initiation
   ephemeral, TAI64N clock read, index draw) and the trace's keys.

    scripts/in-bundle python3 scripts/probe-hidden-inputs.py RUN_DIR VMLINUX TRACES.jsonl
"""
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from harness import noise  # noqa: E402

SITES = {1: ('init_ephemeral', 'drivers/net/wireguard/noise.c:541', 32),
         2: ('resp_ephemeral', 'drivers/net/wireguard/noise.c:688', 32),
         3: ('tai64n_now', 'drivers/net/wireguard/noise.c:501', 16),
         4: ('index_draw', 'drivers/net/wireguard/peerlookup.c:132', 8)}


def tai64n(now):
    sec = int.from_bytes(now[:8], 'little', signed=True)
    nsec = int.from_bytes(now[8:16], 'little', signed=True)
    nsec -= nsec % (1 << 24)   # ALIGN_DOWN(nsec, rounddown_pow_of_two(NSEC_PER_SEC / 50))
    return (0x400000000000000a + sec).to_bytes(8, 'big') + nsec.to_bytes(4, 'big')


def resolve(vmlinux, ips):
    query = ''.join(hex(int(ip, 16) - 1) + '\n' for ip in ips).encode()
    out = subprocess.run(['addr2line', '-e', vmlinux, '-a', '-i'], input=query, capture_output=True,
                         check=True).stdout.decode().splitlines()
    stacks = []
    for line in out:
        if line.startswith('0x'):
            stacks.append([])
        else:
            stacks[-1].append(line.split('/.deps/linux/')[-1].split(' ')[0])
    if len(stacks) != len(ips):
        raise SystemExit('malformed addr2line output')
    return dict(zip(ips, stacks))


def main():
    run, vmlinux, traces_path = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
    traces = {t['id']: t for t in map(json.loads, Path(traces_path).read_text().splitlines())}
    rows = [json.loads(line) for line in (run / 'hidden.jsonl').read_text().splitlines()]
    dgrams = [json.loads(line) for line in (run / 'datagrams.jsonl').read_text().splitlines()]
    problems, counts = [], defaultdict(int)

    # 1. call sites
    ips = sorted({r[1] for row in rows for r in row['records']})
    frames = resolve(vmlinux, ips) if ips else {}
    for row in rows:
        for site, ip, data in row['records']:
            counts[f"records:{row['mode']}:{SITES.get(site, ('?',))[0]}"] += 1
            if site not in SITES:
                problems.append(f"{row['id']}#{row['index']}: unknown site {site}")
                continue
            name, line, length = SITES[site]
            if len(data) != 2 * length:
                problems.append(f"{row['id']}#{row['index']}: {name} has {len(data) // 2} bytes")
            if line not in frames[ip]:
                problems.append(f"{row['id']}#{row['index']}: {name} at {frames[ip]}, expected {line}")

    by_op = defaultdict(list)
    for row in rows:
        by_op[(row['id'], row['index'], row['mode'], row['stream'])] += row['records']

    # 2. responses
    for line in (run / 'observations.jsonl').read_text().splitlines():
        result = json.loads(line)
        tid = result['id']
        trace = traces.get(tid)
        if not trace:
            continue
        for i, op in enumerate(trace['ops']):
            if op['op'] != 'wg_inject' or not op['message'].startswith('01000000'):
                continue
            for mode in ('pc', 'cmp'):
                recs = by_op[(tid, i, mode, 'remote')]
                resp = [r for r in recs if r[0] == 2]
                draws = [r for r in recs if r[0] == 4]
                if resp:
                    counts[f'responses:{mode}'] += 1
                    e = bytes.fromhex(resp[0][2])
                    if len(resp) != 1 or e[0] & 7 or e[31] & 0xc0 != 0x40 or not draws:
                        problems.append(f'{tid}#{i} {mode}: response records {recs}')

    # 3. initiations, in order, against the datagrams at the listeners
    for tid, trace in traces.items():
        private = None
        peers = []
        for op in trace['ops']:
            if op['op'] == 'wg_set':
                config = op['config']
                if 'private_key' in config:
                    private = bytes.fromhex(config['private_key'])
                peers += [bytes.fromhex(p['public_key']) for p in config.get('peers', [])]
        made = []
        for i in range(len(trace['ops'])):
            recs = by_op[(tid, i, 'pc', 'remote')]
            k = 0
            while k < len(recs):
                if recs[k][0] == 1 and (k + 1 == len(recs) or recs[k + 1][0] != 3):
                    # create_initiation drew the ephemeral, then failed (es or
                    # ss null) before reading the clock or inserting an index
                    counts['initiations_failed_after_ephemeral'] += 1
                    k += 1
                elif recs[k][0] == 1:
                    group = recs[k:k + 3]
                    sites = [r[0] for r in group]
                    if sites[:2] != [1, 3] or 4 not in sites:
                        problems.append(f'{tid}#{i}: initiation records {group}')
                        break
                    made.append((bytes.fromhex(group[0][2]), bytes.fromhex(group[1][2]),
                                 int.from_bytes(bytes.fromhex(group[2][2])[:4], 'little')))
                    k += 3
                else:
                    k += 1
        seen = [bytes.fromhex(h) for row in dgrams if row['id'] == tid
                for fam, h in row['datagrams'] if fam in (4, 6) and len(h) == 296 and h.startswith('01000000')]
        if not seen and not made:
            continue
        counts['initiation_traces'] += 1
        for message in seen:
            sender = int.from_bytes(message[4:8], 'little')
            match = [m for m in made if m[2] == sender]
            if len(match) != 1:
                problems.append(f'{tid}: no single initiation record for sender index {sender:#x}')
                continue
            e, now, index = match[0]
            rebuilt = [noise.initiation(peer, private, e, tai64n(now), index) for peer in set(peers)]
            if message in rebuilt:
                counts['initiations_reproduced'] += 1
            else:
                problems.append(f'{tid}: initiation {sender:#x} not reproduced from its records')
    print(json.dumps(dict(counts=dict(sorted(counts.items())), problems=problems[:50], problem_count=len(problems)),
                     indent=2))
    return 1 if problems else 0


if __name__ == '__main__':
    sys.exit(main())
