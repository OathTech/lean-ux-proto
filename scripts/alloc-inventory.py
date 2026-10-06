#!/usr/bin/env python3
"""A0 (docs/2026-10-05-a-alloc.md, section 12): the allocation inventory.

Runs the corpora on the A kernel with the allocation hook in inventory mode
(KCOV_LEANUX_ALLOC_LOAD with KCOV_ALLOC_INVENTORY; Linux only, no mirror) and
summarizes the kind-305 records:

    scripts/in-bundle python3 scripts/alloc-inventory.py run --pass 1 --out .artifacts/a0/pass1
    scripts/in-bundle python3 scripts/alloc-inventory.py run --pass 2 --from .artifacts/a0/pass1 --out .artifacts/a0/pass2
    scripts/in-bundle python3 scripts/alloc-inventory.py report --pass1 DIR --pass2 DIR [--baseline CHECKDIR]

Pass 1 records every allocation in a recording context, by address only (no
unwind). Pass 2 arms the addresses of pass 1 that symbolize into an inventory
file (the section-2 consumers and the allocation helpers) and records their
chains. The report attributes each pass-2 record to its consumer frame (the
first frame outside ALLOC_HELPERS, as the check will) and gives per site the
counts per operation, the gfp masks, the sizes, the chain depth reached, the
below-cut consumers, skb_cow_data's allocations per wg_xmit payload size and
the unwind cost. LEANUX_KERNEL_DIR selects the A kernel.
"""
import argparse
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.linux import KERNEL, LinuxRunError, run_linux  # noqa: E402
from harness.steer import call_sites, resolve as resolve_steering, symbolize  # noqa: E402
from harness.linux import ARTIFACTS  # noqa: E402

ALLOC_KIND = 305
INVENTORY = 1
CHUNK = 100
# The allocation helpers (design section 4.2): files, and functions by name.
ALLOC_HELPER_FILES = ('include/linux/slab.h', 'include/linux/gfp.h', 'mm/slub.c', 'mm/page_alloc.c', 'mm/util.c',
                      'net/core/skbuff.c', 'include/linux/skbuff.h', 'fs/dcache.c', 'fs/inode.c')
ALLOC_HELPER_FUNCTIONS = ('skb_checksum_help',)
# Pass 2 arms the pass-1 addresses whose inline chain touches these files
# (the section-2 consumers' files and the helpers that are not the
# allocators themselves), or the helper functions.
INVENTORY_FILES = ('drivers/net/wireguard/', 'fs/eventfd.c', 'fs/file.c', 'fs/file_table.c', 'fs/anon_inodes.c',
                   'mm/util.c', 'net/core/skbuff.c', 'include/linux/skbuff.h', 'fs/dcache.c', 'fs/inode.c')
# The consumer frames section 2 declares (file:line).
DECLARED = {
    'fs/eventfd.c:393': 'kmallocEventfdCtx', 'fs/file_table.c:232': 'filpAlloc',
    'fs/file_table.c:374': 'dAllocPseudo', 'fs/file.c:148': 'kmallocFdtable', 'fs/file.c:152': 'kvmallocFdArray',
    'fs/file.c:157': 'kvmallocFdBitmaps', 'drivers/net/wireguard/peer.c:33': 'kmemCacheZallocPeer',
    'drivers/net/wireguard/noise.c:100': 'kzallocKeypair', 'drivers/net/wireguard/allowedips.c:190': 'allocNode/190',
    'drivers/net/wireguard/allowedips.c:205': 'allocNode/205', 'drivers/net/wireguard/allowedips.c:234': 'allocNode/234',
    'drivers/net/wireguard/socket.c:192': 'sendBufSkb', 'drivers/net/wireguard/socket.c:217': 'replySkb',
    'drivers/net/wireguard/send.c:226': 'keepaliveSkb', 'drivers/net/wireguard/send.c:183': 'skbCowHead',
    'drivers/net/wireguard/send.c:188': 'skbChecksumHelp', 'drivers/net/wireguard/send.c:192': 'skbCowData(tx)',
    'drivers/net/wireguard/receive.c:268': 'skbCowData(rx)',
}
NESTED, PAGE, NOCHAIN = 1 << 8, 1 << 9, 1 << 10


def decode(record):
    """[kind, ip, seq, len, hex] -> dict, or None for other kinds."""
    if record[0] & 0x7fff != ALLOC_KIND:
        return None
    if record[3] != 40:
        raise ValueError(f'kind-305 record of length {record[3]}')
    words = [int.from_bytes(bytes.fromhex(record[4][16 * i:16 * i + 16]), 'little') for i in range(5)]
    w0 = words[0]
    return dict(addr=int(record[1], 16), seq=record[2], steered=bool(record[0] & 0x8000), ok=w0 & 0xff,
                nested=bool(w0 & NESTED), page=bool(w0 & PAGE), nochain=bool(w0 & NOCHAIN),
                size=(w0 >> 11) & ((1 << 21) - 1), gfp=w0 >> 32, chain=[w for w in words[1:] if w])


def load_corpus(suites, seed, wireguard_count, generated_count):
    from evaluator.check import load_traces
    filtered = Counter()
    return load_traces(suites, {'generated': generated_count, 'wireguard-generated': wireguard_count}, seed, None,
                       filtered)


def steer_wires(traces):
    if not any('steer' in t for t in traces):
        return {}
    from evaluator.check import load_hidden_sites
    by_label = {e['label']: e for e in load_hidden_sites().values()}
    calls = call_sites(KERNEL / 'vmlinux', ARTIFACTS / 'cache')
    return {t['id']: resolve_steering(t, by_label, calls) for t in traces if 'steer' in t}


def run_chunk(traces, out, alloc, wires):
    from evaluator.check import guest_timeout
    try:
        run_linux(traces, out, timeout=3 * guest_timeout(traces), alloc=alloc,
                  steer_wire={t['id']: wires[t['id']] for t in traces if t['id'] in wires})
        return [(out, traces)]
    except LinuxRunError as exc:
        if exc.kind == 'output_limit' and len(traces) > 1:
            half = len(traces) // 2
            return run_chunk(traces[:half], out.with_name(out.name + 'a'), alloc, wires) + \
                run_chunk(traces[half:], out.with_name(out.name + 'b'), alloc, wires)
        raise


def pass2_ranges(pass1):
    """The pass-1 addresses in an inventory file, as [a, a+1) ranges, or the
    containing functions' ranges if there are more than 64."""
    addrs = sorted({r['addr'] for r in records_of(pass1)})
    chains = dict(zip(addrs, symbolize(KERNEL / 'vmlinux', [a - 1 for a in addrs])))
    chosen = [a for a in addrs if any(src.startswith(INVENTORY_FILES) or fn in ALLOC_HELPER_FUNCTIONS
                                      for fn, src in chains[a])]
    if len(chosen) <= 64:
        return [(a, a + 1) for a in chosen], {hex(a): chains[a] for a in chosen}
    raise SystemExit(f'{len(chosen)} inventory addresses: more than 64 ranges; merge by function first')


def iter_rows(passdir):
    """(trace, row) for every hidden row of every chunk."""
    for status in sorted(Path(passdir).glob('chunk-*/run-status.json')):
        if json.loads(status.read_text()).get('kind') != 'complete':
            continue   # split for the output limit and rerun as halves
        chunk = status.parent
        traces = {t['id']: t for t in map(json.loads, (chunk / 'inputs.jsonl').read_text().splitlines())}
        for line in (chunk / 'hidden.jsonl').read_text().splitlines():
            row = json.loads(line)
            yield traces[row['id']], row


def records_of(passdir, mode='pc'):
    for trace, row in iter_rows(passdir):
        if row['mode'] != mode:
            continue
        stack = []
        for rec in row['records']:
            if rec[0] == 300:
                stack.append(int.from_bytes(bytes.fromhex(rec[4]), 'little'))
                continue
            if rec[0] == 301:
                stack.pop()
                continue
            d = decode(rec)
            if d:
                op = trace['ops'][row['index']]
                d.update(trace=trace['id'], index=row['index'], op=op['op'], stream=row['stream'],
                         section=stack[-1] if stack else None, packet=op.get('packet'))
                yield d


def cmd_run(args):
    traces = load_corpus(args.suite.split(','), args.seed, args.wireguard_count, args.generated_count)
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    if args.pass_ == 1:
        alloc = {'flags': INVENTORY, 'ranges': []}
    else:
        ranges, chains = pass2_ranges(Path(args.from_))
        alloc = {'flags': INVENTORY, 'ranges': ranges}
        (out / 'ranges.json').write_text(json.dumps({'ranges': [[hex(a), hex(b)] for a, b in ranges],
                                                     'chains': chains}, indent=1) + '\n')
    wires = steer_wires(traces)
    chunks = [(traces[i:i + CHUNK], out / f'chunk-{i // CHUNK:03}') for i in range(0, len(traces), CHUNK)]
    print(f'{len(traces)} traces, {len(chunks)} chunks, alloc {alloc["flags"]}/{len(alloc["ranges"])}',
          file=sys.stderr, flush=True)
    with ThreadPoolExecutor(args.jobs) as pool:
        done = list(pool.map(lambda c: run_chunk(c[0], c[1], alloc, wires), chunks))
    print(f'{sum(len(d) for d in done)} guest runs', file=sys.stderr)


def symbol_map(addrs):
    addrs = sorted(set(addrs))
    return dict(zip(addrs, symbolize(KERNEL / 'vmlinux', [a - 1 for a in addrs]))) if addrs else {}


def function_names():
    """Text symbols by address (System.map): a section record carries the
    dispatched function's own address, not a return address."""
    names = {}
    for line in (KERNEL / 'System.map').read_text().splitlines():
        address, kind, name = line.split()[:3]
        if kind in ('t', 'T'):
            names.setdefault(int(address, 16), name)
    return names


def helper(frame):
    fn, src = frame
    return src.split(':')[0] in ALLOC_HELPER_FILES or fn in ALLOC_HELPER_FUNCTIONS


def consumer(rec, syms):
    """(consumer "file:line", function, depth): depth 0 is the record's
    address, 1-4 the chain words; None if no frame outside the helpers."""
    for depth, a in enumerate([rec['addr']] + rec['chain']):
        for frame in syms[a]:
            if not helper(frame):
                return frame[1].split(' ')[0], frame[0], depth
    return None


def cycles_per_us(passdir, given=None):
    """The guest's TSC rate. Under TCG the guest reads the host's TSC, so the
    guest kernel's calibration ("cpu MHz") is that rate when the calibration
    succeeded; a boot under host load may report 0. The largest reported
    rate, or --tsc-mhz."""
    if given:
        return given
    rates = [float(json.loads(line)['mhz']) for chunk in sorted(Path(passdir).glob('chunk-*/alloc.jsonl'))
             for line in chunk.read_text().splitlines() if 'mhz' in json.loads(line)]
    if not rates or max(rates) <= 0:
        raise ValueError('no TSC rate: pass --tsc-mhz')
    return max(rates)


def timing(passdir):
    total, ops, traces = 0.0, 0, 0
    for status in sorted(Path(passdir).glob('**/run-status.json')):
        s = json.loads(status.read_text())
        if s.get('kind') == 'complete':
            total += s['elapsed_seconds']
            ops += s['operations']
            traces += s['traces']
    return dict(seconds=round(total, 1), operations=ops, traces=traces,
                ms_per_operation=round(1000 * total / ops, 2) if ops else None)


def cmd_report(args):
    p1 = list(records_of(args.pass1))
    report = {'pass1': {}, 'pass2': {}}
    # ---- pass 1: every allocation by address ----
    syms = symbol_map(r['addr'] for r in p1)
    by_addr = defaultdict(lambda: dict(n=0, ops=Counter(), gfp=Counter(), sizes=Counter(), nested=0, fail=0,
                                       page=False, streams=Counter()))
    for r in p1:
        e = by_addr[r['addr']]
        e['n'] += 1
        e['ops'][r['op']] += 1
        e['gfp'][hex(r['gfp'])] += 1
        e['sizes'][r['size']] += 1
        e['nested'] += r['nested']
        e['fail'] += not r['ok']
        e['page'] = r['page']
        e['streams'][r['stream'] if r['section'] is None else hex(r['section'])] += 1
    names = function_names()
    rows = []
    for a, e in sorted(by_addr.items(), key=lambda kv: -kv[1]['n']):
        rows.append(dict(addr=hex(a), frames=[f'{fn} {src}' for fn, src in syms[a]], n=e['n'], page=e['page'],
                         nested=e['nested'], fail=e['fail'], ops=dict(e['ops'].most_common()),
                         gfp=dict(e['gfp']), sizes=dict(sorted(e['sizes'].items())),
                         contexts={(names[int(k, 16)] if k.startswith('0x') else k): v
                                   for k, v in e['streams'].items()}))
    ops_count = Counter()
    for trace, row in iter_rows(args.pass1):
        if row['mode'] == 'pc' and row['stream'] == 'task':
            ops_count[trace['ops'][row['index']]['op']] += 1
    per_op = Counter(r['op'] for r in p1)
    cmp_total = sum(1 for _ in records_of(args.pass1, 'cmp'))
    report['pass1'] = dict(records=len(p1), records_cmp_child=cmp_total, addresses=len(by_addr),
                           nested=sum(r['nested'] for r in p1), failed=sum(not r['ok'] for r in p1),
                           per_operation={op: dict(operations=ops_count[op], records=n,
                                                   per_op=round(n / ops_count[op], 1))
                                          for op, n in per_op.most_common()},
                           timing=timing(args.pass1), sites=rows)
    # ---- pass 2: chains for the inventory addresses ----
    if args.pass2:
        p2 = list(records_of(args.pass2))
        syms2 = symbol_map([r['addr'] for r in p2] + [w for r in p2 for w in r['chain']])
        sites = defaultdict(lambda: dict(n=0, ops=Counter(), gfp=Counter(), sizes=Counter(), depth=Counter(),
                                         addrs=Counter(), contexts=Counter(), function=None, nochain=0, fail=0))
        unresolved = Counter()
        for r in p2:
            c = consumer(r, syms2)
            if c is None:
                unresolved[hex(r['addr'])] += 1
                continue
            site, fn, depth = c
            e = sites[site]
            e['n'] += 1
            e['function'] = fn
            e['ops'][r['op']] += 1
            e['gfp'][hex(r['gfp'])] += 1
            e['sizes'][r['size']] += 1
            e['depth'][depth] += 1
            e['addrs'][hex(r['addr'])] += 1
            e['nochain'] += r['nochain']
            e['fail'] += not r['ok']
            e['contexts'][r['stream'] if r['section'] is None else hex(r['section'])] += 1
        out = []
        for site, e in sorted(sites.items(), key=lambda kv: (kv[0] not in DECLARED, -kv[1]['n'])):
            out.append(dict(site=site, declared=DECLARED.get(site), function=e['function'], n=e['n'],
                            ops=dict(e['ops'].most_common()), gfp=dict(e['gfp']),
                            sizes=dict(sorted(e['sizes'].items())), depth=dict(sorted(e['depth'].items())),
                            nochain=e['nochain'], fail=e['fail'],
                            addrs={k: [f'{fn} {src}' for fn, src in syms2[int(k, 16)]][:3] for k in e['addrs']},
                            contexts={(names[int(k, 16)] if k.startswith('0x') else k): v
                                      for k, v in e['contexts'].items()}))
        # per consultation: records per (trace, op) at each declared site
        per_consult = defaultdict(Counter)
        for r in p2:
            c = consumer(r, syms2)
            if c and c[0] in DECLARED:
                per_consult[c[0]][(r['trace'], r['index'])] += 1
        # skb_cow_data (send.c:192) per wg_xmit payload: records per packet
        xmit = defaultdict(Counter)
        for trace, row in iter_rows(args.pass2):
            op = trace['ops'][row['index']]
            if row['mode'] == 'pc' and row['stream'] == 'task' and op['op'] == 'wg_xmit':
                key = (op['packet']['family'], len(op['packet'].get('payload', '')) // 2)
                xmit[key]['ops'] += 1
        for r in p2:
            c = consumer(r, syms2)
            if r['op'] == 'wg_xmit' and c and c[0] in ('drivers/net/wireguard/send.c:192',
                                                        'drivers/net/wireguard/send.c:183',
                                                        'drivers/net/wireguard/send.c:188'):
                key = (r['packet']['family'], len(r['packet'].get('payload', '')) // 2)
                xmit[key][c[0].split(':')[-1]] += 1
        mhz = cycles_per_us(args.pass2, args.tsc_mhz)
        unwinds = cycles = 0
        for chunk in sorted(Path(args.pass2).glob('chunk-*/alloc.jsonl')):
            for line in chunk.read_text().splitlines():
                row = json.loads(line)
                if row.get('mode') == 'pc':
                    unwinds += row['unwinds']
                    cycles += row['cycles']
        report['pass2'] = dict(records=len(p2), unresolved=dict(unresolved), sites=out,
                               per_consultation={s: dict(Counter(c.values())) for s, c in per_consult.items()},
                               cow_by_payload={f'v{f} payload {n}': dict(c) for (f, n), c in sorted(xmit.items())},
                               unwind=dict(unwinds=unwinds, cpu_mhz=mhz,
                                           us_per_unwind=round(cycles / unwinds / mhz, 2) if unwinds else None),
                               timing=timing(args.pass2))
    if args.baseline:
        report['baseline_timing'] = timing(args.baseline)
    print(json.dumps(report, indent=1))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='cmd', required=True)
    run = sub.add_parser('run')
    run.add_argument('--pass', dest='pass_', type=int, choices=(1, 2), required=True)
    run.add_argument('--from', dest='from_')
    run.add_argument('--out', required=True)
    run.add_argument('--suite', default='handwritten,critic,wireguard,generated,wireguard-generated')
    run.add_argument('--seed', type=int, default=20260920)
    run.add_argument('--generated-count', type=int, default=1000)
    run.add_argument('--wireguard-count', type=int, default=200)
    run.add_argument('--jobs', type=int, default=2)
    rep = sub.add_parser('report')
    rep.add_argument('--pass1', required=True)
    rep.add_argument('--pass2')
    rep.add_argument('--baseline')
    rep.add_argument('--tsc-mhz', type=float)
    args = parser.parse_args()
    if args.cmd == 'run' and args.pass_ == 2 and not args.from_:
        parser.error('pass 2 needs --from PASS1')
    (cmd_run if args.cmd == 'run' else cmd_report)(args)


if __name__ == '__main__':
    main()
