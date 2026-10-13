#!/usr/bin/env python3
"""Probe P-A for W7's full-ring tier (docs/2026-10-06-w4-w7-transmit-bulk.md,
sections 12 and 17.16), Linux only, no mirror: runs corpus/w7-tier traces (one
chunk, one boot) on the oracle and reports what the tier needs sized: the KCOV
words each child produced per operation against the capacity, the captured
output against the checker's limit, the batch's completions (the send result
per item), the observed datagrams, the peers' byte counters from wg_get and the
trace's time after wg_up.
    LEANUX_KERNEL_DIR=... scripts/in-bundle python3 scripts/wg-w7-tier-probe.py \\
        --trace corpus/w7-tier/w7_ring_wrap.json --out .artifacts/w7-tier/wrap-1
The run is a measurement, never evidence of agreement: the mirror is not run.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness import linux as H  # noqa: E402
from harness.steer import alloc_call_sites, call_sites, resolve as resolve_steering  # noqa: E402
from harness.trace import KCOV_CAPACITY, loads_trace  # noqa: E402
from harness.wg import decode_dump  # noqa: E402
from evaluator.check import load_hidden_sites  # noqa: E402

ROWS = ('LEANUX_COVERAGE', 'LEANUX_RCOVERAGE', 'LEANUX_CMP', 'LEANUX_RCMP', 'LEANUX_WGBATCH', 'LEANUX_WGOBS',
        'LEANUX_WG', 'LEANUX_TIMING')


def fresh():
    return dict(coverage={}, comparisons={}, batches=[], observed=[], peers=[], timing=[])


def absorb(per_trace, tag, row):
    report = per_trace.setdefault(row.get('id'), fresh())
    if tag in ('LEANUX_COVERAGE', 'LEANUX_RCOVERAGE', 'LEANUX_CMP', 'LEANUX_RCMP'):
        target = report['coverage'] if 'COVERAGE' in tag else report['comparisons']
        target[f"{tag[7:]} op {row.get('index')}"] = dict(
            count=row.get('count'), line_bytes=row['_bytes'], printed=len(row.get('pcs', row.get('records', []))))
    elif tag == 'LEANUX_WGBATCH':
        cqes = row.get('cqes', [])
        present = [c for c in cqes if c is not None]
        report['batches'].append(dict(index=row.get('index'), items=len(cqes), present=len(present),
                                      results=dict(Counter(map(str, present))),
                                      first_failure=next(((k, c) for k, c in enumerate(cqes) if c is not None and c < 0), None)))
    elif tag == 'LEANUX_WGOBS':
        datagrams = row.get('datagrams')
        report['observed'].append(dict(index=row.get('index'), datagrams=None if datagrams is None else len(datagrams),
                                       stats=row.get('stats')))
    elif tag == 'LEANUX_WG':
        try:
            device = decode_dump(row.get('payloads', []))
            peers = [dict(public_key=p.get('public_key', '')[:16], rx_bytes=p.get('rx_bytes'), tx_bytes=p.get('tx_bytes'))
                     for p in device.get('peers', [])]
        except Exception as exc:  # the probe reports, it does not judge
            peers = f'undecoded: {exc}'
        report['peers'].append(dict(index=row.get('index'), peers=peers))
    elif tag == 'LEANUX_TIMING' and 'since_up_ns' in row:
        report['timing'].append(dict(mode=row.get('mode'), since_up_s=row['since_up_ns'] / 1e9))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--trace', required=True, nargs='+')
    ap.add_argument('--out', required=True)
    ap.add_argument('--timeout', type=float, default=900)
    args = ap.parse_args()
    traces = [loads_trace(Path(p).read_text()) for p in args.trace]
    out = Path(args.out).resolve()
    steer_wire = {}
    if any('steer' in t for t in traces):
        sites = load_hidden_sites()
        by_label = {e['label']: e for e in sites.values()}
        calls = call_sites(H.KERNEL / 'vmlinux', H.ARTIFACTS / 'cache')
        asites = alloc_call_sites(H.KERNEL / 'vmlinux', H.ARTIFACTS / 'cache')
        for t in traces:
            if 'steer' in t:
                steer_wire[t['id']] = resolve_steering(t, by_label, calls, asites)
    status = 'complete'
    try:
        H.run_linux(traces, out, timeout=args.timeout, steer_wire=steer_wire)
    except H.LinuxRunError as exc:
        status = f'{exc.kind}: {exc}'
    per_trace = {}
    errors = []
    if (out / 'boot.log').exists():
        for line in (out / 'boot.log').read_text(errors='replace').splitlines():
            tag, _, rest = line.partition(' ')
            if tag in ROWS and rest.startswith('{'):
                row = json.loads(rest)
                row['_bytes'] = len(line)
                absorb(per_trace, tag, row)
    if (out / 'guest-errors.jsonl').exists():
        errors = [json.loads(l) for l in (out / 'guest-errors.jsonl').read_text().splitlines() if l.strip()]
    report = dict(traces=[t['id'] for t in traces], status=status, kcov_capacity=KCOV_CAPACITY,
                  output_limit=H.OUTPUT_LIMIT,
                  boot_log_bytes=(out / 'boot.log').stat().st_size if (out / 'boot.log').exists() else None,
                  guest_errors=errors, per_trace=per_trace)
    (out / 'probe.json').write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps(report, indent=1))
    return 0 if status == 'complete' else 1


if __name__ == '__main__':
    sys.exit(main())
