#!/usr/bin/env python3
"""Negative controls for steering (choice-stream strategy, step 2): every
trace in corpus/steering-controls, corpus/lifecycle-controls and corpus/underload-controls must fail,
with the stated problem or outcome.

    scripts/in-bundle python3 scripts/steering-controls.py
"""
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = {
    'sc_unreached_site': 'the schedule was not consumed exactly',
    'sc_extra_entry': 'the schedule was not consumed exactly',
    'sc_wrong_order': 'a scheduled site met an entry it does not match',
}


# L (docs/2026-10-05-l-lifecycle.md, section 3.3): the random port's first
# candidate steered onto the fixture's listener port. Linux steps to another
# port; the mirror stops outside its domain, which fails the trace's chunk
# (its own suite).
LIFECYCLE_EXPECTED = {
    'l_random_port_collision': ('unsupported_path', 'the random port draw collides with a bound port'),
    # W3b (docs/2026-10-06-w3-w12.md I.8; the Peer audit's F1, 2026-10-15): a
    # session's keepalive staged by the first entry of a wg_set message is
    # crypt work the second entry's remove flushes (peer.c:116-120); the
    # mirror stops where the flush would run it.
    'l_w3b_remove_crypt_queued': ('unsupported_path', 'crypt work queued at a peer removal'),
}


# E-B (docs/2026-10-05-e-dos.md §4.1): the merged-injection control bundles a
# valid initiation into the flood's io_uring batch, so the kernel makes a cookie
# reply inside the flood's (discarded) receive-worker section. The mirror's
# section-bracket discard then meets the reply's modeled records inside the flood
# section and fails closed (the two-distinct-sections assertion).
UNDERLOAD_EXPECTED = {
    'e_underload_merged': ('hidden_mismatch', 'inside the discarded flood region'),
}


def run_suite(suite, count, trace=None):
    """The suite's run, or one trace of it alone (`trace`): a stopped mirror
    fails its whole chunk, so controls that stop run one per chunk."""
    out = ROOT / f'.artifacts/check/{suite}' / (trace or 'all')
    subprocess.run(['rm', '-rf', str(out)], check=True)
    subprocess.run([sys.executable, '-m', 'evaluator.check', '--suite', suite,
                    '--out', str(out)] + (['--trace', trace] if trace else []), cwd=ROOT, capture_output=True)
    report = json.loads((out / 'report.json').read_text())
    if report.get('aborted') or report['traces'] != count:
        print(json.dumps(dict(suite=suite, trace=trace, error='the control run did not run its traces',
                              aborted=report.get('aborted'))))
        return None
    return report


def main():
    report = run_suite('steering-controls', len(EXPECTED))
    if report is None:
        return 2
    failures = {f['id']: f for f in report['failures']}
    results, ok = {}, True
    for trace_id, problem in EXPECTED.items():
        f = failures.get(trace_id)
        found = sorted({p['problem'] for p in (f or {}).get('problems', [])})
        passed = f is not None and problem in found
        ok &= passed
        results[trace_id] = dict(rejected=passed, outcome=(f or {}).get('outcome', 'agreement'), problems=found)
    ok &= set(failures) == set(EXPECTED)
    # a stopped mirror fails its chunk, so each lifecycle control runs alone;
    # the report's failures carry the stopping trace in their detail
    # ("trace <id> operation <i>: ...")
    for trace_id, (outcome, detail) in LIFECYCLE_EXPECTED.items():
        report = run_suite('lifecycle-controls', 1, trace_id)
        if report is None:
            return 2
        failures = [f for f in report['failures']
                    if f.get('id') == trace_id or f.get('detail', '').startswith(f'trace {trace_id} ')]
        f = failures[0] if failures else {}
        passed = f.get('outcome') == outcome and detail in f.get('detail', '')
        ok &= passed and len(report['failures']) == 1
        results[trace_id] = dict(rejected=passed, outcome=f.get('outcome', 'agreement'), detail=f.get('detail'))
    report = run_suite('underload-controls', len(UNDERLOAD_EXPECTED))
    if report is None:
        return 2
    failures = {f.get('id') or f.get('detail', '').split(' ')[1]: f for f in report['failures']}
    for trace_id, (outcome, detail) in UNDERLOAD_EXPECTED.items():
        f = failures.get(trace_id) or {}
        passed = f.get('outcome') == outcome and detail in f.get('detail', '')
        ok &= passed
        results[trace_id] = dict(rejected=passed, outcome=f.get('outcome', 'agreement'), detail=f.get('detail'))
    ok &= set(failures) == set(UNDERLOAD_EXPECTED)
    print(json.dumps(results, indent=1))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
