#!/usr/bin/env python3
"""Negative controls for steering (choice-stream strategy, step 2): every
trace in corpus/steering-controls and corpus/lifecycle-controls must fail,
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
}


def run_suite(suite, count):
    out = ROOT / f'.artifacts/check/{suite}'
    subprocess.run(['rm', '-rf', str(out)], check=True)
    subprocess.run([sys.executable, '-m', 'evaluator.check', '--suite', suite,
                    '--out', str(out)], cwd=ROOT, capture_output=True)
    report = json.loads((out / 'report.json').read_text())
    if report.get('aborted') or report['traces'] != count:
        print(json.dumps(dict(suite=suite, error='the control run did not run its traces',
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
    report = run_suite('lifecycle-controls', len(LIFECYCLE_EXPECTED))
    if report is None:
        return 2
    failures = {f['id']: f for f in report['failures']}
    for trace_id, (outcome, detail) in LIFECYCLE_EXPECTED.items():
        f = failures.get(trace_id) or {}
        passed = f.get('outcome') == outcome and detail in f.get('detail', '')
        ok &= passed
        results[trace_id] = dict(rejected=passed, outcome=f.get('outcome', 'agreement'), detail=f.get('detail'))
    ok &= set(failures) == set(LIFECYCLE_EXPECTED)
    print(json.dumps(results, indent=1))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
