#!/usr/bin/env python3
"""Negative controls for steering (choice-stream strategy, step 2): every
trace in corpus/steering-controls must fail, with the stated problem.

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


def main():
    out = ROOT / '.artifacts/check/steering-controls'
    subprocess.run(['rm', '-rf', str(out)], check=True)
    subprocess.run([sys.executable, '-m', 'evaluator.check', '--suite', 'steering-controls', '--no-build',
                    '--out', str(out)], cwd=ROOT, capture_output=True)
    report = json.loads((out / 'report.json').read_text())
    failures = {f['id']: f for f in report['failures']}
    results, ok = {}, True
    for trace_id, problem in EXPECTED.items():
        f = failures.get(trace_id)
        found = sorted({p['problem'] for p in (f or {}).get('problems', [])})
        passed = f is not None and problem in found
        ok &= passed
        results[trace_id] = dict(rejected=passed, outcome=(f or {}).get('outcome', 'agreement'), problems=found)
    print(json.dumps(results, indent=1))
    return 0 if ok and set(failures) == set(EXPECTED) else 1


if __name__ == '__main__':
    sys.exit(main())
