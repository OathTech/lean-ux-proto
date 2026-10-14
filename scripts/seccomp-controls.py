#!/usr/bin/env python3
"""Negative controls for seccomp (docs/2026-10-12-seccomp-design.md, sections 7
and 9.1): every trace in corpus/seccomp-controls is valid, the kernel runs it,
and the mirror must stop `unsupported` at the named site. A stopped mirror
fails its whole chunk, so each control runs alone (`--trace`), on the oracle
or on a scratch kernel named by LEANUX_KERNEL_IDENTITY.

    scripts/in-bundle python3 scripts/seccomp-controls.py

Written by stream X before the mirror (stream V) landed: the detail strings
are the design's site names and are reconciled against the mirror's stop
messages at the first run, which the claim point records.
"""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# trace id: (outcome, a substring of the failure's detail)
EXPECTED = {
    'sk_new_listener': ('unsupported_path', 'NEW_LISTENER'),   # seccomp_set_mode_filter
    'sk_wait_killable': ('unsupported_path', 'NEW_LISTENER'),  # the same listener arm
    'sk_user_notif': ('unsupported_path', 'USER_NOTIF'),       # __seccomp_filter
}


def run_one(trace_id, no_build=False):
    out = ROOT / f'.artifacts/check/seccomp-controls-{trace_id}'
    subprocess.run(['rm', '-rf', str(out)], check=True)
    subprocess.run([sys.executable, '-m', 'evaluator.check', '--suite', 'seccomp-controls', '--trace', trace_id,
                    '--out', str(out)] + (['--no-build'] if no_build else []), cwd=ROOT, capture_output=True)
    path = out / 'report.json'
    if not path.exists():
        return None
    return json.loads(path.read_text())


def main():
    no_build = '--no-build' in sys.argv[1:]   # reuse the built model (a run beside another check)
    results, ok = {}, True
    for trace_id, (outcome, detail) in EXPECTED.items():
        report = run_one(trace_id, no_build)
        if report is None or report.get('aborted') or report['traces'] != 1:
            results[trace_id] = dict(rejected=False, error='the control run did not run its trace',
                                     aborted=(report or {}).get('aborted'))
            ok = False
            continue
        # a stopped mirror fails its chunk: the failure carries the stopping
        # trace in its detail ("trace <id> operation <i>: ...")
        failures = [f for f in report['failures']
                    if f.get('id') == trace_id or f.get('detail', '').startswith(f'trace {trace_id} ')]
        f = failures[0] if failures else {}
        passed = f.get('outcome') == outcome and detail in f.get('detail', '')
        ok &= passed
        results[trace_id] = dict(rejected=passed, outcome=f.get('outcome', 'agreement'), detail=f.get('detail', '')[:300])
    print(json.dumps(dict(status='pass' if ok else 'fail', controls=results), indent=2))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
